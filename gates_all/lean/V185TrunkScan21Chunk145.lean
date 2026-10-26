import V185TrunkScan21Chunk144

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_1767820 : List Nat := [2, 2, 1, 2, 1, 6, 1, 1, 5]
def baseStart_1767820 : Nat := 118140960795 + 1767820 * 2 ^ 59
def prefixEnd_1767820 : Nat := 4983230072969 + 3 ^ 40 * 1767820 * 2
def baseEnd_1767820 : Nat := 403440609169501613253311

theorem tailTrace_1767820 : CollatzResearch.WordTrace tailWord_1767820 prefixEnd_1767820 403440609169501613253311 := by
  unfold tailWord_1767820
  simp only [CollatzResearch.WordTrace]
  refine ⟨32238846227748767232030457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42985128303665022976040609 32238846227748767232030457)
  ·
    refine ⟨24179134670811575424022843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32238846227748767232030457 24179134670811575424022843)
    ·
      refine ⟨36268702006217363136034265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24179134670811575424022843 36268702006217363136034265)
      ·
        refine ⟨27201526504663022352025699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36268702006217363136034265 27201526504663022352025699)
        ·
          refine ⟨40802289756994533528038549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27201526504663022352025699 40802289756994533528038549)
          ·
            refine ⟨1912607332359118759126807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 40802289756994533528038549 1912607332359118759126807)
            ·
              refine ⟨2868910998538678138690211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1912607332359118759126807 2868910998538678138690211)
              ·
                refine ⟨4303366497808017208035317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2868910998538678138690211 4303366497808017208035317)
                ·
                  refine ⟨403440609169501613253311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4303366497808017208035317 403440609169501613253311)
                  ·
                    rfl

theorem cell21_1767820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 1, 5].length) (baseStart_1767820 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1767820 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1767820 prefixEnd_1767820 := by exact prefixLift 1767820
  have htrace : WordTrace (prefixWord ++ tailWord_1767820) baseStart_1767820 baseEnd_1767820 := by
    simpa [prefixWord, tailWord_1767820, baseEnd_1767820] using wordTrace_append hprefix tailTrace_1767820
  have hstable : (prefixWord ++ tailWord_1767820).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767820).length < 2 ^ (prefixWord ++ tailWord_1767820).sum := by decide
  have hdescent : baseEnd_1767820 < baseStart_1767820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767969 : List Nat := [1, 2, 3, 2, 2, 1, 1, 1, 8]
def baseStart_1767969 : Nat := 118140960795 + 1767969 * 2 ^ 59
def prefixEnd_1767969 : Nat := 4983230072969 + 3 ^ 40 * 1767969 * 2
def baseEnd_1767969 : Nat := 403474612999510465269673

theorem tailTrace_1767969 : CollatzResearch.WordTrace tailWord_1767969 prefixEnd_1767969 403474612999510465269673 := by
  unfold tailWord_1767969
  simp only [CollatzResearch.WordTrace]
  refine ⟨64483126931957732911234961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42988751287971821940823307 64483126931957732911234961)
  ·
    refine ⟨48362345198968299683426221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64483126931957732911234961 48362345198968299683426221)
    ·
      refine ⟨18135879449613112381284833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48362345198968299683426221 18135879449613112381284833)
      ·
        refine ⟨13601909587209834285963625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18135879449613112381284833 13601909587209834285963625)
        ·
          refine ⟨10201432190407375714472719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13601909587209834285963625 10201432190407375714472719)
          ·
            refine ⟨15302148285611063571709079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10201432190407375714472719 15302148285611063571709079)
            ·
              refine ⟨22953222428416595357563619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15302148285611063571709079 22953222428416595357563619)
              ·
                refine ⟨34429833642624893036345429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22953222428416595357563619 34429833642624893036345429)
                ·
                  refine ⟨403474612999510465269673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34429833642624893036345429 403474612999510465269673)
                  ·
                    rfl

theorem cell21_1767969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 8].length) (baseStart_1767969 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1767969 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1767969 prefixEnd_1767969 := by exact prefixLift 1767969
  have htrace : WordTrace (prefixWord ++ tailWord_1767969) baseStart_1767969 baseEnd_1767969 := by
    simpa [prefixWord, tailWord_1767969, baseEnd_1767969] using wordTrace_append hprefix tailTrace_1767969
  have hstable : (prefixWord ++ tailWord_1767969).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767969).length < 2 ^ (prefixWord ++ tailWord_1767969).sum := by decide
  have hdescent : baseEnd_1767969 < baseStart_1767969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767975 : List Nat := [1, 1, 7, 2, 2, 1, 7]
def baseStart_1767975 : Nat := 118140960795 + 1767975 * 2 ^ 59
def prefixEnd_1767975 : Nat := 4983230072969 + 3 ^ 40 * 1767975 * 2
def baseEnd_1767975 : Nat := 44830664697917309796629

theorem tailTrace_1767975 : CollatzResearch.WordTrace tailWord_1767975 prefixEnd_1767975 44830664697917309796629 := by
  unfold tailWord_1767975
  simp only [CollatzResearch.WordTrace]
  refine ⟨64483345769935995935953379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42988897179957330623968919 64483345769935995935953379)
  ·
    refine ⟨96725018654903993903930069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64483345769935995935953379 96725018654903993903930069)
    ·
      refine ⟨2266992624724312357123361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 96725018654903993903930069 2266992624724312357123361)
      ·
        refine ⟨1700244468543234267842521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2266992624724312357123361 1700244468543234267842521)
        ·
          refine ⟨1275183351407425700881891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1700244468543234267842521 1275183351407425700881891)
          ·
            refine ⟨1912775027111138551322837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1275183351407425700881891 1912775027111138551322837)
            ·
              refine ⟨44830664697917309796629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1912775027111138551322837 44830664697917309796629)
              ·
                rfl

theorem cell21_1767975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 7].length) (baseStart_1767975 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1767975 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1767975 prefixEnd_1767975 := by exact prefixLift 1767975
  have htrace : WordTrace (prefixWord ++ tailWord_1767975) baseStart_1767975 baseEnd_1767975 := by
    simpa [prefixWord, tailWord_1767975, baseEnd_1767975] using wordTrace_append hprefix tailTrace_1767975
  have hstable : (prefixWord ++ tailWord_1767975).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767975).length < 2 ^ (prefixWord ++ tailWord_1767975).sum := by decide
  have hdescent : baseEnd_1767975 < baseStart_1767975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767989 : List Nat := [1, 3, 3, 1, 1, 2, 5, 2, 3]
def baseStart_1767989 : Nat := 118140960795 + 1767989 * 2 ^ 59
def prefixEnd_1767989 : Nat := 4983230072969 + 3 ^ 40 * 1767989 * 2
def baseEnd_1767989 : Nat := 403479177271994874936299

theorem tailTrace_1767989 : CollatzResearch.WordTrace tailWord_1767989 prefixEnd_1767989 403479177271994874936299 := by
  unfold tailWord_1767989
  simp only [CollatzResearch.WordTrace]
  refine ⟨64483856391885276326963021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42989237594590184217975347 64483856391885276326963021)
  ·
    refine ⟨24181446146956978622611133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64483856391885276326963021 24181446146956978622611133)
    ·
      refine ⟨9068042305108866983479175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24181446146956978622611133 9068042305108866983479175)
      ·
        refine ⟨13602063457663300475218763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9068042305108866983479175 13602063457663300475218763)
        ·
          refine ⟨20403095186494950712828145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13602063457663300475218763 20403095186494950712828145)
          ·
            refine ⟨15302321389871213034621109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20403095186494950712828145 15302321389871213034621109)
            ·
              refine ⟨1434592630300426221995729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15302321389871213034621109 1434592630300426221995729)
              ·
                refine ⟨1075944472725319666496797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1434592630300426221995729 1075944472725319666496797)
                ·
                  refine ⟨403479177271994874936299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1075944472725319666496797 403479177271994874936299)
                  ·
                    rfl

theorem cell21_1767989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 5, 2, 3].length) (baseStart_1767989 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1767989 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1767989 prefixEnd_1767989 := by exact prefixLift 1767989
  have htrace : WordTrace (prefixWord ++ tailWord_1767989) baseStart_1767989 baseEnd_1767989 := by
    simpa [prefixWord, tailWord_1767989, baseEnd_1767989] using wordTrace_append hprefix tailTrace_1767989
  have hstable : (prefixWord ++ tailWord_1767989).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767989).length < 2 ^ (prefixWord ++ tailWord_1767989).sum := by decide
  have hdescent : baseEnd_1767989 < baseStart_1767989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768034 : List Nat := [3, 3, 2, 3, 2, 8]
def baseStart_1768034 : Nat := 118140960795 + 1768034 * 2 ^ 59
def prefixEnd_1768034 : Nat := 4983230072969 + 3 ^ 40 * 1768034 * 2
def baseEnd_1768034 : Nat := 14944053588336473951341

theorem tailTrace_1768034 : CollatzResearch.WordTrace tailWord_1768034 prefixEnd_1768034 14944053588336473951341 := by
  unfold tailWord_1768034
  simp only [CollatzResearch.WordTrace]
  refine ⟨16121374419180562253087789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42990331784481499341567437 16121374419180562253087789)
  ·
    refine ⟨6045515407192710844907921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16121374419180562253087789 6045515407192710844907921)
    ·
      refine ⟨4534136555394533133680941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6045515407192710844907921 4534136555394533133680941)
      ·
        refine ⟨1700301208272949925130353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4534136555394533133680941 1700301208272949925130353)
        ·
          refine ⟨1275225906204712443847765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1700301208272949925130353 1275225906204712443847765)
          ·
            refine ⟨14944053588336473951341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1275225906204712443847765 14944053588336473951341)
            ·
              rfl

theorem cell21_1768034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 8].length) (baseStart_1768034 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1768034 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1768034 prefixEnd_1768034 := by exact prefixLift 1768034
  have htrace : WordTrace (prefixWord ++ tailWord_1768034) baseStart_1768034 baseEnd_1768034 := by
    simpa [prefixWord, tailWord_1768034, baseEnd_1768034] using wordTrace_append hprefix tailTrace_1768034
  have hstable : (prefixWord ++ tailWord_1768034).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768034).length < 2 ^ (prefixWord ++ tailWord_1768034).sum := by decide
  have hdescent : baseEnd_1768034 < baseStart_1768034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768059 : List Nat := [1, 1, 1, 1, 1, 4, 2, 10]
def baseStart_1768059 : Nat := 118140960795 + 1768059 * 2 ^ 59
def prefixEnd_1768059 : Nat := 4983230072969 + 3 ^ 40 * 1768059 * 2
def baseEnd_1768059 : Nat := 134498384075230102923163

theorem tailTrace_1768059 : CollatzResearch.WordTrace tailWord_1768059 prefixEnd_1768059 134498384075230102923163 := by
  unfold tailWord_1768059
  simp only [CollatzResearch.WordTrace]
  refine ⟨64486409501631678282011231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42990939667754452188007487 64486409501631678282011231)
  ·
    refine ⟨96729614252447517423016847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64486409501631678282011231 96729614252447517423016847)
    ·
      refine ⟨145094421378671276134525271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96729614252447517423016847 145094421378671276134525271)
      ·
        refine ⟨217641632068006914201787907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145094421378671276134525271 217641632068006914201787907)
        ·
          refine ⟨326462448102010371302681861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217641632068006914201787907 326462448102010371302681861)
          ·
            refine ⟨61211709019126944619252849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 326462448102010371302681861 61211709019126944619252849)
            ·
              refine ⟨45908781764345208464439637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61211709019126944619252849 45908781764345208464439637)
              ·
                refine ⟨134498384075230102923163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 45908781764345208464439637 134498384075230102923163)
                ·
                  rfl

theorem cell21_1768059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 10].length) (baseStart_1768059 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1768059 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1768059 prefixEnd_1768059 := by exact prefixLift 1768059
  have htrace : WordTrace (prefixWord ++ tailWord_1768059) baseStart_1768059 baseEnd_1768059 := by
    simpa [prefixWord, tailWord_1768059, baseEnd_1768059] using wordTrace_append hprefix tailTrace_1768059
  have hstable : (prefixWord ++ tailWord_1768059).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768059).length < 2 ^ (prefixWord ++ tailWord_1768059).sum := by decide
  have hdescent : baseEnd_1768059 < baseStart_1768059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768096 : List Nat := [2, 1, 1, 4, 5, 1, 1, 2, 4]
def baseStart_1768096 : Nat := 118140960795 + 1768096 * 2 ^ 59
def prefixEnd_1768096 : Nat := 4983230072969 + 3 ^ 40 * 1768096 * 2
def baseEnd_1768096 : Nat := 403503596129786466652747

theorem tailTrace_1768096 : CollatzResearch.WordTrace tailWord_1768096 prefixEnd_1768096 403503596129786466652747 := by
  unfold tailWord_1768096
  simp only [CollatzResearch.WordTrace]
  refine ⟨32243879501248816800554071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42991839334998422400738761 32243879501248816800554071)
  ·
    refine ⟨48365819251873225200831107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32243879501248816800554071 48365819251873225200831107)
    ·
      refine ⟨72548728877809837801246661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48365819251873225200831107 72548728877809837801246661)
      ·
        refine ⟨13602886664589344587733749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72548728877809837801246661 13602886664589344587733749)
        ·
          refine ⟨1275270624805251055100039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13602886664589344587733749 1275270624805251055100039)
          ·
            refine ⟨1912905937207876582650059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1275270624805251055100039 1912905937207876582650059)
            ·
              refine ⟨2869358905811814873975089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1912905937207876582650059 2869358905811814873975089)
              ·
                refine ⟨2152019179358861155481317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2869358905811814873975089 2152019179358861155481317)
                ·
                  refine ⟨403503596129786466652747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2152019179358861155481317 403503596129786466652747)
                  ·
                    rfl

theorem cell21_1768096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 2, 4].length) (baseStart_1768096 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1768096 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1768096 prefixEnd_1768096 := by exact prefixLift 1768096
  have htrace : WordTrace (prefixWord ++ tailWord_1768096) baseStart_1768096 baseEnd_1768096 := by
    simpa [prefixWord, tailWord_1768096, baseEnd_1768096] using wordTrace_append hprefix tailTrace_1768096
  have hstable : (prefixWord ++ tailWord_1768096).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768096).length < 2 ^ (prefixWord ++ tailWord_1768096).sum := by decide
  have hdescent : baseEnd_1768096 < baseStart_1768096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768152 : List Nat := [2, 1, 2, 2, 3, 4, 7]
def baseStart_1768152 : Nat := 118140960795 + 1768152 * 2 ^ 59
def prefixEnd_1768152 : Nat := 4983230072969 + 3 ^ 40 * 1768152 * 2
def baseEnd_1768152 : Nat := 44835152899193645968811

theorem tailTrace_1768152 : CollatzResearch.WordTrace tailWord_1768152 prefixEnd_1768152 44835152899193645968811 := by
  unfold tailWord_1768152
  simp only [CollatzResearch.WordTrace]
  refine ⟨32244900745147377582573355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42993200993529836776764473 32244900745147377582573355)
  ·
    refine ⟨48367351117721066373860033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32244900745147377582573355 48367351117721066373860033)
    ·
      refine ⟨36275513338290799780395025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48367351117721066373860033 36275513338290799780395025)
      ·
        refine ⟨27206635003718099835296269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36275513338290799780395025 27206635003718099835296269)
        ·
          refine ⟨10202488126394287438236101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27206635003718099835296269 10202488126394287438236101)
          ·
            refine ⟨1912966523698928894669269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10202488126394287438236101 1912966523698928894669269)
            ·
              refine ⟨44835152899193645968811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1912966523698928894669269 44835152899193645968811)
              ·
                rfl

theorem cell21_1768152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 7].length) (baseStart_1768152 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1768152 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1768152 prefixEnd_1768152 := by exact prefixLift 1768152
  have htrace : WordTrace (prefixWord ++ tailWord_1768152) baseStart_1768152 baseEnd_1768152 := by
    simpa [prefixWord, tailWord_1768152, baseEnd_1768152] using wordTrace_append hprefix tailTrace_1768152
  have hstable : (prefixWord ++ tailWord_1768152).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768152).length < 2 ^ (prefixWord ++ tailWord_1768152).sum := by decide
  have hdescent : baseEnd_1768152 < baseStart_1768152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768245 : List Nat := [1, 3, 3, 1, 3, 2, 3, 5]
def baseStart_1768245 : Nat := 118140960795 + 1768245 * 2 ^ 59
def prefixEnd_1768245 : Nat := 4983230072969 + 3 ^ 40 * 1768245 * 2
def baseEnd_1768245 : Nat := 134512533319931772889703

theorem tailTrace_1768245 : CollatzResearch.WordTrace tailWord_1768245 prefixEnd_1768245 134512533319931772889703 := by
  unfold tailWord_1768245
  simp only [CollatzResearch.WordTrace]
  refine ⟨64493193478957832048282189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42995462319305221365521459 64493193478957832048282189)
  ·
    refine ⟨24184947554609187018105821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64493193478957832048282189 24184947554609187018105821)
    ·
      refine ⟨9069355332978445131789683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24184947554609187018105821 9069355332978445131789683)
      ·
        refine ⟨13604032999467667697684525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9069355332978445131789683 13604032999467667697684525)
        ·
          refine ⟨5101512374800375386631697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13604032999467667697684525 5101512374800375386631697)
          ·
            refine ⟨3826134281100281539973773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5101512374800375386631697 3826134281100281539973773)
            ·
              refine ⟨1434800355412605577490165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3826134281100281539973773 1434800355412605577490165)
              ·
                refine ⟨134512533319931772889703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1434800355412605577490165 134512533319931772889703)
                ·
                  rfl

theorem cell21_1768245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 3, 5].length) (baseStart_1768245 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1768245 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1768245 prefixEnd_1768245 := by exact prefixLift 1768245
  have htrace : WordTrace (prefixWord ++ tailWord_1768245) baseStart_1768245 baseEnd_1768245 := by
    simpa [prefixWord, tailWord_1768245, baseEnd_1768245] using wordTrace_append hprefix tailTrace_1768245
  have hstable : (prefixWord ++ tailWord_1768245).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768245).length < 2 ^ (prefixWord ++ tailWord_1768245).sum := by decide
  have hdescent : baseEnd_1768245 < baseStart_1768245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768262 : List Nat := [6, 1, 1, 2, 2, 1, 8]
def baseStart_1768262 : Nat := 118140960795 + 1768262 * 2 ^ 59
def prefixEnd_1768262 : Nat := 4983230072969 + 3 ^ 40 * 1768262 * 2
def baseEnd_1768262 : Nat := 44837942176823007431749

theorem tailTrace_1768262 : CollatzResearch.WordTrace tailWord_1768262 prefixEnd_1768262 44837942176823007431749 := by
  unfold tailWord_1768262
  simp only [CollatzResearch.WordTrace]
  refine ⟨2015431672496757623489095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 42995875679930829301100693 2015431672496757623489095)
  ·
    refine ⟨3023147508745136435233643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2015431672496757623489095 3023147508745136435233643)
    ·
      refine ⟨4534721263117704652850465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3023147508745136435233643 4534721263117704652850465)
      ·
        refine ⟨3401040947338278489637849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4534721263117704652850465 3401040947338278489637849)
        ·
          refine ⟨2550780710503708867228387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3401040947338278489637849 2550780710503708867228387)
          ·
            refine ⟨3826171065755563300842581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2550780710503708867228387 3826171065755563300842581)
            ·
              refine ⟨44837942176823007431749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3826171065755563300842581 44837942176823007431749)
              ·
                rfl

theorem cell21_1768262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 8].length) (baseStart_1768262 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1768262 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1768262 prefixEnd_1768262 := by exact prefixLift 1768262
  have htrace : WordTrace (prefixWord ++ tailWord_1768262) baseStart_1768262 baseEnd_1768262 := by
    simpa [prefixWord, tailWord_1768262, baseEnd_1768262] using wordTrace_append hprefix tailTrace_1768262
  have hstable : (prefixWord ++ tailWord_1768262).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768262).length < 2 ^ (prefixWord ++ tailWord_1768262).sum := by decide
  have hdescent : baseEnd_1768262 < baseStart_1768262 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768276 : List Nat := [2, 4, 1, 1, 4, 1, 2, 1, 5]
def baseStart_1768276 : Nat := 118140960795 + 1768276 * 2 ^ 59
def prefixEnd_1768276 : Nat := 4983230072969 + 3 ^ 40 * 1768276 * 2
def baseEnd_1768276 : Nat := 403544674582146153652379

theorem tailTrace_1768276 : CollatzResearch.WordTrace tailWord_1768276 prefixEnd_1768276 403544674582146153652379 := by
  unfold tailWord_1768276
  simp only [CollatzResearch.WordTrace]
  refine ⟨32247162070922762171330341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42996216094563682895107121 32247162070922762171330341)
  ·
    refine ⟨6046342888298017907124439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32247162070922762171330341 6046342888298017907124439)
    ·
      refine ⟨9069514332447026860686659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6046342888298017907124439 9069514332447026860686659)
      ·
        refine ⟨13604271498670540291029989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9069514332447026860686659 13604271498670540291029989)
        ·
          refine ⟨2550800906000726304568123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13604271498670540291029989 2550800906000726304568123)
          ·
            refine ⟨3826201359001089456852185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2550800906000726304568123 3826201359001089456852185)
            ·
              refine ⟨2869651019250817092639139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3826201359001089456852185 2869651019250817092639139)
              ·
                refine ⟨4304476528876225638958709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2869651019250817092639139 4304476528876225638958709)
                ·
                  refine ⟨403544674582146153652379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4304476528876225638958709 403544674582146153652379)
                  ·
                    rfl

theorem cell21_1768276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_1768276 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1768276 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1768276 prefixEnd_1768276 := by exact prefixLift 1768276
  have htrace : WordTrace (prefixWord ++ tailWord_1768276) baseStart_1768276 baseEnd_1768276 := by
    simpa [prefixWord, tailWord_1768276, baseEnd_1768276] using wordTrace_append hprefix tailTrace_1768276
  have hstable : (prefixWord ++ tailWord_1768276).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768276).length < 2 ^ (prefixWord ++ tailWord_1768276).sum := by decide
  have hdescent : baseEnd_1768276 < baseStart_1768276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768287 : List Nat := [1, 1, 2, 3, 1, 3, 2, 8]
def baseStart_1768287 : Nat := 118140960795 + 1768287 * 2 ^ 59
def prefixEnd_1768287 : Nat := 4983230072969 + 3 ^ 40 * 1768287 * 2
def baseEnd_1768287 : Nat := 134515728310670859656341

theorem tailTrace_1768287 : CollatzResearch.WordTrace tailWord_1768287 prefixEnd_1768287 134515728310670859656341 := by
  unfold tailWord_1768287
  simp only [CollatzResearch.WordTrace]
  refine ⟨64494725344805673221311115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42996483563203782147540743 64494725344805673221311115)
  ·
    refine ⟨96742088017208509831966673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64494725344805673221311115 96742088017208509831966673)
    ·
      refine ⟨72556566012906382373975005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96742088017208509831966673 72556566012906382373975005)
      ·
        refine ⟨27208712254839893390240627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72556566012906382373975005 27208712254839893390240627)
        ·
          refine ⟨40813068382259840085360941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27208712254839893390240627 40813068382259840085360941)
          ·
            refine ⟨15304900643347440032010353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40813068382259840085360941 15304900643347440032010353)
            ·
              refine ⟨11478675482510580024007765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15304900643347440032010353 11478675482510580024007765)
              ·
                refine ⟨134515728310670859656341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11478675482510580024007765 134515728310670859656341)
                ·
                  rfl

theorem cell21_1768287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 8].length) (baseStart_1768287 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1768287 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1768287 prefixEnd_1768287 := by exact prefixLift 1768287
  have htrace : WordTrace (prefixWord ++ tailWord_1768287) baseStart_1768287 baseEnd_1768287 := by
    simpa [prefixWord, tailWord_1768287, baseEnd_1768287] using wordTrace_append hprefix tailTrace_1768287
  have hstable : (prefixWord ++ tailWord_1768287).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768287).length < 2 ^ (prefixWord ++ tailWord_1768287).sum := by decide
  have hdescent : baseEnd_1768287 < baseStart_1768287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768304 : List Nat := [2, 1, 1, 1, 4, 1, 6, 5]
def baseStart_1768304 : Nat := 118140960795 + 1768304 * 2 ^ 59
def prefixEnd_1768304 : Nat := 4983230072969 + 3 ^ 40 * 1768304 * 2
def baseEnd_1768304 : Nat := 134517021521208109061885

theorem tailTrace_1768304 : CollatzResearch.WordTrace tailWord_1768304 prefixEnd_1768304 134517021521208109061885 := by
  unfold tailWord_1768304
  simp only [CollatzResearch.WordTrace]
  refine ⟨32247672692872042562339983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42996896923829390083119977 32247672692872042562339983)
  ·
    refine ⟨48371509039308063843509975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32247672692872042562339983 48371509039308063843509975)
    ·
      refine ⟨72557263558962095765264963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48371509039308063843509975 72557263558962095765264963)
      ·
        refine ⟨108835895338443143647897445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72557263558962095765264963 108835895338443143647897445)
        ·
          refine ⟨20406730375958089433980771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108835895338443143647897445 20406730375958089433980771)
          ·
            refine ⟨30610095563937134150971157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20406730375958089433980771 30610095563937134150971157)
            ·
              refine ⟨1434848229559553163326773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 30610095563937134150971157 1434848229559553163326773)
              ·
                refine ⟨134517021521208109061885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1434848229559553163326773 134517021521208109061885)
                ·
                  rfl

theorem cell21_1768304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 6, 5].length) (baseStart_1768304 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1768304 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1768304 prefixEnd_1768304 := by exact prefixLift 1768304
  have htrace : WordTrace (prefixWord ++ tailWord_1768304) baseStart_1768304 baseEnd_1768304 := by
    simpa [prefixWord, tailWord_1768304, baseEnd_1768304] using wordTrace_append hprefix tailTrace_1768304
  have hstable : (prefixWord ++ tailWord_1768304).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768304).length < 2 ^ (prefixWord ++ tailWord_1768304).sum := by decide
  have hdescent : baseEnd_1768304 < baseStart_1768304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768310 : List Nat := [5, 1, 1, 3, 1, 3, 1, 3, 3]
def baseStart_1768310 : Nat := 118140960795 + 1768310 * 2 ^ 59
def prefixEnd_1768310 : Nat := 4983230072969 + 3 ^ 40 * 1768310 * 2
def baseEnd_1768310 : Nat := 403552433845369650085643

theorem tailTrace_1768310 : CollatzResearch.WordTrace tailWord_1768310 prefixEnd_1768310 403552433845369650085643 := by
  unfold tailWord_1768310
  simp only [CollatzResearch.WordTrace]
  refine ⟨4030972763982646759337399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42997042815814898766265589 4030972763982646759337399)
  ·
    refine ⟨6046459145973970139006099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4030972763982646759337399 6046459145973970139006099)
    ·
      refine ⟨9069688718960955208509149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6046459145973970139006099 9069688718960955208509149)
      ·
        refine ⟨3401133269610358203190931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9069688718960955208509149 3401133269610358203190931)
        ·
          refine ⟨5101699904415537304786397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3401133269610358203190931 5101699904415537304786397)
          ·
            refine ⟨1913137464155826489294899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5101699904415537304786397 1913137464155826489294899)
            ·
              refine ⟨2869706196233739733942349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1913137464155826489294899 2869706196233739733942349)
              ·
                refine ⟨1076139823587652400228381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2869706196233739733942349 1076139823587652400228381)
                ·
                  refine ⟨403552433845369650085643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1076139823587652400228381 403552433845369650085643)
                  ·
                    rfl

theorem cell21_1768310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 3, 3].length) (baseStart_1768310 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1768310 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1768310 prefixEnd_1768310 := by exact prefixLift 1768310
  have htrace : WordTrace (prefixWord ++ tailWord_1768310) baseStart_1768310 baseEnd_1768310 := by
    simpa [prefixWord, tailWord_1768310, baseEnd_1768310] using wordTrace_append hprefix tailTrace_1768310
  have hstable : (prefixWord ++ tailWord_1768310).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768310).length < 2 ^ (prefixWord ++ tailWord_1768310).sum := by decide
  have hdescent : baseEnd_1768310 < baseStart_1768310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768394 : List Nat := [3, 1, 2, 1, 2, 1, 1, 5, 5]
def baseStart_1768394 : Nat := 118140960795 + 1768394 * 2 ^ 59
def prefixEnd_1768394 : Nat := 4983230072969 + 3 ^ 40 * 1768394 * 2
def baseEnd_1768394 : Nat := 403571603789804170685471

theorem tailTrace_1768394 : CollatzResearch.WordTrace tailWord_1768394 prefixEnd_1768394 403571603789804170685471 := by
  unfold tailWord_1768394
  simp only [CollatzResearch.WordTrace]
  refine ⟨16124656988854507623864059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42999085303612020330304157 16124656988854507623864059)
  ·
    refine ⟨24186985483281761435796089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16124656988854507623864059 24186985483281761435796089)
    ·
      refine ⟨18140239112461321076847067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24186985483281761435796089 18140239112461321076847067)
      ·
        refine ⟨27210358668691981615270601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18140239112461321076847067 27210358668691981615270601)
        ·
          refine ⟨20407769001518986211452951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27210358668691981615270601 20407769001518986211452951)
          ·
            refine ⟨30611653502278479317179427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20407769001518986211452951 30611653502278479317179427)
            ·
              refine ⟨45917480253417718975769141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30611653502278479317179427 45917480253417718975769141)
              ·
                refine ⟨4304763773757911153978357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45917480253417718975769141 4304763773757911153978357)
                ·
                  refine ⟨403571603789804170685471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4304763773757911153978357 403571603789804170685471)
                  ·
                    rfl

theorem cell21_1768394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 5, 5].length) (baseStart_1768394 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1768394 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1768394 prefixEnd_1768394 := by exact prefixLift 1768394
  have htrace : WordTrace (prefixWord ++ tailWord_1768394) baseStart_1768394 baseEnd_1768394 := by
    simpa [prefixWord, tailWord_1768394, baseEnd_1768394] using wordTrace_append hprefix tailTrace_1768394
  have hstable : (prefixWord ++ tailWord_1768394).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768394).length < 2 ^ (prefixWord ++ tailWord_1768394).sum := by decide
  have hdescent : baseEnd_1768394 < baseStart_1768394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768501 : List Nat := [1, 3, 3, 1, 1, 1, 1, 6, 4]
def baseStart_1768501 : Nat := 118140960795 + 1768501 * 2 ^ 59
def prefixEnd_1768501 : Nat := 4983230072969 + 3 ^ 40 * 1768501 * 2
def baseEnd_1768501 : Nat := 403596022647595762401919

theorem tailTrace_1768501 : CollatzResearch.WordTrace tailWord_1768501 prefixEnd_1768501 403596022647595762401919 := by
  unfold tailWord_1768501
  simp only [CollatzResearch.WordTrace]
  refine ⟨64502530566030387769601357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43001687044020258513067571 64502530566030387769601357)
  ·
    refine ⟨24188448962261395413600509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64502530566030387769601357 24188448962261395413600509)
    ·
      refine ⟨9070668360848023280100191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24188448962261395413600509 9070668360848023280100191)
      ·
        refine ⟨13606002541272034920150287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9070668360848023280100191 13606002541272034920150287)
        ·
          refine ⟨20409003811908052380225431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13606002541272034920150287 20409003811908052380225431)
          ·
            refine ⟨30613505717862078570338147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20409003811908052380225431 30613505717862078570338147)
            ·
              refine ⟨45920258576793117855507221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30613505717862078570338147 45920258576793117855507221)
              ·
                refine ⟨2152512120787177399476901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 45920258576793117855507221 2152512120787177399476901)
                ·
                  refine ⟨403596022647595762401919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2152512120787177399476901 403596022647595762401919)
                  ·
                    rfl

theorem cell21_1768501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 6, 4].length) (baseStart_1768501 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1768501 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1768501 prefixEnd_1768501 := by exact prefixLift 1768501
  have htrace : WordTrace (prefixWord ++ tailWord_1768501) baseStart_1768501 baseEnd_1768501 := by
    simpa [prefixWord, tailWord_1768501, baseEnd_1768501] using wordTrace_append hprefix tailTrace_1768501
  have hstable : (prefixWord ++ tailWord_1768501).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768501).length < 2 ^ (prefixWord ++ tailWord_1768501).sum := by decide
  have hdescent : baseEnd_1768501 < baseStart_1768501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768515 : List Nat := [1, 1, 1, 3, 1, 2, 6, 6]
def baseStart_1768515 : Nat := 118140960795 + 1768515 * 2 ^ 59
def prefixEnd_1768515 : Nat := 4983230072969 + 3 ^ 40 * 1768515 * 2
def baseEnd_1768515 : Nat := 134533072546111616389519

theorem tailTrace_1768515 : CollatzResearch.WordTrace tailWord_1768515 prefixEnd_1768515 134533072546111616389519 := by
  unfold tailWord_1768515
  simp only [CollatzResearch.WordTrace]
  refine ⟨64503041187979668160610999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43002027458653112107073999 64503041187979668160610999)
  ·
    refine ⟨96754561781969502240916499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64503041187979668160610999 96754561781969502240916499)
    ·
      refine ⟨145131842672954253361374749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96754561781969502240916499 145131842672954253361374749)
      ·
        refine ⟨54424441002357845010515531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145131842672954253361374749 54424441002357845010515531)
        ·
          refine ⟨81636661503536767515773297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54424441002357845010515531 81636661503536767515773297)
          ·
            refine ⟨61227496127652575636829973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81636661503536767515773297 61227496127652575636829973)
            ·
              refine ⟨2870038880983714482976405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 61227496127652575636829973 2870038880983714482976405)
              ·
                refine ⟨134533072546111616389519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2870038880983714482976405 134533072546111616389519)
                ·
                  rfl

theorem cell21_1768515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 6].length) (baseStart_1768515 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1768515 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1768515 prefixEnd_1768515 := by exact prefixLift 1768515
  have htrace : WordTrace (prefixWord ++ tailWord_1768515) baseStart_1768515 baseEnd_1768515 := by
    simpa [prefixWord, tailWord_1768515, baseEnd_1768515] using wordTrace_append hprefix tailTrace_1768515
  have hstable : (prefixWord ++ tailWord_1768515).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768515).length < 2 ^ (prefixWord ++ tailWord_1768515).sum := by decide
  have hdescent : baseEnd_1768515 < baseStart_1768515 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768642 : List Nat := [3, 5, 1, 1, 2, 1, 1, 7]
def baseStart_1768642 : Nat := 118140960795 + 1768642 * 2 ^ 59
def prefixEnd_1768642 : Nat := 4983230072969 + 3 ^ 40 * 1768642 * 2
def baseEnd_1768642 : Nat := 134542733589536950183877

theorem tailTrace_1768642 : CollatzResearch.WordTrace tailWord_1768642 prefixEnd_1768642 134542733589536950183877 := by
  unfold tailWord_1768642
  simp only [CollatzResearch.WordTrace]
  refine ⟨16126918314629892212621045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43005115505679712566989453 16126918314629892212621045)
  ·
    refine ⟨1511898591996552394933223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16126918314629892212621045 1511898591996552394933223)
    ·
      refine ⟨2267847887994828592399835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1511898591996552394933223 2267847887994828592399835)
      ·
        refine ⟨3401771831992242888599753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2267847887994828592399835 3401771831992242888599753)
        ·
          refine ⟨2551328873994182166449815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3401771831992242888599753 2551328873994182166449815)
          ·
            refine ⟨3826993310991273249674723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2551328873994182166449815 3826993310991273249674723)
            ·
              refine ⟨5740489966486909874512085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3826993310991273249674723 5740489966486909874512085)
              ·
                refine ⟨134542733589536950183877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5740489966486909874512085 134542733589536950183877)
                ·
                  rfl

theorem cell21_1768642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 7].length) (baseStart_1768642 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1768642 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1768642 prefixEnd_1768642 := by exact prefixLift 1768642
  have htrace : WordTrace (prefixWord ++ tailWord_1768642) baseStart_1768642 baseEnd_1768642 := by
    simpa [prefixWord, tailWord_1768642, baseEnd_1768642] using wordTrace_append hprefix tailTrace_1768642
  have hstable : (prefixWord ++ tailWord_1768642).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768642).length < 2 ^ (prefixWord ++ tailWord_1768642).sum := by decide
  have hdescent : baseEnd_1768642 < baseStart_1768642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768687 : List Nat := [1, 1, 2, 1, 7, 2, 2, 1, 4]
def baseStart_1768687 : Nat := 118140960795 + 1768687 * 2 ^ 59
def prefixEnd_1768687 : Nat := 4983230072969 + 3 ^ 40 * 1768687 * 2
def baseEnd_1768687 : Nat := 403638470381700772301539

theorem tailTrace_1768687 : CollatzResearch.WordTrace tailWord_1768687 prefixEnd_1768687 403638470381700772301539 := by
  unfold tailWord_1768687
  simp only [CollatzResearch.WordTrace]
  refine ⟨64509314543356541535872315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43006209695571027690581543 64509314543356541535872315)
  ·
    refine ⟨96763971815034812303808473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64509314543356541535872315 96763971815034812303808473)
    ·
      refine ⟨72572978861276109227856355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96763971815034812303808473 72572978861276109227856355)
      ·
        refine ⟨108859468291914163841784533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72572978861276109227856355 108859468291914163841784533)
        ·
          refine ⟨2551393788091738215041825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 108859468291914163841784533 2551393788091738215041825)
          ·
            refine ⟨1913545341068803661281369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2551393788091738215041825 1913545341068803661281369)
            ·
              refine ⟨1435159005801602745961027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1913545341068803661281369 1435159005801602745961027)
              ·
                refine ⟨2152738508702404118941541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1435159005801602745961027 2152738508702404118941541)
                ·
                  refine ⟨403638470381700772301539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2152738508702404118941541 403638470381700772301539)
                  ·
                    rfl

theorem cell21_1768687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 2, 1, 4].length) (baseStart_1768687 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1768687 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1768687 prefixEnd_1768687 := by exact prefixLift 1768687
  have htrace : WordTrace (prefixWord ++ tailWord_1768687) baseStart_1768687 baseEnd_1768687 := by
    simpa [prefixWord, tailWord_1768687, baseEnd_1768687] using wordTrace_append hprefix tailTrace_1768687
  have hstable : (prefixWord ++ tailWord_1768687).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768687).length < 2 ^ (prefixWord ++ tailWord_1768687).sum := by decide
  have hdescent : baseEnd_1768687 < baseStart_1768687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768732 : List Nat := [2, 2, 3, 1, 1, 1, 6, 2, 3]
def baseStart_1768732 : Nat := 118140960795 + 1768732 * 2 ^ 59
def prefixEnd_1768732 : Nat := 4983230072969 + 3 ^ 40 * 1768732 * 2
def baseEnd_1768732 : Nat := 403648739994790694051447

theorem tailTrace_1768732 : CollatzResearch.WordTrace tailWord_1768732 prefixEnd_1768732 403648739994790694051447 := by
  unfold tailWord_1768732
  simp only [CollatzResearch.WordTrace]
  refine ⟨32255477914096757110630225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43007303885462342814173633 32255477914096757110630225)
  ·
    refine ⟨24191608435572567832972669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32255477914096757110630225 24191608435572567832972669)
    ·
      refine ⟨9071853163339712937364751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24191608435572567832972669 9071853163339712937364751)
      ·
        refine ⟨13607779745009569406047127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9071853163339712937364751 13607779745009569406047127)
        ·
          refine ⟨20411669617514354109070691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13607779745009569406047127 20411669617514354109070691)
          ·
            refine ⟨30617504426271531163606037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20411669617514354109070691 30617504426271531163606037)
            ·
              refine ⟨1435195519981478023294033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 30617504426271531163606037 1435195519981478023294033)
              ·
                refine ⟨1076396639986108517470525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1435195519981478023294033 1076396639986108517470525)
                ·
                  refine ⟨403648739994790694051447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1076396639986108517470525 403648739994790694051447)
                  ·
                    rfl

theorem cell21_1768732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 6, 2, 3].length) (baseStart_1768732 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1768732 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1768732 prefixEnd_1768732 := by exact prefixLift 1768732
  have htrace : WordTrace (prefixWord ++ tailWord_1768732) baseStart_1768732 baseEnd_1768732 := by
    simpa [prefixWord, tailWord_1768732, baseEnd_1768732] using wordTrace_append hprefix tailTrace_1768732
  have hstable : (prefixWord ++ tailWord_1768732).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768732).length < 2 ^ (prefixWord ++ tailWord_1768732).sum := by decide
  have hdescent : baseEnd_1768732 < baseStart_1768732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768746 : List Nat := [3, 1, 4, 2, 1, 1, 2, 3, 4]
def baseStart_1768746 : Nat := 118140960795 + 1768746 * 2 ^ 59
def prefixEnd_1768746 : Nat := 4983230072969 + 3 ^ 40 * 1768746 * 2
def baseEnd_1768746 : Nat := 403651934985529780818085

theorem tailTrace_1768746 : CollatzResearch.WordTrace tailWord_1768746 prefixEnd_1768746 403651934985529780818085 := by
  unfold tailWord_1768746
  simp only [CollatzResearch.WordTrace]
  refine ⟨16127866612535698653067523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43007644300095196408180061 16127866612535698653067523)
  ·
    refine ⟨24191799918803547979601285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16127866612535698653067523 24191799918803547979601285)
    ·
      refine ⟨4535962484775665246175241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24191799918803547979601285 4535962484775665246175241)
      ·
        refine ⟨3401971863581748934631431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4535962484775665246175241 3401971863581748934631431)
        ·
          refine ⟨5102957795372623401947147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3401971863581748934631431 5102957795372623401947147)
          ·
            refine ⟨7654436693058935102920721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5102957795372623401947147 7654436693058935102920721)
            ·
              refine ⟨5740827519794201327190541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7654436693058935102920721 5740827519794201327190541)
              ·
                refine ⟨2152810319922825497696453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5740827519794201327190541 2152810319922825497696453)
                ·
                  refine ⟨403651934985529780818085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2152810319922825497696453 403651934985529780818085)
                  ·
                    rfl

theorem cell21_1768746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 3, 4].length) (baseStart_1768746 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1768746 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1768746 prefixEnd_1768746 := by exact prefixLift 1768746
  have htrace : WordTrace (prefixWord ++ tailWord_1768746) baseStart_1768746 baseEnd_1768746 := by
    simpa [prefixWord, tailWord_1768746, baseEnd_1768746] using wordTrace_append hprefix tailTrace_1768746
  have hstable : (prefixWord ++ tailWord_1768746).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768746).length < 2 ^ (prefixWord ++ tailWord_1768746).sum := by decide
  have hdescent : baseEnd_1768746 < baseStart_1768746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768791 : List Nat := [1, 1, 3, 2, 3, 2, 2, 4, 3]
def baseStart_1768791 : Nat := 118140960795 + 1768791 * 2 ^ 59
def prefixEnd_1768791 : Nat := 4983230072969 + 3 ^ 40 * 1768791 * 2
def baseEnd_1768791 : Nat := 403662204598619702567993

theorem tailTrace_1768791 : CollatzResearch.WordTrace tailWord_1768791 prefixEnd_1768791 403662204598619702567993 := by
  unfold tailWord_1768791
  simp only [CollatzResearch.WordTrace]
  refine ⟨64513107734979767297658227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43008738489986511531772151 64513107734979767297658227)
  ·
    refine ⟨96769661602469650946487341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64513107734979767297658227 96769661602469650946487341)
    ·
      refine ⟨36288623100926119104932753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96769661602469650946487341 36288623100926119104932753)
      ·
        refine ⟨27216467325694589328699565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36288623100926119104932753 27216467325694589328699565)
        ·
          refine ⟨10206175247135470998262337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27216467325694589328699565 10206175247135470998262337)
          ·
            refine ⟨7654631435351603248696753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10206175247135470998262337 7654631435351603248696753)
            ·
              refine ⟨5740973576513702436522565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7654631435351603248696753 5740973576513702436522565)
              ·
                refine ⟨1076432545596319206847981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5740973576513702436522565 1076432545596319206847981)
                ·
                  refine ⟨403662204598619702567993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1076432545596319206847981 403662204598619702567993)
                  ·
                    rfl

theorem cell21_1768791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 4, 3].length) (baseStart_1768791 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1768791 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1768791 prefixEnd_1768791 := by exact prefixLift 1768791
  have htrace : WordTrace (prefixWord ++ tailWord_1768791) baseStart_1768791 baseEnd_1768791 := by
    simpa [prefixWord, tailWord_1768791, baseEnd_1768791] using wordTrace_append hprefix tailTrace_1768791
  have hstable : (prefixWord ++ tailWord_1768791).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768791).length < 2 ^ (prefixWord ++ tailWord_1768791).sum := by decide
  have hdescent : baseEnd_1768791 < baseStart_1768791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768797 : List Nat := [1, 4, 5, 1, 1, 1, 3, 1, 4]
def baseStart_1768797 : Nat := 118140960795 + 1768797 * 2 ^ 59
def prefixEnd_1768797 : Nat := 4983230072969 + 3 ^ 40 * 1768797 * 2
def baseEnd_1768797 : Nat := 403663573880365025467981

theorem tailTrace_1768797 : CollatzResearch.WordTrace tailWord_1768797 prefixEnd_1768797 403663573880365025467981 := by
  unfold tailWord_1768797
  simp only [CollatzResearch.WordTrace]
  refine ⟨64513326572958030322376645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43008884381972020214917763 64513326572958030322376645)
  ·
    refine ⟨12096248732429630685445621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64513326572958030322376645 12096248732429630685445621)
    ·
      refine ⟨1134023318665277876760527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12096248732429630685445621 1134023318665277876760527)
      ·
        refine ⟨1701034977997916815140791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1134023318665277876760527 1701034977997916815140791)
        ·
          refine ⟨2551552466996875222711187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1701034977997916815140791 2551552466996875222711187)
          ·
            refine ⟨3827328700495312834066781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2551552466996875222711187 3827328700495312834066781)
            ·
              refine ⟨1435248262685742312775043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3827328700495312834066781 1435248262685742312775043)
              ·
                refine ⟨2152872394028613469162565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1435248262685742312775043 2152872394028613469162565)
                ·
                  refine ⟨403663573880365025467981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2152872394028613469162565 403663573880365025467981)
                  ·
                    rfl

theorem cell21_1768797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 3, 1, 4].length) (baseStart_1768797 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1768797 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1768797 prefixEnd_1768797 := by exact prefixLift 1768797
  have htrace : WordTrace (prefixWord ++ tailWord_1768797) baseStart_1768797 baseEnd_1768797 := by
    simpa [prefixWord, tailWord_1768797, baseEnd_1768797] using wordTrace_append hprefix tailTrace_1768797
  have hstable : (prefixWord ++ tailWord_1768797).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768797).length < 2 ^ (prefixWord ++ tailWord_1768797).sum := by decide
  have hdescent : baseEnd_1768797 < baseStart_1768797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768856 : List Nat := [2, 1, 2, 5, 3, 1, 2, 1, 4]
def baseStart_1768856 : Nat := 118140960795 + 1768856 * 2 ^ 59
def prefixEnd_1768856 : Nat := 4983230072969 + 3 ^ 40 * 1768856 * 2
def baseEnd_1768856 : Nat := 403677038484194033984527

theorem tailTrace_1768856 : CollatzResearch.WordTrace tailWord_1768856 prefixEnd_1768856 403677038484194033984527 := by
  unfold tailWord_1768856
  simp only [CollatzResearch.WordTrace]
  refine ⟨32257739239872141699387211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43010318986496188932516281 32257739239872141699387211)
  ·
    refine ⟨48386608859808212549080817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32257739239872141699387211 48386608859808212549080817)
    ·
      refine ⟨36289956644856159411810613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48386608859808212549080817 36289956644856159411810613)
      ·
        refine ⟨3402183435455264944857245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36289956644856159411810613 3402183435455264944857245)
        ·
          refine ⟨1275818788295724354321467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3402183435455264944857245 1275818788295724354321467)
          ·
            refine ⟨1913728182443586531482201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1275818788295724354321467 1913728182443586531482201)
            ·
              refine ⟨1435296136832689898611651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1913728182443586531482201 1435296136832689898611651)
              ·
                refine ⟨2152944205249034847917477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1435296136832689898611651 2152944205249034847917477)
                ·
                  refine ⟨403677038484194033984527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2152944205249034847917477 403677038484194033984527)
                  ·
                    rfl

theorem cell21_1768856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 2, 1, 4].length) (baseStart_1768856 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1768856 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1768856 prefixEnd_1768856 := by exact prefixLift 1768856
  have htrace : WordTrace (prefixWord ++ tailWord_1768856) baseStart_1768856 baseEnd_1768856 := by
    simpa [prefixWord, tailWord_1768856, baseEnd_1768856] using wordTrace_append hprefix tailTrace_1768856
  have hstable : (prefixWord ++ tailWord_1768856).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768856).length < 2 ^ (prefixWord ++ tailWord_1768856).sum := by decide
  have hdescent : baseEnd_1768856 < baseStart_1768856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768954 : List Nat := [3, 1, 1, 1, 1, 2, 12]
def baseStart_1768954 : Nat := 118140960795 + 1768954 * 2 ^ 59
def prefixEnd_1768954 : Nat := 4983230072969 + 3 ^ 40 * 1768954 * 2
def baseEnd_1768954 : Nat := 44855489268818626816777

theorem tailTrace_1768954 : CollatzResearch.WordTrace tailWord_1768954 prefixEnd_1768954 44855489268818626816777 := by
  unfold tailWord_1768954
  simp only [CollatzResearch.WordTrace]
  refine ⟨16129763208347311533960479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43012701888926164090561277 16129763208347311533960479)
  ·
    refine ⟨24194644812520967300940719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16129763208347311533960479 24194644812520967300940719)
    ·
      refine ⟨36291967218781450951411079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24194644812520967300940719 36291967218781450951411079)
      ·
        refine ⟨54437950828172176427116619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36291967218781450951411079 54437950828172176427116619)
        ·
          refine ⟨81656926242258264640674929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54437950828172176427116619 81656926242258264640674929)
          ·
            refine ⟨61242694681693698480506197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81656926242258264640674929 61242694681693698480506197)
            ·
              refine ⟨44855489268818626816777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 61242694681693698480506197 44855489268818626816777)
              ·
                rfl

theorem cell21_1768954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 12].length) (baseStart_1768954 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1768954 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1768954 prefixEnd_1768954 := by exact prefixLift 1768954
  have htrace : WordTrace (prefixWord ++ tailWord_1768954) baseStart_1768954 baseEnd_1768954 := by
    simpa [prefixWord, tailWord_1768954, baseEnd_1768954] using wordTrace_append hprefix tailTrace_1768954
  have hstable : (prefixWord ++ tailWord_1768954).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768954).length < 2 ^ (prefixWord ++ tailWord_1768954).sum := by decide
  have hdescent : baseEnd_1768954 < baseStart_1768954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768957 : List Nat := [1, 4, 1, 1, 1, 4, 3, 2, 4]
def baseStart_1768957 : Nat := 118140960795 + 1768957 * 2 ^ 59
def prefixEnd_1768957 : Nat := 4983230072969 + 3 ^ 40 * 1768957 * 2
def baseEnd_1768957 : Nat := 403700088060240302800987

theorem tailTrace_1768957 : CollatzResearch.WordTrace tailWord_1768957 prefixEnd_1768957 403700088060240302800987 := by
  unfold tailWord_1768957
  simp only [CollatzResearch.WordTrace]
  refine ⟨64519162252378377648201125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43012774834918918432134083 64519162252378377648201125)
  ·
    refine ⟨12097342922320945809037711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64519162252378377648201125 12097342922320945809037711)
    ·
      refine ⟨18146014383481418713556567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12097342922320945809037711 18146014383481418713556567)
      ·
        refine ⟨27219021575222128070334851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18146014383481418713556567 27219021575222128070334851)
        ·
          refine ⟨40828532362833192105502277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27219021575222128070334851 40828532362833192105502277)
          ·
            refine ⟨7655349818031223519781677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40828532362833192105502277 7655349818031223519781677)
            ·
              refine ⟨2870756181761708819918129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7655349818031223519781677 2870756181761708819918129)
              ·
                refine ⟨2153067136321281614938597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2870756181761708819918129 2153067136321281614938597)
                ·
                  refine ⟨403700088060240302800987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2153067136321281614938597 403700088060240302800987)
                  ·
                    rfl

theorem cell21_1768957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 2, 4].length) (baseStart_1768957 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1768957 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1768957 prefixEnd_1768957 := by exact prefixLift 1768957
  have htrace : WordTrace (prefixWord ++ tailWord_1768957) baseStart_1768957 baseEnd_1768957 := by
    simpa [prefixWord, tailWord_1768957, baseEnd_1768957] using wordTrace_append hprefix tailTrace_1768957
  have hstable : (prefixWord ++ tailWord_1768957).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768957).length < 2 ^ (prefixWord ++ tailWord_1768957).sum := by decide
  have hdescent : baseEnd_1768957 < baseStart_1768957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1769016 : List Nat := [2, 1, 2, 1, 4, 2, 2, 1, 6]
def baseStart_1769016 : Nat := 118140960795 + 1769016 * 2 ^ 59
def prefixEnd_1769016 : Nat := 4983230072969 + 3 ^ 40 * 1769016 * 2
def baseEnd_1769016 : Nat := 403713552664069311317533

theorem tailTrace_1769016 : CollatzResearch.WordTrace tailWord_1769016 prefixEnd_1769016 403713552664069311317533 := by
  unfold tailWord_1769016
  simp only [CollatzResearch.WordTrace]
  refine ⟨32260657079582315362299451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43014209439443087149732601 32260657079582315362299451)
  ·
    refine ⟨48390985619373473043449177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32260657079582315362299451 48390985619373473043449177)
    ·
      refine ⟨36293239214530104782586883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48390985619373473043449177 36293239214530104782586883)
      ·
        refine ⟨54439858821795157173880325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36293239214530104782586883 54439858821795157173880325)
        ·
          refine ⟨10207473529086591970102561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54439858821795157173880325 10207473529086591970102561)
          ·
            refine ⟨7655605146814943977576921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10207473529086591970102561 7655605146814943977576921)
            ·
              refine ⟨5741703860111207983182691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7655605146814943977576921 5741703860111207983182691)
              ·
                refine ⟨8612555790166811974774037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5741703860111207983182691 8612555790166811974774037)
                ·
                  refine ⟨403713552664069311317533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8612555790166811974774037 403713552664069311317533)
                  ·
                    rfl

theorem cell21_1769016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 6].length) (baseStart_1769016 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1769016 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1769016 prefixEnd_1769016 := by exact prefixLift 1769016
  have htrace : WordTrace (prefixWord ++ tailWord_1769016) baseStart_1769016 baseEnd_1769016 := by
    simpa [prefixWord, tailWord_1769016, baseEnd_1769016] using wordTrace_append hprefix tailTrace_1769016
  have hstable : (prefixWord ++ tailWord_1769016).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1769016).length < 2 ^ (prefixWord ++ tailWord_1769016).sum := by decide
  have hdescent : baseEnd_1769016 < baseStart_1769016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1769016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1769070 : List Nat := [4, 1, 2, 2, 4, 1, 2, 2, 3]
def baseStart_1769070 : Nat := 118140960795 + 1769070 * 2 ^ 59
def prefixEnd_1769070 : Nat := 4983230072969 + 3 ^ 40 * 1769070 * 2
def baseEnd_1769070 : Nat := 403725876199777217417423

theorem tailTrace_1769070 : CollatzResearch.WordTrace tailWord_1769070 prefixEnd_1769070 403725876199777217417423 := by
  unfold tailWord_1769070
  simp only [CollatzResearch.WordTrace]
  refine ⟨8065410462621124743383083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43015522467312665298043109 8065410462621124743383083)
  ·
    refine ⟨12098115693931687115074625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8065410462621124743383083 12098115693931687115074625)
    ·
      refine ⟨9073586770448765336305969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12098115693931687115074625 9073586770448765336305969)
      ·
        refine ⟨6805190077836574002229477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9073586770448765336305969 6805190077836574002229477)
        ·
          refine ⟨1275973139594357625418027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6805190077836574002229477 1275973139594357625418027)
          ·
            refine ⟨1913959709391536438127041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1275973139594357625418027 1913959709391536438127041)
            ·
              refine ⟨1435469782043652328595281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1913959709391536438127041 1435469782043652328595281)
              ·
                refine ⟨1076602336532739246446461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1435469782043652328595281 1076602336532739246446461)
                ·
                  refine ⟨403725876199777217417423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1076602336532739246446461 403725876199777217417423)
                  ·
                    rfl

theorem cell21_1769070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 2, 2, 3].length) (baseStart_1769070 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1769070 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1769070 prefixEnd_1769070 := by exact prefixLift 1769070
  have htrace : WordTrace (prefixWord ++ tailWord_1769070) baseStart_1769070 baseEnd_1769070 := by
    simpa [prefixWord, tailWord_1769070, baseEnd_1769070] using wordTrace_append hprefix tailTrace_1769070
  have hstable : (prefixWord ++ tailWord_1769070).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1769070).length < 2 ^ (prefixWord ++ tailWord_1769070).sum := by decide
  have hdescent : baseEnd_1769070 < baseStart_1769070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1769070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1769075 : List Nat := [1, 1, 1, 2, 2, 1, 1, 2, 10]
def baseStart_1769075 : Nat := 118140960795 + 1769075 * 2 ^ 59
def prefixEnd_1769075 : Nat := 4983230072969 + 3 ^ 40 * 1769075 * 2
def baseEnd_1769075 : Nat := 403727017267898319834079

theorem tailTrace_1769075 : CollatzResearch.WordTrace tailWord_1769075 prefixEnd_1769075 403727017267898319834079 := by
  unfold tailWord_1769075
  simp only [CollatzResearch.WordTrace]
  refine ⟨64523466065950883800996679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43015644043967255867331119 64523466065950883800996679)
  ·
    refine ⟨96785199098926325701495019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64523466065950883800996679 96785199098926325701495019)
    ·
      refine ⟨145177798648389488552242529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96785199098926325701495019 145177798648389488552242529)
      ·
        refine ⟨108883348986292116414181897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145177798648389488552242529 108883348986292116414181897)
        ·
          refine ⟨81662511739719087310636423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108883348986292116414181897 81662511739719087310636423)
          ·
            refine ⟨122493767609578630965954635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81662511739719087310636423 122493767609578630965954635)
            ·
              refine ⟨183740651414367946448931953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122493767609578630965954635 183740651414367946448931953)
              ·
                refine ⟨137805488560775959836698965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 183740651414367946448931953 137805488560775959836698965)
                ·
                  refine ⟨403727017267898319834079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 137805488560775959836698965 403727017267898319834079)
                  ·
                    rfl

theorem cell21_1769075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 10].length) (baseStart_1769075 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1769075 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1769075 prefixEnd_1769075 := by exact prefixLift 1769075
  have htrace : WordTrace (prefixWord ++ tailWord_1769075) baseStart_1769075 baseEnd_1769075 := by
    simpa [prefixWord, tailWord_1769075, baseEnd_1769075] using wordTrace_append hprefix tailTrace_1769075
  have hstable : (prefixWord ++ tailWord_1769075).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1769075).length < 2 ^ (prefixWord ++ tailWord_1769075).sum := by decide
  have hdescent : baseEnd_1769075 < baseStart_1769075 := by decide
  rcases family_descends (prefixWord ++ tailWord_1769075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1769174 : List Nat := [5, 2, 1, 3, 2, 1, 7]
def baseStart_1769174 : Nat := 118140960795 + 1769174 * 2 ^ 59
def prefixEnd_1769174 : Nat := 4983230072969 + 3 ^ 40 * 1769174 * 2
def baseEnd_1769174 : Nat := 44861067824077349742653

theorem tailTrace_1769174 : CollatzResearch.WordTrace tailWord_1769174 prefixEnd_1769174 44861067824077349742653 := by
  unfold tailWord_1769174
  simp only [CollatzResearch.WordTrace]
  refine ⟨4032942305787013981803161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43018051261728149139233717 4032942305787013981803161)
  ·
    refine ⟨3024706729340260486352371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4032942305787013981803161 3024706729340260486352371)
    ·
      refine ⟨4537060094010390729528557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3024706729340260486352371 4537060094010390729528557)
      ·
        refine ⟨1701397535253896523573209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4537060094010390729528557 1701397535253896523573209)
        ·
          refine ⟨1276048151440422392679907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1701397535253896523573209 1276048151440422392679907)
          ·
            refine ⟨1914072227160633589019861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1276048151440422392679907 1914072227160633589019861)
            ·
              refine ⟨44861067824077349742653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1914072227160633589019861 44861067824077349742653)
              ·
                rfl

theorem cell21_1769174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 7].length) (baseStart_1769174 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1769174 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1769174 prefixEnd_1769174 := by exact prefixLift 1769174
  have htrace : WordTrace (prefixWord ++ tailWord_1769174) baseStart_1769174 baseEnd_1769174 := by
    simpa [prefixWord, tailWord_1769174, baseEnd_1769174] using wordTrace_append hprefix tailTrace_1769174
  have hstable : (prefixWord ++ tailWord_1769174).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1769174).length < 2 ^ (prefixWord ++ tailWord_1769174).sum := by decide
  have hdescent : baseEnd_1769174 < baseStart_1769174 := by decide
  rcases family_descends (prefixWord ++ tailWord_1769174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1769227 : List Nat := [1, 1, 1, 1, 5, 1, 2, 1, 8]
def baseStart_1769227 : Nat := 118140960795 + 1769227 * 2 ^ 59
def prefixEnd_1769227 : Nat := 4983230072969 + 3 ^ 40 * 1769227 * 2
def baseEnd_1769227 : Nat := 403761705738779833300435

theorem tailTrace_1769227 : CollatzResearch.WordTrace tailWord_1769227 prefixEnd_1769227 403761705738779833300435 := by
  unfold tailWord_1769227
  simp only [CollatzResearch.WordTrace]
  refine ⟨64529009961400213760529935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43019339974266809173686623 64529009961400213760529935)
  ·
    refine ⟨96793514942100320640794903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64529009961400213760529935 96793514942100320640794903)
    ·
      refine ⟨145190272413150480961192355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96793514942100320640794903 145190272413150480961192355)
      ·
        refine ⟨217785408619725721441788533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145190272413150480961192355 217785408619725721441788533)
        ·
          refine ⟨20417382058099286385167675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 217785408619725721441788533 20417382058099286385167675)
          ·
            refine ⟨30626073087148929577751513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20417382058099286385167675 30626073087148929577751513)
            ·
              refine ⟨22969554815361697183313635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30626073087148929577751513 22969554815361697183313635)
              ·
                refine ⟨34454332223042545774970453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22969554815361697183313635 34454332223042545774970453)
                ·
                  refine ⟨403761705738779833300435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34454332223042545774970453 403761705738779833300435)
                  ·
                    rfl

theorem cell21_1769227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 8].length) (baseStart_1769227 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1769227 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1769227 prefixEnd_1769227 := by exact prefixLift 1769227
  have htrace : WordTrace (prefixWord ++ tailWord_1769227) baseStart_1769227 baseEnd_1769227 := by
    simpa [prefixWord, tailWord_1769227, baseEnd_1769227] using wordTrace_append hprefix tailTrace_1769227
  have hstable : (prefixWord ++ tailWord_1769227).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1769227).length < 2 ^ (prefixWord ++ tailWord_1769227).sum := by decide
  have hdescent : baseEnd_1769227 < baseStart_1769227 := by decide
  rcases family_descends (prefixWord ++ tailWord_1769227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1769236 : List Nat := [2, 4, 4, 1, 1, 1, 2, 2, 4]
def baseStart_1769236 : Nat := 118140960795 + 1769236 * 2 ^ 59
def prefixEnd_1769236 : Nat := 4983230072969 + 3 ^ 40 * 1769236 * 2
def baseEnd_1769236 : Nat := 403763759661397817650417

theorem tailTrace_1769236 : CollatzResearch.WordTrace tailWord_1769236 prefixEnd_1769236 403763759661397817650417 := by
  unfold tailWord_1769236
  simp only [CollatzResearch.WordTrace]
  refine ⟨32264669109183804148803781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43019558812245072198405041 32264669109183804148803781)
  ·
    refine ⟨6049625457971963277900709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32264669109183804148803781 6049625457971963277900709)
    ·
      refine ⟨1134304773369743114606383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6049625457971963277900709 1134304773369743114606383)
      ·
        refine ⟨1701457160054614671909575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1134304773369743114606383 1701457160054614671909575)
        ·
          refine ⟨2552185740081922007864363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1701457160054614671909575 2552185740081922007864363)
          ·
            refine ⟨3828278610122883011796545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2552185740081922007864363 3828278610122883011796545)
            ·
              refine ⟨2871208957592162258847409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3828278610122883011796545 2871208957592162258847409)
              ·
                refine ⟨2153406718194121694135557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2871208957592162258847409 2153406718194121694135557)
                ·
                  refine ⟨403763759661397817650417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2153406718194121694135557 403763759661397817650417)
                  ·
                    rfl

theorem cell21_1769236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 2, 4].length) (baseStart_1769236 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1769236 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1769236 prefixEnd_1769236 := by exact prefixLift 1769236
  have htrace : WordTrace (prefixWord ++ tailWord_1769236) baseStart_1769236 baseEnd_1769236 := by
    simpa [prefixWord, tailWord_1769236, baseEnd_1769236] using wordTrace_append hprefix tailTrace_1769236
  have hstable : (prefixWord ++ tailWord_1769236).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1769236).length < 2 ^ (prefixWord ++ tailWord_1769236).sum := by decide
  have hdescent : baseEnd_1769236 < baseStart_1769236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1769236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1769306 : List Nat := [3, 1, 1, 2, 1, 3, 1, 6, 3]
def baseStart_1769306 : Nat := 118140960795 + 1769306 * 2 ^ 59
def prefixEnd_1769306 : Nat := 4983230072969 + 3 ^ 40 * 1769306 * 2
def baseEnd_1769306 : Nat := 403779734615093251483607

theorem tailTrace_1769306 : CollatzResearch.WordTrace tailWord_1769306 prefixEnd_1769306 403779734615093251483607 := by
  unfold tailWord_1769306
  simp only [CollatzResearch.WordTrace]
  refine ⟨16132972832028502563163943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43021260885409340168437181 16132972832028502563163943)
  ·
    refine ⟨24199459248042753844745915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16132972832028502563163943 24199459248042753844745915)
    ·
      refine ⟨36299188872064130767118873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24199459248042753844745915 36299188872064130767118873)
      ·
        refine ⟨27224391654048098075339155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36299188872064130767118873 27224391654048098075339155)
        ·
          refine ⟨40836587481072147113008733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27224391654048098075339155 40836587481072147113008733)
          ·
            refine ⟨15313720305402055167378275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40836587481072147113008733 15313720305402055167378275)
            ·
              refine ⟨22970580458103082751067413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15313720305402055167378275 22970580458103082751067413)
              ·
                refine ⟨1076745958973582003956285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 22970580458103082751067413 1076745958973582003956285)
                ·
                  refine ⟨403779734615093251483607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1076745958973582003956285 403779734615093251483607)
                  ·
                    rfl

theorem cell21_1769306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 6, 3].length) (baseStart_1769306 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1769306 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1769306 prefixEnd_1769306 := by exact prefixLift 1769306
  have htrace : WordTrace (prefixWord ++ tailWord_1769306) baseStart_1769306 baseEnd_1769306 := by
    simpa [prefixWord, tailWord_1769306, baseEnd_1769306] using wordTrace_append hprefix tailTrace_1769306
  have hstable : (prefixWord ++ tailWord_1769306).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1769306).length < 2 ^ (prefixWord ++ tailWord_1769306).sum := by decide
  have hdescent : baseEnd_1769306 < baseStart_1769306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1769306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1769351 : List Nat := [1, 1, 4, 2, 4, 2, 7]
def baseStart_1769351 : Nat := 118140960795 + 1769351 * 2 ^ 59
def prefixEnd_1769351 : Nat := 4983230072969 + 3 ^ 40 * 1769351 * 2
def baseEnd_1769351 : Nat := 44865556025353685914835

theorem tailTrace_1769351 : CollatzResearch.WordTrace tailWord_1769351 prefixEnd_1769351 44865556025353685914835 := by
  unfold tailWord_1769351
  simp only [CollatzResearch.WordTrace]
  refine ⟨64533532612950982938043907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43022355075300655292029271 64533532612950982938043907)
  ·
    refine ⟨96800298919426474407065861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64533532612950982938043907 96800298919426474407065861)
    ·
      refine ⟨18150056047392463951324849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96800298919426474407065861 18150056047392463951324849)
      ·
        refine ⟨13612542035544347963493637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18150056047392463951324849 13612542035544347963493637)
        ·
          refine ⟨2552351631664565243155057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13612542035544347963493637 2552351631664565243155057)
          ·
            refine ⟨1914263723748423932366293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2552351631664565243155057 1914263723748423932366293)
            ·
              refine ⟨44865556025353685914835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1914263723748423932366293 44865556025353685914835)
              ·
                rfl

theorem cell21_1769351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 7].length) (baseStart_1769351 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1769351 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1769351 prefixEnd_1769351 := by exact prefixLift 1769351
  have htrace : WordTrace (prefixWord ++ tailWord_1769351) baseStart_1769351 baseEnd_1769351 := by
    simpa [prefixWord, tailWord_1769351, baseEnd_1769351] using wordTrace_append hprefix tailTrace_1769351
  have hstable : (prefixWord ++ tailWord_1769351).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1769351).length < 2 ^ (prefixWord ++ tailWord_1769351).sum := by decide
  have hdescent : baseEnd_1769351 < baseStart_1769351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1769351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1769368 : List Nat := [2, 1, 2, 6, 1, 1, 2, 6]
def baseStart_1769368 : Nat := 118140960795 + 1769368 * 2 ^ 59
def prefixEnd_1769368 : Nat := 4983230072969 + 3 ^ 40 * 1769368 * 2
def baseEnd_1769368 : Nat := 134597961286598307150049

theorem tailTrace_1769368 : CollatzResearch.WordTrace tailWord_1769368 prefixEnd_1769368 134597961286598307150049 := by
  unfold tailWord_1769368
  simp only [CollatzResearch.WordTrace]
  refine ⟨32267076326944697420706379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43022768435926263227608505 32267076326944697420706379)
  ·
    refine ⟨48400614490417046131059569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32267076326944697420706379 48400614490417046131059569)
    ·
      refine ⟨36300460867812784598294677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48400614490417046131059569 36300460867812784598294677)
      ·
        refine ⟨1701584103178724278045063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 36300460867812784598294677 1701584103178724278045063)
        ·
          refine ⟨2552376154768086417067595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1701584103178724278045063 2552376154768086417067595)
          ·
            refine ⟨3828564232152129625601393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2552376154768086417067595 3828564232152129625601393)
            ·
              refine ⟨2871423174114097219201045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3828564232152129625601393 2871423174114097219201045)
              ·
                refine ⟨134597961286598307150049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2871423174114097219201045 134597961286598307150049)
                ·
                  rfl

theorem cell21_1769368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 6].length) (baseStart_1769368 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1769368 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1769368 prefixEnd_1769368 := by exact prefixLift 1769368
  have htrace : WordTrace (prefixWord ++ tailWord_1769368) baseStart_1769368 baseEnd_1769368 := by
    simpa [prefixWord, tailWord_1769368, baseEnd_1769368] using wordTrace_append hprefix tailTrace_1769368
  have hstable : (prefixWord ++ tailWord_1769368).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1769368).length < 2 ^ (prefixWord ++ tailWord_1769368).sum := by decide
  have hdescent : baseEnd_1769368 < baseStart_1769368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1769368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1769416 : List Nat := [2, 1, 3, 1, 4, 3, 2, 2, 3]
def baseStart_1769416 : Nat := 118140960795 + 1769416 * 2 ^ 59
def prefixEnd_1769416 : Nat := 4983230072969 + 3 ^ 40 * 1769416 * 2
def baseEnd_1769416 : Nat := 403804838113757504650049

theorem tailTrace_1769416 : CollatzResearch.WordTrace tailWord_1769416 prefixEnd_1769416 403804838113757504650049 := by
  unfold tailWord_1769416
  simp only [CollatzResearch.WordTrace]
  refine ⟨32267951678857749519580051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43023935571810332692773401 32267951678857749519580051)
  ·
    refine ⟨48401927518286624279370077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32267951678857749519580051 48401927518286624279370077)
    ·
      refine ⟨18150722819357484104763779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48401927518286624279370077 18150722819357484104763779)
      ·
        refine ⟨27226084229036226157145669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18150722819357484104763779 27226084229036226157145669)
        ·
          refine ⟨5104890792944292404464813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27226084229036226157145669 5104890792944292404464813)
          ·
            refine ⟨1914334047354109651674305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5104890792944292404464813 1914334047354109651674305)
            ·
              refine ⟨1435750535515582238755729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1914334047354109651674305 1435750535515582238755729)
              ·
                refine ⟨1076812901636686679066797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1435750535515582238755729 1076812901636686679066797)
                ·
                  refine ⟨403804838113757504650049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1076812901636686679066797 403804838113757504650049)
                  ·
                    rfl

theorem cell21_1769416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 2, 2, 3].length) (baseStart_1769416 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1769416 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1769416 prefixEnd_1769416 := by exact prefixLift 1769416
  have htrace : WordTrace (prefixWord ++ tailWord_1769416) baseStart_1769416 baseEnd_1769416 := by
    simpa [prefixWord, tailWord_1769416, baseEnd_1769416] using wordTrace_append hprefix tailTrace_1769416
  have hstable : (prefixWord ++ tailWord_1769416).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1769416).length < 2 ^ (prefixWord ++ tailWord_1769416).sum := by decide
  have hdescent : baseEnd_1769416 < baseStart_1769416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1769416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1769455 : List Nat := [1, 1, 2, 1, 4, 2, 2, 2, 6]
def baseStart_1769455 : Nat := 118140960795 + 1769455 * 2 ^ 59
def prefixEnd_1769455 : Nat := 4983230072969 + 3 ^ 40 * 1769455 * 2
def baseEnd_1769455 : Nat := 403813738445102103499969

theorem tailTrace_1769455 : CollatzResearch.WordTrace tailWord_1769455 prefixEnd_1769455 403813738445102103499969 := by
  unfold tailWord_1769455
  simp only [CollatzResearch.WordTrace]
  refine ⟨64537325804574208699829819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43024883869716139133219879 64537325804574208699829819)
  ·
    refine ⟨96805988706861313049744729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64537325804574208699829819 96805988706861313049744729)
    ·
      refine ⟨72604491530145984787308547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96805988706861313049744729 72604491530145984787308547)
      ·
        refine ⟨108906737295218977180962821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72604491530145984787308547 108906737295218977180962821)
        ·
          refine ⟨20420013242853558221430529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108906737295218977180962821 20420013242853558221430529)
          ·
            refine ⟨15315009932140168666072897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20420013242853558221430529 15315009932140168666072897)
            ·
              refine ⟨11486257449105126499554673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15315009932140168666072897 11486257449105126499554673)
              ·
                refine ⟨8614693086828844874666005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11486257449105126499554673 8614693086828844874666005)
                ·
                  refine ⟨403813738445102103499969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8614693086828844874666005 403813738445102103499969)
                  ·
                    rfl

theorem cell21_1769455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 2, 6].length) (baseStart_1769455 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1769455 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1769455 prefixEnd_1769455 := by exact prefixLift 1769455
  have htrace : WordTrace (prefixWord ++ tailWord_1769455) baseStart_1769455 baseEnd_1769455 := by
    simpa [prefixWord, tailWord_1769455, baseEnd_1769455] using wordTrace_append hprefix tailTrace_1769455
  have hstable : (prefixWord ++ tailWord_1769455).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1769455).length < 2 ^ (prefixWord ++ tailWord_1769455).sum := by decide
  have hdescent : baseEnd_1769455 < baseStart_1769455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1769455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1769486 : List Nat := [4, 1, 1, 2, 2, 1, 2, 8]
def baseStart_1769486 : Nat := 118140960795 + 1769486 * 2 ^ 59
def prefixEnd_1769486 : Nat := 4983230072969 + 3 ^ 40 * 1769486 * 2
def baseEnd_1769486 : Nat := 134606937689150979494413

theorem tailTrace_1769486 : CollatzResearch.WordTrace tailWord_1769486 prefixEnd_1769486 134606937689150979494413 := by
  unfold tailWord_1769486
  simp only [CollatzResearch.WordTrace]
  refine ⟨8067307058432737624276039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43025637644974600662805541 8067307058432737624276039)
  ·
    refine ⟨12100960587649106436414059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8067307058432737624276039 12100960587649106436414059)
    ·
      refine ⟨18151440881473659654621089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12100960587649106436414059 18151440881473659654621089)
      ·
        refine ⟨13613580661105244740965817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18151440881473659654621089 13613580661105244740965817)
        ·
          refine ⟨10210185495828933555724363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13613580661105244740965817 10210185495828933555724363)
          ·
            refine ⟨15315278243743400333586545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10210185495828933555724363 15315278243743400333586545)
            ·
              refine ⟨11486458682807550250189909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15315278243743400333586545 11486458682807550250189909)
              ·
                refine ⟨134606937689150979494413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11486458682807550250189909 134606937689150979494413)
                ·
                  rfl

theorem cell21_1769486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 8].length) (baseStart_1769486 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1769486 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1769486 prefixEnd_1769486 := by exact prefixLift 1769486
  have htrace : WordTrace (prefixWord ++ tailWord_1769486) baseStart_1769486 baseEnd_1769486 := by
    simpa [prefixWord, tailWord_1769486, baseEnd_1769486] using wordTrace_append hprefix tailTrace_1769486
  have hstable : (prefixWord ++ tailWord_1769486).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1769486).length < 2 ^ (prefixWord ++ tailWord_1769486).sum := by decide
  have hdescent : baseEnd_1769486 < baseStart_1769486 := by decide
  rcases family_descends (prefixWord ++ tailWord_1769486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1769714 : List Nat := [3, 2, 1, 3, 2, 1, 1, 8]
def baseStart_1769714 : Nat := 118140960795 + 1769714 * 2 ^ 59
def prefixEnd_1769714 : Nat := 4983230072969 + 3 ^ 40 * 1769714 * 2
def baseEnd_1769714 : Nat := 134624281924591736227591

theorem tailTrace_1769714 : CollatzResearch.WordTrace tailWord_1769714 prefixEnd_1769714 134624281924591736227591 := by
  unfold tailWord_1769714
  simp only [CollatzResearch.WordTrace]
  refine ⟨16136693077658973983377049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43031181540423930622338797 16136693077658973983377049)
  ·
    refine ⟨12102519808244230487532787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16136693077658973983377049 12102519808244230487532787)
    ·
      refine ⟨18153779712366345731299181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12102519808244230487532787 18153779712366345731299181)
      ·
        refine ⟨6807667392137379649237193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18153779712366345731299181 6807667392137379649237193)
        ·
          refine ⟨5105750544103034736927895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6807667392137379649237193 5105750544103034736927895)
          ·
            refine ⟨7658625816154552105391843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5105750544103034736927895 7658625816154552105391843)
            ·
              refine ⟨11487938724231828158087765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7658625816154552105391843 11487938724231828158087765)
              ·
                refine ⟨134624281924591736227591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11487938724231828158087765 134624281924591736227591)
                ·
                  rfl

theorem cell21_1769714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 8].length) (baseStart_1769714 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1769714 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1769714 prefixEnd_1769714 := by exact prefixLift 1769714
  have htrace : WordTrace (prefixWord ++ tailWord_1769714) baseStart_1769714 baseEnd_1769714 := by
    simpa [prefixWord, tailWord_1769714, baseEnd_1769714] using wordTrace_append hprefix tailTrace_1769714
  have hstable : (prefixWord ++ tailWord_1769714).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1769714).length < 2 ^ (prefixWord ++ tailWord_1769714).sum := by decide
  have hdescent : baseEnd_1769714 < baseStart_1769714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1769714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1769728 : List Nat := [2, 1, 1, 2, 1, 1, 4, 4, 5]
def baseStart_1769728 : Nat := 118140960795 + 1769728 * 2 ^ 59
def prefixEnd_1769728 : Nat := 4983230072969 + 3 ^ 40 * 1769728 * 2
def baseEnd_1769728 : Nat := 403876040764514295449411

theorem tailTrace_1769728 : CollatzResearch.WordTrace tailWord_1769728 prefixEnd_1769728 403876040764514295449411 := by
  unfold tailWord_1769728
  simp only [CollatzResearch.WordTrace]
  refine ⟨32273641466292588162258919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43031521955056784216345225 32273641466292588162258919)
  ·
    refine ⟨48410462199438882243388379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32273641466292588162258919 48410462199438882243388379)
    ·
      refine ⟨72615693299158323365082569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48410462199438882243388379 72615693299158323365082569)
      ·
        refine ⟨54461769974368742523811927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72615693299158323365082569 54461769974368742523811927)
        ·
          refine ⟨81692654961553113785717891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54461769974368742523811927 81692654961553113785717891)
          ·
            refine ⟨122538982442329670678576837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81692654961553113785717891 122538982442329670678576837)
            ·
              refine ⟨22976059207936813252233157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 122538982442329670678576837 22976059207936813252233157)
              ·
                refine ⟨4308011101488152484793717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22976059207936813252233157 4308011101488152484793717)
                ·
                  refine ⟨403876040764514295449411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4308011101488152484793717 403876040764514295449411)
                  ·
                    rfl

theorem cell21_1769728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 4, 5].length) (baseStart_1769728 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1769728 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1769728 prefixEnd_1769728 := by exact prefixLift 1769728
  have htrace : WordTrace (prefixWord ++ tailWord_1769728) baseStart_1769728 baseEnd_1769728 := by
    simpa [prefixWord, tailWord_1769728, baseEnd_1769728] using wordTrace_append hprefix tailTrace_1769728
  have hstable : (prefixWord ++ tailWord_1769728).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1769728).length < 2 ^ (prefixWord ++ tailWord_1769728).sum := by decide
  have hdescent : baseEnd_1769728 < baseStart_1769728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1769728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1769796 : List Nat := [2, 3, 4, 1, 2, 1, 2, 3, 3]
def baseStart_1769796 : Nat := 118140960795 + 1769796 * 2 ^ 59
def prefixEnd_1769796 : Nat := 4983230072969 + 3 ^ 40 * 1769796 * 2
def baseEnd_1769796 : Nat := 403891559290961288315939

theorem tailTrace_1769796 : CollatzResearch.WordTrace tailWord_1769796 prefixEnd_1769796 403891559290961288315939 := by
  unfold tailWord_1769796
  simp only [CollatzResearch.WordTrace]
  refine ⟨32274881548169411968996621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43033175397559215958662161 32274881548169411968996621)
  ·
    refine ⟨12103080580563529488373733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32274881548169411968996621 12103080580563529488373733)
    ·
      refine ⟨2269327608855661779070075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12103080580563529488373733 2269327608855661779070075)
      ·
        refine ⟨3403991413283492668605113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2269327608855661779070075 3403991413283492668605113)
        ·
          refine ⟨2552993559962619501453835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3403991413283492668605113 2552993559962619501453835)
          ·
            refine ⟨3829490339943929252180753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2552993559962619501453835 3829490339943929252180753)
            ·
              refine ⟨2872117754957946939135565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3829490339943929252180753 2872117754957946939135565)
              ·
                refine ⟨1077044158109230102175837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2872117754957946939135565 1077044158109230102175837)
                ·
                  refine ⟨403891559290961288315939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1077044158109230102175837 403891559290961288315939)
                  ·
                    rfl

theorem cell21_1769796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 3, 3].length) (baseStart_1769796 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1769796 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1769796 prefixEnd_1769796 := by exact prefixLift 1769796
  have htrace : WordTrace (prefixWord ++ tailWord_1769796) baseStart_1769796 baseEnd_1769796 := by
    simpa [prefixWord, tailWord_1769796, baseEnd_1769796] using wordTrace_append hprefix tailTrace_1769796
  have hstable : (prefixWord ++ tailWord_1769796).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1769796).length < 2 ^ (prefixWord ++ tailWord_1769796).sum := by decide
  have hdescent : baseEnd_1769796 < baseStart_1769796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1769796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1769804 : List Nat := [2, 2, 1, 3, 2, 1, 1, 2, 7]
def baseStart_1769804 : Nat := 118140960795 + 1769804 * 2 ^ 59
def prefixEnd_1769804 : Nat := 4983230072969 + 3 ^ 40 * 1769804 * 2
def baseEnd_1769804 : Nat := 403893384999955052182589

theorem tailTrace_1769804 : CollatzResearch.WordTrace tailWord_1769804 prefixEnd_1769804 403893384999955052182589 := by
  unfold tailWord_1769804
  simp only [CollatzResearch.WordTrace]
  refine ⟨32275027440154920652142233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43033369920206560869522977 32275027440154920652142233)
  ·
    refine ⟨24206270580116190489106675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32275027440154920652142233 24206270580116190489106675)
    ·
      refine ⟨36309405870174285733660013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24206270580116190489106675 36309405870174285733660013)
      ·
        refine ⟨13616027201315357150122505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36309405870174285733660013 13616027201315357150122505)
        ·
          refine ⟨10212020400986517862591879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13616027201315357150122505 10212020400986517862591879)
          ·
            refine ⟨15318030601479776793887819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10212020400986517862591879 15318030601479776793887819)
            ·
              refine ⟨22977045902219665190831729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15318030601479776793887819 22977045902219665190831729)
              ·
                refine ⟨17232784426664748893123797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22977045902219665190831729 17232784426664748893123797)
                ·
                  refine ⟨403893384999955052182589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17232784426664748893123797 403893384999955052182589)
                  ·
                    rfl

theorem cell21_1769804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 7].length) (baseStart_1769804 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1769804 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1769804 prefixEnd_1769804 := by exact prefixLift 1769804
  have htrace : WordTrace (prefixWord ++ tailWord_1769804) baseStart_1769804 baseEnd_1769804 := by
    simpa [prefixWord, tailWord_1769804, baseEnd_1769804] using wordTrace_append hprefix tailTrace_1769804
  have hstable : (prefixWord ++ tailWord_1769804).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1769804).length < 2 ^ (prefixWord ++ tailWord_1769804).sum := by decide
  have hdescent : baseEnd_1769804 < baseStart_1769804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1769804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1769886 : List Nat := [4, 3, 1, 2, 1, 1, 4, 1, 4]
def baseStart_1769886 : Nat := 118140960795 + 1769886 * 2 ^ 59
def prefixEnd_1769886 : Nat := 4983230072969 + 3 ^ 40 * 1769886 * 2
def baseEnd_1769886 : Nat := 403912098517141131815755

theorem tailTrace_1769886 : CollatzResearch.WordTrace tailWord_1769886 prefixEnd_1769886 403912098517141131815755 := by
  unfold tailWord_1769886
  simp only [CollatzResearch.WordTrace]
  refine ⟨8069130708251596163596189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43035363777341846205846341 8069130708251596163596189)
  ·
    refine ⟨3025924015594348561348571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8069130708251596163596189 3025924015594348561348571)
    ·
      refine ⟨4538886023391522842022857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3025924015594348561348571 4538886023391522842022857)
      ·
        refine ⟨3404164517543642131517143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4538886023391522842022857 3404164517543642131517143)
        ·
          refine ⟨5106246776315463197275715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3404164517543642131517143 5106246776315463197275715)
          ·
            refine ⟨7659370164473194795913573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5106246776315463197275715 7659370164473194795913573)
            ·
              refine ⟨1436131905838724024233795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7659370164473194795913573 1436131905838724024233795)
              ·
                refine ⟨2154197858758086036350693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1436131905838724024233795 2154197858758086036350693)
                ·
                  refine ⟨403912098517141131815755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2154197858758086036350693 403912098517141131815755)
                  ·
                    rfl

theorem cell21_1769886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_1769886 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1769886 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1769886 prefixEnd_1769886 := by exact prefixLift 1769886
  have htrace : WordTrace (prefixWord ++ tailWord_1769886) baseStart_1769886 baseEnd_1769886 := by
    simpa [prefixWord, tailWord_1769886, baseEnd_1769886] using wordTrace_append hprefix tailTrace_1769886
  have hstable : (prefixWord ++ tailWord_1769886).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1769886).length < 2 ^ (prefixWord ++ tailWord_1769886).sum := by decide
  have hdescent : baseEnd_1769886 < baseStart_1769886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1769886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1769928 : List Nat := [2, 1, 3, 1, 3, 3, 2, 2, 4]
def baseStart_1769928 : Nat := 118140960795 + 1769928 * 2 ^ 59
def prefixEnd_1769928 : Nat := 4983230072969 + 3 ^ 40 * 1769928 * 2
def baseEnd_1769928 : Nat := 403921683489358392115669

theorem tailTrace_1769928 : CollatzResearch.WordTrace tailWord_1769928 prefixEnd_1769928 403921683489358392115669 := by
  unfold tailWord_1769928
  simp only [CollatzResearch.WordTrace]
  refine ⟨32277288765930305240899219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43036385021240406987865625 32277288765930305240899219)
  ·
    refine ⟨48415933148895457861348829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32277288765930305240899219 48415933148895457861348829)
    ·
      refine ⟨18155974930835796698005811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48415933148895457861348829 18155974930835796698005811)
      ·
        refine ⟨27233962396253695047008717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18155974930835796698005811 27233962396253695047008717)
        ·
          refine ⟨10212735898595135642628269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27233962396253695047008717 10212735898595135642628269)
          ·
            refine ⟨3829775961973175865985601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10212735898595135642628269 3829775961973175865985601)
            ·
              refine ⟨2872331971479881899489201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3829775961973175865985601 2872331971479881899489201)
              ·
                refine ⟨2154248978609911424616901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2872331971479881899489201 2154248978609911424616901)
                ·
                  refine ⟨403921683489358392115669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2154248978609911424616901 403921683489358392115669)
                  ·
                    rfl

theorem cell21_1769928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 2, 4].length) (baseStart_1769928 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1769928 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1769928 prefixEnd_1769928 := by exact prefixLift 1769928
  have htrace : WordTrace (prefixWord ++ tailWord_1769928) baseStart_1769928 baseEnd_1769928 := by
    simpa [prefixWord, tailWord_1769928, baseEnd_1769928] using wordTrace_append hprefix tailTrace_1769928
  have hstable : (prefixWord ++ tailWord_1769928).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1769928).length < 2 ^ (prefixWord ++ tailWord_1769928).sum := by decide
  have hdescent : baseEnd_1769928 < baseStart_1769928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1769928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770049 : List Nat := [1, 2, 5, 1, 1, 2, 3, 1, 5]
def baseStart_1770049 : Nat := 118140960795 + 1770049 * 2 ^ 59
def prefixEnd_1770049 : Nat := 4983230072969 + 3 ^ 40 * 1770049 * 2
def baseEnd_1770049 : Nat := 403949297337889070598755

theorem tailTrace_1770049 : CollatzResearch.WordTrace tailWord_1770049 prefixEnd_1770049 403949297337889070598755 := by
  unfold tailWord_1770049
  simp only [CollatzResearch.WordTrace]
  refine ⟨64558990764422248146953201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43039327176281498764635467 64558990764422248146953201)
  ·
    refine ⟨48419243073316686110214901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64558990764422248146953201 48419243073316686110214901)
    ·
      refine ⟨4539304038123439322832647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48419243073316686110214901 4539304038123439322832647)
      ·
        refine ⟨6808956057185158984248971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4539304038123439322832647 6808956057185158984248971)
        ·
          refine ⟨10213434085777738476373457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6808956057185158984248971 10213434085777738476373457)
          ·
            refine ⟨7660075564333303857280093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10213434085777738476373457 7660075564333303857280093)
            ·
              refine ⟨2872528336624988946480035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7660075564333303857280093 2872528336624988946480035)
              ·
                refine ⟨4308792504937483419720053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2872528336624988946480035 4308792504937483419720053)
                ·
                  refine ⟨403949297337889070598755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4308792504937483419720053 403949297337889070598755)
                  ·
                    rfl

theorem cell21_1770049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 1, 5].length) (baseStart_1770049 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1770049 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1770049 prefixEnd_1770049 := by exact prefixLift 1770049
  have htrace : WordTrace (prefixWord ++ tailWord_1770049) baseStart_1770049 baseEnd_1770049 := by
    simpa [prefixWord, tailWord_1770049, baseEnd_1770049] using wordTrace_append hprefix tailTrace_1770049
  have hstable : (prefixWord ++ tailWord_1770049).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770049).length < 2 ^ (prefixWord ++ tailWord_1770049).sum := by decide
  have hdescent : baseEnd_1770049 < baseStart_1770049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770091 : List Nat := [1, 1, 1, 1, 2, 2, 1, 3, 9]
def baseStart_1770091 : Nat := 118140960795 + 1770091 * 2 ^ 59
def prefixEnd_1770091 : Nat := 4983230072969 + 3 ^ 40 * 1770091 * 2
def baseEnd_1770091 : Nat := 403958882310106330898669

theorem tailTrace_1770091 : CollatzResearch.WordTrace tailWord_1770091 prefixEnd_1770091 403958882310106330898669 := by
  unfold tailWord_1770091
  simp only [CollatzResearch.WordTrace]
  refine ⟨64560522630270089319982127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43040348420180059546654751 64560522630270089319982127)
  ·
    refine ⟨96840783945405133979973191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64560522630270089319982127 96840783945405133979973191)
    ·
      refine ⟨145261175918107700969959787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96840783945405133979973191 145261175918107700969959787)
      ·
        refine ⟨217891763877161551454939681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145261175918107700969959787 217891763877161551454939681)
        ·
          refine ⟨163418822907871163591204761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217891763877161551454939681 163418822907871163591204761)
          ·
            refine ⟨122564117180903372693403571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163418822907871163591204761 122564117180903372693403571)
            ·
              refine ⟨183846175771355059040105357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122564117180903372693403571 183846175771355059040105357)
              ·
                refine ⟨68942315914258147140039509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 183846175771355059040105357 68942315914258147140039509)
                ·
                  refine ⟨403958882310106330898669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 68942315914258147140039509 403958882310106330898669)
                  ·
                    rfl

theorem cell21_1770091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 9].length) (baseStart_1770091 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1770091 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1770091 prefixEnd_1770091 := by exact prefixLift 1770091
  have htrace : WordTrace (prefixWord ++ tailWord_1770091) baseStart_1770091 baseEnd_1770091 := by
    simpa [prefixWord, tailWord_1770091, baseEnd_1770091] using wordTrace_append hprefix tailTrace_1770091
  have hstable : (prefixWord ++ tailWord_1770091).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770091).length < 2 ^ (prefixWord ++ tailWord_1770091).sum := by decide
  have hdescent : baseEnd_1770091 < baseStart_1770091 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770184 : List Nat := [2, 1, 3, 1, 2, 3, 2, 2, 5]
def baseStart_1770184 : Nat := 118140960795 + 1770184 * 2 ^ 59
def prefixEnd_1770184 : Nat := 4983230072969 + 3 ^ 40 * 1770184 * 2
def baseEnd_1770184 : Nat := 403980106177158835848479

theorem tailTrace_1770184 : CollatzResearch.WordTrace tailWord_1770184 prefixEnd_1770184 403980106177158835848479 := by
  unfold tailWord_1770184
  simp only [CollatzResearch.WordTrace]
  refine ⟨32281957309466583101558803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43042609745955444135411737 32281957309466583101558803)
  ·
    refine ⟨48422935964199874652338205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32281957309466583101558803 48422935964199874652338205)
    ·
      refine ⟨18158600986574952994626827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48422935964199874652338205 18158600986574952994626827)
      ·
        refine ⟨27237901479862429491940241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18158600986574952994626827 27237901479862429491940241)
        ·
          refine ⟨20428426109896822118955181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27237901479862429491940241 20428426109896822118955181)
          ·
            refine ⟨7660659791211308294608193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20428426109896822118955181 7660659791211308294608193)
            ·
              refine ⟨5745494843408481220956145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7660659791211308294608193 5745494843408481220956145)
              ·
                refine ⟨4309121132556360915717109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5745494843408481220956145 4309121132556360915717109)
                ·
                  refine ⟨403980106177158835848479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4309121132556360915717109 403980106177158835848479)
                  ·
                    rfl

theorem cell21_1770184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 2, 5].length) (baseStart_1770184 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1770184 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1770184 prefixEnd_1770184 := by exact prefixLift 1770184
  have htrace : WordTrace (prefixWord ++ tailWord_1770184) baseStart_1770184 baseEnd_1770184 := by
    simpa [prefixWord, tailWord_1770184, baseEnd_1770184] using wordTrace_append hprefix tailTrace_1770184
  have hstable : (prefixWord ++ tailWord_1770184).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770184).length < 2 ^ (prefixWord ++ tailWord_1770184).sum := by decide
  have hdescent : baseEnd_1770184 < baseStart_1770184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770243 : List Nat := [1, 1, 1, 3, 2, 2, 1, 3, 7]
def baseStart_1770243 : Nat := 118140960795 + 1770243 * 2 ^ 59
def prefixEnd_1770243 : Nat := 4983230072969 + 3 ^ 40 * 1770243 * 2
def baseEnd_1770243 : Nat := 403993570780987844365025

theorem tailTrace_1770243 : CollatzResearch.WordTrace tailWord_1770243 prefixEnd_1770243 403993570780987844365025 := by
  unfold tailWord_1770243
  simp only [CollatzResearch.WordTrace]
  refine ⟨64566066525719419279515383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43044044350479612853010255 64566066525719419279515383)
  ·
    refine ⟨96849099788579128919273075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64566066525719419279515383 96849099788579128919273075)
    ·
      refine ⟨145273649682868693378909613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96849099788579128919273075 145273649682868693378909613)
      ·
        refine ⟨54477618631075760017091105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145273649682868693378909613 54477618631075760017091105)
        ·
          refine ⟨40858213973306820012818329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54477618631075760017091105 40858213973306820012818329)
          ·
            refine ⟨30643660479980115009613747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40858213973306820012818329 30643660479980115009613747)
            ·
              refine ⟨45965490719970172514420621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30643660479980115009613747 45965490719970172514420621)
              ·
                refine ⟨17237059019988814692907733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45965490719970172514420621 17237059019988814692907733)
                ·
                  refine ⟨403993570780987844365025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17237059019988814692907733 403993570780987844365025)
                  ·
                    rfl

theorem cell21_1770243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 7].length) (baseStart_1770243 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1770243 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1770243 prefixEnd_1770243 := by exact prefixLift 1770243
  have htrace : WordTrace (prefixWord ++ tailWord_1770243) baseStart_1770243 baseEnd_1770243 := by
    simpa [prefixWord, tailWord_1770243, baseEnd_1770243] using wordTrace_append hprefix tailTrace_1770243
  have hstable : (prefixWord ++ tailWord_1770243).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770243).length < 2 ^ (prefixWord ++ tailWord_1770243).sum := by decide
  have hdescent : baseEnd_1770243 < baseStart_1770243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770269 : List Nat := [1, 4, 2, 4, 2, 1, 2, 2, 3]
def baseStart_1770269 : Nat := 118140960795 + 1770269 * 2 ^ 59
def prefixEnd_1770269 : Nat := 4983230072969 + 3 ^ 40 * 1770269 * 2
def baseEnd_1770269 : Nat := 403999504335217576931639

theorem tailTrace_1770269 : CollatzResearch.WordTrace tailWord_1770269 prefixEnd_1770269 403999504335217576931639 := by
  unfold tailWord_1770269
  simp only [CollatzResearch.WordTrace]
  refine ⟨64567014823625225719961861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43044676549083483813307907 64567014823625225719961861)
  ·
    refine ⟨12106315279429729822492849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64567014823625225719961861 12106315279429729822492849)
    ·
      refine ⟨9079736459572297366869637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12106315279429729822492849 9079736459572297366869637)
      ·
        refine ⟨1702450586169805756288057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9079736459572297366869637 1702450586169805756288057)
        ·
          refine ⟨1276837939627354317216043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1702450586169805756288057 1276837939627354317216043)
          ·
            refine ⟨1915256909441031475824065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1276837939627354317216043 1915256909441031475824065)
            ·
              refine ⟨1436442682080773606868049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1915256909441031475824065 1436442682080773606868049)
              ·
                refine ⟨1077332011560580205151037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1436442682080773606868049 1077332011560580205151037)
                ·
                  refine ⟨403999504335217576931639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1077332011560580205151037 403999504335217576931639)
                  ·
                    rfl

theorem cell21_1770269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 2, 2, 3].length) (baseStart_1770269 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1770269 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1770269 prefixEnd_1770269 := by exact prefixLift 1770269
  have htrace : WordTrace (prefixWord ++ tailWord_1770269) baseStart_1770269 baseEnd_1770269 := by
    simpa [prefixWord, tailWord_1770269, baseEnd_1770269] using wordTrace_append hprefix tailTrace_1770269
  have hstable : (prefixWord ++ tailWord_1770269).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770269).length < 2 ^ (prefixWord ++ tailWord_1770269).sum := by decide
  have hdescent : baseEnd_1770269 < baseStart_1770269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770277 : List Nat := [1, 3, 1, 2, 3, 1, 3, 4, 3]
def baseStart_1770277 : Nat := 118140960795 + 1770277 * 2 ^ 59
def prefixEnd_1770277 : Nat := 4983230072969 + 3 ^ 40 * 1770277 * 2
def baseEnd_1770277 : Nat := 404001330044211340798289

theorem tailTrace_1770277 : CollatzResearch.WordTrace tailWord_1770277 prefixEnd_1770277 404001330044211340798289 := by
  unfold tailWord_1770277
  simp only [CollatzResearch.WordTrace]
  refine ⟨64567306607596243086253085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43044871071730828724168723 64567306607596243086253085)
  ·
    refine ⟨24212739977848591157344907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64567306607596243086253085 24212739977848591157344907)
    ·
      refine ⟨36319109966772886736017361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24212739977848591157344907 36319109966772886736017361)
      ·
        refine ⟨27239332475079665052013021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36319109966772886736017361 27239332475079665052013021)
        ·
          refine ⟨10214749678154874394504883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27239332475079665052013021 10214749678154874394504883)
          ·
            refine ⟨15322124517232311591757325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10214749678154874394504883 15322124517232311591757325)
            ·
              refine ⟨5745796693962116846908997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15322124517232311591757325 5745796693962116846908997)
              ·
                refine ⟨1077336880117896908795437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5745796693962116846908997 1077336880117896908795437)
                ·
                  refine ⟨404001330044211340798289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1077336880117896908795437 404001330044211340798289)
                  ·
                    rfl

theorem cell21_1770277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 4, 3].length) (baseStart_1770277 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1770277 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1770277 prefixEnd_1770277 := by exact prefixLift 1770277
  have htrace : WordTrace (prefixWord ++ tailWord_1770277) baseStart_1770277 baseEnd_1770277 := by
    simpa [prefixWord, tailWord_1770277, baseEnd_1770277] using wordTrace_append hprefix tailTrace_1770277
  have hstable : (prefixWord ++ tailWord_1770277).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770277).length < 2 ^ (prefixWord ++ tailWord_1770277).sum := by decide
  have hdescent : baseEnd_1770277 < baseStart_1770277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770291 : List Nat := [1, 1, 1, 2, 6, 1, 2, 3, 4]
def baseStart_1770291 : Nat := 118140960795 + 1770291 * 2 ^ 59
def prefixEnd_1770291 : Nat := 4983230072969 + 3 ^ 40 * 1770291 * 2
def baseEnd_1770291 : Nat := 404004525034950427564927

theorem tailTrace_1770291 : CollatzResearch.WordTrace tailWord_1770291 prefixEnd_1770291 404004525034950427564927 := by
  unfold tailWord_1770291
  simp only [CollatzResearch.WordTrace]
  refine ⟨64567817229545523477262727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43045211486363682318175151 64567817229545523477262727)
  ·
    refine ⟨96851725844318285215894091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64567817229545523477262727 96851725844318285215894091)
    ·
      refine ⟨145277588766477427823841137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96851725844318285215894091 145277588766477427823841137)
      ·
        refine ⟨108958191574858070867880853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145277588766477427823841137 108958191574858070867880853)
        ·
          refine ⟨5107415230071472071931915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 108958191574858070867880853 5107415230071472071931915)
          ·
            refine ⟨7661122845107208107897873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5107415230071472071931915 7661122845107208107897873)
            ·
              refine ⟨5745842133830406080923405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7661122845107208107897873 5745842133830406080923405)
              ·
                refine ⟨2154690800186402280346277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5745842133830406080923405 2154690800186402280346277)
                ·
                  refine ⟨404004525034950427564927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2154690800186402280346277 404004525034950427564927)
                  ·
                    rfl

theorem cell21_1770291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 3, 4].length) (baseStart_1770291 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1770291 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1770291 prefixEnd_1770291 := by exact prefixLift 1770291
  have htrace : WordTrace (prefixWord ++ tailWord_1770291) baseStart_1770291 baseEnd_1770291 := by
    simpa [prefixWord, tailWord_1770291, baseEnd_1770291] using wordTrace_append hprefix tailTrace_1770291
  have hstable : (prefixWord ++ tailWord_1770291).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770291).length < 2 ^ (prefixWord ++ tailWord_1770291).sum := by decide
  have hdescent : baseEnd_1770291 < baseStart_1770291 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770294 : List Nat := [5, 1, 2, 2, 2, 1, 1, 2, 5]
def baseStart_1770294 : Nat := 118140960795 + 1770294 * 2 ^ 59
def prefixEnd_1770294 : Nat := 4983230072969 + 3 ^ 40 * 1770294 * 2
def baseEnd_1770294 : Nat := 404005209675823089014921

theorem tailTrace_1770294 : CollatzResearch.WordTrace tailWord_1770294 prefixEnd_1770294 404005209675823089014921 := by
  unfold tailWord_1770294
  simp only [CollatzResearch.WordTrace]
  refine ⟨4035495415533415936851371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43045284432356436659747957 4035495415533415936851371)
  ·
    refine ⟨6053243123300123905277057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4035495415533415936851371 6053243123300123905277057)
    ·
      refine ⟨4539932342475092928957793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6053243123300123905277057 4539932342475092928957793)
      ·
        refine ⟨3404949256856319696718345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4539932342475092928957793 3404949256856319696718345)
        ·
          refine ⟨2553711942642239772538759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3404949256856319696718345 2553711942642239772538759)
          ·
            refine ⟨3830567913963359658808139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2553711942642239772538759 3830567913963359658808139)
            ·
              refine ⟨5745851870945039488212209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3830567913963359658808139 5745851870945039488212209)
              ·
                refine ⟨4309388903208779616159157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5745851870945039488212209 4309388903208779616159157)
                ·
                  refine ⟨404005209675823089014921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4309388903208779616159157 404005209675823089014921)
                  ·
                    rfl

theorem cell21_1770294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_1770294 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1770294 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1770294 prefixEnd_1770294 := by exact prefixLift 1770294
  have htrace : WordTrace (prefixWord ++ tailWord_1770294) baseStart_1770294 baseEnd_1770294 := by
    simpa [prefixWord, tailWord_1770294, baseEnd_1770294] using wordTrace_append hprefix tailTrace_1770294
  have hstable : (prefixWord ++ tailWord_1770294).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770294).length < 2 ^ (prefixWord ++ tailWord_1770294).sum := by decide
  have hdescent : baseEnd_1770294 < baseStart_1770294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770336 : List Nat := [2, 1, 1, 3, 3, 1, 4, 1, 5]
def baseStart_1770336 : Nat := 118140960795 + 1770336 * 2 ^ 59
def prefixEnd_1770336 : Nat := 4983230072969 + 3 ^ 40 * 1770336 * 2
def baseEnd_1770336 : Nat := 404014794648040349314835

theorem tailTrace_1770336 : CollatzResearch.WordTrace tailWord_1770336 prefixEnd_1770336 404014794648040349314835 := by
  unfold tailWord_1770336
  simp only [CollatzResearch.WordTrace]
  refine ⟨32284729257191248081325431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43046305676254997441767241 32284729257191248081325431)
  ·
    refine ⟨48427093885786872121988147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32284729257191248081325431 48427093885786872121988147)
    ·
      refine ⟨72640640828680308182982221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48427093885786872121988147 72640640828680308182982221)
      ·
        refine ⟨27240240310755115568618333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72640640828680308182982221 27240240310755115568618333)
        ·
          refine ⟨10215090116533168338231875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27240240310755115568618333 10215090116533168338231875)
          ·
            refine ⟨15322635174799752507347813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10215090116533168338231875 15322635174799752507347813)
            ·
              refine ⟨2872994095274953595127715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15322635174799752507347813 2872994095274953595127715)
              ·
                refine ⟨4309491142912430392691573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2872994095274953595127715 4309491142912430392691573)
                ·
                  refine ⟨404014794648040349314835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4309491142912430392691573 404014794648040349314835)
                  ·
                    rfl

theorem cell21_1770336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 1, 5].length) (baseStart_1770336 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1770336 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1770336 prefixEnd_1770336 := by exact prefixLift 1770336
  have htrace : WordTrace (prefixWord ++ tailWord_1770336) baseStart_1770336 baseEnd_1770336 := by
    simpa [prefixWord, tailWord_1770336, baseEnd_1770336] using wordTrace_append hprefix tailTrace_1770336
  have hstable : (prefixWord ++ tailWord_1770336).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770336).length < 2 ^ (prefixWord ++ tailWord_1770336).sum := by decide
  have hdescent : baseEnd_1770336 < baseStart_1770336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770401 : List Nat := [1, 2, 3, 4, 1, 3, 2, 1, 4]
def baseStart_1770401 : Nat := 118140960795 + 1770401 * 2 ^ 59
def prefixEnd_1770401 : Nat := 4983230072969 + 3 ^ 40 * 1770401 * 2
def baseEnd_1770401 : Nat := 404029628533614680731369

theorem tailTrace_1770401 : CollatzResearch.WordTrace tailWord_1770401 prefixEnd_1770401 404029628533614680731369 := by
  unfold tailWord_1770401
  simp only [CollatzResearch.WordTrace]
  refine ⟨64571829259147012263767057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43047886172764674842511371 64571829259147012263767057)
  ·
    refine ⟨48428871944360259197825293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64571829259147012263767057 48428871944360259197825293)
    ·
      refine ⟨18160826979135097199184485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48428871944360259197825293 18160826979135097199184485)
      ·
        refine ⟨3405155058587830724847091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18160826979135097199184485 3405155058587830724847091)
        ·
          refine ⟨5107732587881746087270637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3405155058587830724847091 5107732587881746087270637)
          ·
            refine ⟨1915399720455654782726489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5107732587881746087270637 1915399720455654782726489)
            ·
              refine ⟨1436549790341741087044867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1915399720455654782726489 1436549790341741087044867)
              ·
                refine ⟨2154824685512611630567301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1436549790341741087044867 2154824685512611630567301)
                ·
                  refine ⟨404029628533614680731369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2154824685512611630567301 404029628533614680731369)
                  ·
                    rfl

theorem cell21_1770401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 2, 1, 4].length) (baseStart_1770401 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1770401 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1770401 prefixEnd_1770401 := by exact prefixLift 1770401
  have htrace : WordTrace (prefixWord ++ tailWord_1770401) baseStart_1770401 baseEnd_1770401 := by
    simpa [prefixWord, tailWord_1770401, baseEnd_1770401] using wordTrace_append hprefix tailTrace_1770401
  have hstable : (prefixWord ++ tailWord_1770401).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770401).length < 2 ^ (prefixWord ++ tailWord_1770401).sum := by decide
  have hdescent : baseEnd_1770401 < baseStart_1770401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770440 : List Nat := [2, 1, 3, 1, 14]
def baseStart_1770440 : Nat := 118140960795 + 1770440 * 2 ^ 59
def prefixEnd_1770440 : Nat := 4983230072969 + 3 ^ 40 * 1770440 * 2
def baseEnd_1770440 : Nat := 4988129985987151599769

theorem tailTrace_1770440 : CollatzResearch.WordTrace tailWord_1770440 prefixEnd_1770440 4988129985987151599769 := by
  unfold tailWord_1770440
  simp only [CollatzResearch.WordTrace]
  refine ⟨32286625853002860962218387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43048834470670481282957849 32286625853002860962218387)
  ·
    refine ⟨48429938779504291443327581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32286625853002860962218387 48429938779504291443327581)
    ·
      refine ⟨18161227042314109291247843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48429938779504291443327581 18161227042314109291247843)
      ·
        refine ⟨27241840563471163936871765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18161227042314109291247843 27241840563471163936871765)
        ·
          refine ⟨4988129985987151599769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 27241840563471163936871765 4988129985987151599769)
          ·
            rfl

theorem cell21_1770440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 14].length) (baseStart_1770440 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1770440 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1770440 prefixEnd_1770440 := by exact prefixLift 1770440
  have htrace : WordTrace (prefixWord ++ tailWord_1770440) baseStart_1770440 baseEnd_1770440 := by
    simpa [prefixWord, tailWord_1770440, baseEnd_1770440] using wordTrace_append hprefix tailTrace_1770440
  have hstable : (prefixWord ++ tailWord_1770440).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770440).length < 2 ^ (prefixWord ++ tailWord_1770440).sum := by decide
  have hdescent : baseEnd_1770440 < baseStart_1770440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770443 : List Nat := [1, 1, 1, 1, 3, 6, 2, 2, 4]
def baseStart_1770443 : Nat := 118140960795 + 1770443 * 2 ^ 59
def prefixEnd_1770443 : Nat := 4983230072969 + 3 ^ 40 * 1770443 * 2
def baseEnd_1770443 : Nat := 404039213505831941031283

theorem tailTrace_1770443 : CollatzResearch.WordTrace tailWord_1770443 prefixEnd_1770443 404039213505831941031283 := by
  unfold tailWord_1770443
  simp only [CollatzResearch.WordTrace]
  refine ⟨64573361124994853436795983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43048907416663235624530655 64573361124994853436795983)
  ·
    refine ⟨96860041687492280155193975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64573361124994853436795983 96860041687492280155193975)
    ·
      refine ⟨145290062531238420232790963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96860041687492280155193975 145290062531238420232790963)
      ·
        refine ⟨217935093796857630349186445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145290062531238420232790963 217935093796857630349186445)
        ·
          refine ⟨81725660173821611380944917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 217935093796857630349186445 81725660173821611380944917)
          ·
            refine ⟨3830890320647888033481793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 81725660173821611380944917 3830890320647888033481793)
            ·
              refine ⟨2873167740485916025111345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3830890320647888033481793 2873167740485916025111345)
              ·
                refine ⟨2154875805364437018833509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2873167740485916025111345 2154875805364437018833509)
                ·
                  refine ⟨404039213505831941031283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2154875805364437018833509 404039213505831941031283)
                  ·
                    rfl

theorem cell21_1770443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 2, 4].length) (baseStart_1770443 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1770443 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1770443 prefixEnd_1770443 := by exact prefixLift 1770443
  have htrace : WordTrace (prefixWord ++ tailWord_1770443) baseStart_1770443 baseEnd_1770443 := by
    simpa [prefixWord, tailWord_1770443, baseEnd_1770443] using wordTrace_append hprefix tailTrace_1770443
  have hstable : (prefixWord ++ tailWord_1770443).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770443).length < 2 ^ (prefixWord ++ tailWord_1770443).sum := by decide
  have hdescent : baseEnd_1770443 < baseStart_1770443 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770446 : List Nat := [4, 1, 1, 1, 2, 3, 4, 2, 3]
def baseStart_1770446 : Nat := 118140960795 + 1770446 * 2 ^ 59
def prefixEnd_1770446 : Nat := 4983230072969 + 3 ^ 40 * 1770446 * 2
def baseEnd_1770446 : Nat := 404039898146704602481277

theorem tailTrace_1770446 : CollatzResearch.WordTrace tailWord_1770446 prefixEnd_1770446 404039898146704602481277 := by
  unfold tailWord_1770446
  simp only [CollatzResearch.WordTrace]
  refine ⟨8071683817997998118644399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43048980362655989966103461 8071683817997998118644399)
  ·
    refine ⟨12107525726996997177966599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8071683817997998118644399 12107525726996997177966599)
    ·
      refine ⟨18161288590495495766949899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12107525726996997177966599 18161288590495495766949899)
      ·
        refine ⟨27241932885743243650424849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18161288590495495766949899 27241932885743243650424849)
        ·
          refine ⟨20431449664307432737818637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27241932885743243650424849 20431449664307432737818637)
          ·
            refine ⟨7661793624115287276681989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20431449664307432737818637 7661793624115287276681989)
            ·
              refine ⟨1436586304521616364377873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7661793624115287276681989 1436586304521616364377873)
              ·
                refine ⟨1077439728391212273283405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1436586304521616364377873 1077439728391212273283405)
                ·
                  refine ⟨404039898146704602481277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1077439728391212273283405 404039898146704602481277)
                  ·
                    rfl

theorem cell21_1770446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 4, 2, 3].length) (baseStart_1770446 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1770446 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1770446 prefixEnd_1770446 := by exact prefixLift 1770446
  have htrace : WordTrace (prefixWord ++ tailWord_1770446) baseStart_1770446 baseEnd_1770446 := by
    simpa [prefixWord, tailWord_1770446, baseEnd_1770446] using wordTrace_append hprefix tailTrace_1770446
  have hstable : (prefixWord ++ tailWord_1770446).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770446).length < 2 ^ (prefixWord ++ tailWord_1770446).sum := by decide
  have hdescent : baseEnd_1770446 < baseStart_1770446 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770457 : List Nat := [1, 2, 1, 2, 5, 1, 3, 6]
def baseStart_1770457 : Nat := 118140960795 + 1770457 * 2 ^ 59
def prefixEnd_1770457 : Nat := 4983230072969 + 3 ^ 40 * 1770457 * 2
def baseEnd_1770457 : Nat := 134680802832190342599307

theorem tailTrace_1770457 : CollatzResearch.WordTrace tailWord_1770457 prefixEnd_1770457 134680802832190342599307 := by
  unfold tailWord_1770457
  simp only [CollatzResearch.WordTrace]
  refine ⟨64573871746944133827805625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43049247831296089218537083 64573871746944133827805625)
  ·
    refine ⟨48430403810208100370854219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64573871746944133827805625 48430403810208100370854219)
    ·
      refine ⟨72645605715312150556281329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48430403810208100370854219 72645605715312150556281329)
      ·
        refine ⟨54484204286484112917210997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72645605715312150556281329 54484204286484112917210997)
        ·
          refine ⟨5107894151857885585988531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54484204286484112917210997 5107894151857885585988531)
          ·
            refine ⟨7661841227786828378982797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5107894151857885585988531 7661841227786828378982797)
            ·
              refine ⟨2873190460420060642118549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7661841227786828378982797 2873190460420060642118549)
              ·
                refine ⟨134680802832190342599307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2873190460420060642118549 134680802832190342599307)
                ·
                  rfl

theorem cell21_1770457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 6].length) (baseStart_1770457 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1770457 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1770457 prefixEnd_1770457 := by exact prefixLift 1770457
  have htrace : WordTrace (prefixWord ++ tailWord_1770457) baseStart_1770457 baseEnd_1770457 := by
    simpa [prefixWord, tailWord_1770457, baseEnd_1770457] using wordTrace_append hprefix tailTrace_1770457
  have hstable : (prefixWord ++ tailWord_1770457).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770457).length < 2 ^ (prefixWord ++ tailWord_1770457).sum := by decide
  have hdescent : baseEnd_1770457 < baseStart_1770457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770474 : List Nat := [3, 1, 3, 1, 2, 3, 3, 5]
def baseStart_1770474 : Nat := 118140960795 + 1770474 * 2 ^ 59
def prefixEnd_1770474 : Nat := 4983230072969 + 3 ^ 40 * 1770474 * 2
def baseEnd_1770474 : Nat := 134682096042727592004851

theorem tailTrace_1770474 : CollatzResearch.WordTrace tailWord_1770474 prefixEnd_1770474 134682096042727592004851 := by
  unfold tailWord_1770474
  simp only [CollatzResearch.WordTrace]
  refine ⟨16143622946970636432793619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43049661191921697154116317 16143622946970636432793619)
  ·
    refine ⟨24215434420455954649190429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16143622946970636432793619 24215434420455954649190429)
    ·
      refine ⟨9080787907670982993446411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24215434420455954649190429 9080787907670982993446411)
      ·
        refine ⟨13621181861506474490169617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9080787907670982993446411 13621181861506474490169617)
        ·
          refine ⟨10215886396129855867627213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13621181861506474490169617 10215886396129855867627213)
          ·
            refine ⟨3830957398548695950360205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10215886396129855867627213 3830957398548695950360205)
            ·
              refine ⟨1436609024455760981385077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3830957398548695950360205 1436609024455760981385077)
              ·
                refine ⟨134682096042727592004851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1436609024455760981385077 134682096042727592004851)
                ·
                  rfl

theorem cell21_1770474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 3, 5].length) (baseStart_1770474 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1770474 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1770474 prefixEnd_1770474 := by exact prefixLift 1770474
  have htrace : WordTrace (prefixWord ++ tailWord_1770474) baseStart_1770474 baseEnd_1770474 := by
    simpa [prefixWord, tailWord_1770474, baseEnd_1770474] using wordTrace_append hprefix tailTrace_1770474
  have hstable : (prefixWord ++ tailWord_1770474).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770474).length < 2 ^ (prefixWord ++ tailWord_1770474).sum := by decide
  have hdescent : baseEnd_1770474 < baseStart_1770474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770494 : List Nat := [4, 2, 2, 2, 3, 1, 1, 2, 4]
def baseStart_1770494 : Nat := 118140960795 + 1770494 * 2 ^ 59
def prefixEnd_1770494 : Nat := 4983230072969 + 3 ^ 40 * 1770494 * 2
def baseEnd_1770494 : Nat := 404050852400667185681179

theorem tailTrace_1770494 : CollatzResearch.WordTrace tailWord_1770494 prefixEnd_1770494 404050852400667185681179 := by
  unfold tailWord_1770494
  simp only [CollatzResearch.WordTrace]
  refine ⟨8071902655976261143362817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43050147498540059431268357 8071902655976261143362817)
  ·
    refine ⟨6053926991982195857522113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8071902655976261143362817 6053926991982195857522113)
    ·
      refine ⟨4540445243986646893141585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6053926991982195857522113 4540445243986646893141585)
      ·
        refine ⟨3405333932989985169856189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4540445243986646893141585 3405333932989985169856189)
        ·
          refine ⟨1277000224871244438696071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3405333932989985169856189 1277000224871244438696071)
          ·
            refine ⟨1915500337306866658044107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1277000224871244438696071 1915500337306866658044107)
            ·
              refine ⟨2873250505960299987066161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1915500337306866658044107 2873250505960299987066161)
              ·
                refine ⟨2154937879470224990299621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2873250505960299987066161 2154937879470224990299621)
                ·
                  refine ⟨404050852400667185681179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2154937879470224990299621 404050852400667185681179)
                  ·
                    rfl

theorem cell21_1770494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 2, 4].length) (baseStart_1770494 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1770494 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1770494 prefixEnd_1770494 := by exact prefixLift 1770494
  have htrace : WordTrace (prefixWord ++ tailWord_1770494) baseStart_1770494 baseEnd_1770494 := by
    simpa [prefixWord, tailWord_1770494, baseEnd_1770494] using wordTrace_append hprefix tailTrace_1770494
  have hstable : (prefixWord ++ tailWord_1770494).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770494).length < 2 ^ (prefixWord ++ tailWord_1770494).sum := by decide
  have hdescent : baseEnd_1770494 < baseStart_1770494 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770550 : List Nat := [5, 1, 2, 1, 1, 4, 7]
def baseStart_1770550 : Nat := 118140960795 + 1770550 * 2 ^ 59
def prefixEnd_1770550 : Nat := 4983230072969 + 3 ^ 40 * 1770550 * 2
def baseEnd_1770550 : Nat := 44895959151513725860859

theorem tailTrace_1770550 : CollatzResearch.WordTrace tailWord_1770550 prefixEnd_1770550 44895959151513725860859 := by
  unfold tailWord_1770550
  simp only [CollatzResearch.WordTrace]
  refine ⟨4036078983475450669433819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43051509157071473807294069 4036078983475450669433819)
  ·
    refine ⟨6054118475213176004150729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4036078983475450669433819 6054118475213176004150729)
    ·
      refine ⟨4540588856409882003113047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6054118475213176004150729 4540588856409882003113047)
      ·
        refine ⟨6810883284614823004669571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4540588856409882003113047 6810883284614823004669571)
        ·
          refine ⟨10216324926922234507004357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6810883284614823004669571 10216324926922234507004357)
          ·
            refine ⟨1915560923797918970063317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10216324926922234507004357 1915560923797918970063317)
            ·
              refine ⟨44895959151513725860859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1915560923797918970063317 44895959151513725860859)
              ·
                rfl

theorem cell21_1770550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 7].length) (baseStart_1770550 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1770550 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1770550 prefixEnd_1770550 := by exact prefixLift 1770550
  have htrace : WordTrace (prefixWord ++ tailWord_1770550) baseStart_1770550 baseEnd_1770550 := by
    simpa [prefixWord, tailWord_1770550, baseEnd_1770550] using wordTrace_append hprefix tailTrace_1770550
  have hstable : (prefixWord ++ tailWord_1770550).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770550).length < 2 ^ (prefixWord ++ tailWord_1770550).sum := by decide
  have hdescent : baseEnd_1770550 < baseStart_1770550 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770592 : List Nat := [2, 1, 1, 3, 2, 2, 1, 9]
def baseStart_1770592 : Nat := 118140960795 + 1770592 * 2 ^ 59
def prefixEnd_1770592 : Nat := 4983230072969 + 3 ^ 40 * 1770592 * 2
def baseEnd_1770592 : Nat := 134691072445280264349215

theorem tailTrace_1770592 : CollatzResearch.WordTrace tailWord_1770592 prefixEnd_1770592 134691072445280264349215 := by
  unfold tailWord_1770592
  simp only [CollatzResearch.WordTrace]
  refine ⟨32289397800727525941985015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43052530400970034589313353 32289397800727525941985015)
  ·
    refine ⟨48434096701091288912977523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32289397800727525941985015 48434096701091288912977523)
    ·
      refine ⟨72651145051636933369466285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48434096701091288912977523 72651145051636933369466285)
      ·
        refine ⟨27244179394363850013549857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72651145051636933369466285 27244179394363850013549857)
        ·
          refine ⟨20433134545772887510162393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27244179394363850013549857 20433134545772887510162393)
          ·
            refine ⟨15324850909329665632621795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20433134545772887510162393 15324850909329665632621795)
            ·
              refine ⟨22987276363994498448932693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15324850909329665632621795 22987276363994498448932693)
              ·
                refine ⟨134691072445280264349215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22987276363994498448932693 134691072445280264349215)
                ·
                  rfl

theorem cell21_1770592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 9].length) (baseStart_1770592 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1770592 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1770592 prefixEnd_1770592 := by exact prefixLift 1770592
  have htrace : WordTrace (prefixWord ++ tailWord_1770592) baseStart_1770592 baseEnd_1770592 := by
    simpa [prefixWord, tailWord_1770592, baseEnd_1770592] using wordTrace_append hprefix tailTrace_1770592
  have hstable : (prefixWord ++ tailWord_1770592).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770592).length < 2 ^ (prefixWord ++ tailWord_1770592).sum := by decide
  have hdescent : baseEnd_1770592 < baseStart_1770592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770657 : List Nat := [1, 2, 3, 3, 1, 1, 4, 3, 3]
def baseStart_1770657 : Nat := 118140960795 + 1770657 * 2 ^ 59
def prefixEnd_1770657 : Nat := 4983230072969 + 3 ^ 40 * 1770657 * 2
def baseEnd_1770657 : Nat := 404088051221415124464179

theorem tailTrace_1770657 : CollatzResearch.WordTrace tailWord_1770657 prefixEnd_1770657 404088051221415124464179 := by
  unfold tailWord_1770657
  simp only [CollatzResearch.WordTrace]
  refine ⟨64581166346219567985086225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43054110897479711990057483 64581166346219567985086225)
  ·
    refine ⟨48435874759664675988814669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64581166346219567985086225 48435874759664675988814669)
    ·
      refine ⟨18163453034874253495805501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48435874759664675988814669 18163453034874253495805501)
      ·
        refine ⟨6811294888077845060927063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18163453034874253495805501 6811294888077845060927063)
        ·
          refine ⟨10216942332116767591390595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6811294888077845060927063 10216942332116767591390595)
          ·
            refine ⟨15325413498175151387085893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10216942332116767591390595 15325413498175151387085893)
            ·
              refine ⟨2873515030907840885078605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15325413498175151387085893 2873515030907840885078605)
              ·
                refine ⟨1077568136590440331904477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2873515030907840885078605 1077568136590440331904477)
                ·
                  refine ⟨404088051221415124464179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1077568136590440331904477 404088051221415124464179)
                  ·
                    rfl

theorem cell21_1770657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 3, 3].length) (baseStart_1770657 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1770657 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1770657 prefixEnd_1770657 := by exact prefixLift 1770657
  have htrace : WordTrace (prefixWord ++ tailWord_1770657) baseStart_1770657 baseEnd_1770657 := by
    simpa [prefixWord, tailWord_1770657, baseEnd_1770657] using wordTrace_append hprefix tailTrace_1770657
  have hstable : (prefixWord ++ tailWord_1770657).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770657).length < 2 ^ (prefixWord ++ tailWord_1770657).sum := by decide
  have hdescent : baseEnd_1770657 < baseStart_1770657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770688 : List Nat := [2, 1, 1, 2, 6, 1, 3, 1, 4]
def baseStart_1770688 : Nat := 118140960795 + 1770688 * 2 ^ 59
def prefixEnd_1770688 : Nat := 4983230072969 + 3 ^ 40 * 1770688 * 2
def baseEnd_1770688 : Nat := 404095125843765959447449

theorem tailTrace_1770688 : CollatzResearch.WordTrace tailWord_1770688 prefixEnd_1770688 404095125843765959447449 := by
  unfold tailWord_1770688
  simp only [CollatzResearch.WordTrace]
  refine ⟨32291148504553630139732359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43054864672738173519643145 32291148504553630139732359)
  ·
    refine ⟨48436722756830445209598539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32291148504553630139732359 48436722756830445209598539)
    ·
      refine ⟨72655084135245667814397809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48436722756830445209598539 72655084135245667814397809)
      ·
        refine ⟨54491313101434250860798357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72655084135245667814397809 54491313101434250860798357)
        ·
          refine ⟨2554280301629730509099923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 54491313101434250860798357 2554280301629730509099923)
          ·
            refine ⟨3831420452444595763649885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2554280301629730509099923 3831420452444595763649885)
            ·
              refine ⟨1436782669666723411368707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3831420452444595763649885 1436782669666723411368707)
              ·
                refine ⟨2155174004500085117053061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1436782669666723411368707 2155174004500085117053061)
                ·
                  refine ⟨404095125843765959447449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2155174004500085117053061 404095125843765959447449)
                  ·
                    rfl

theorem cell21_1770688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 3, 1, 4].length) (baseStart_1770688 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1770688 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1770688 prefixEnd_1770688 := by exact prefixLift 1770688
  have htrace : WordTrace (prefixWord ++ tailWord_1770688) baseStart_1770688 baseEnd_1770688 := by
    simpa [prefixWord, tailWord_1770688, baseEnd_1770688] using wordTrace_append hprefix tailTrace_1770688
  have hstable : (prefixWord ++ tailWord_1770688).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770688).length < 2 ^ (prefixWord ++ tailWord_1770688).sum := by decide
  have hdescent : baseEnd_1770688 < baseStart_1770688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770694 : List Nat := [6, 1, 2, 2, 2, 1, 2, 5]
def baseStart_1770694 : Nat := 118140960795 + 1770694 * 2 ^ 59
def prefixEnd_1770694 : Nat := 4983230072969 + 3 ^ 40 * 1770694 * 2
def baseEnd_1770694 : Nat := 134698831708503760782479

theorem tailTrace_1770694 : CollatzResearch.WordTrace tailWord_1770694 prefixEnd_1770694 134698831708503760782479 := by
  unfold tailWord_1770694
  simp only [CollatzResearch.WordTrace]
  refine ⟨2018203620221422603255723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 43055010564723682202788757 2018203620221422603255723)
  ·
    refine ⟨3027305430332133904883585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2018203620221422603255723 3027305430332133904883585)
    ·
      refine ⟨2270479072749100428662689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3027305430332133904883585 2270479072749100428662689)
      ·
        refine ⟨1702859304561825321497017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2270479072749100428662689 1702859304561825321497017)
        ·
          refine ⟨1277144478421368991122763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1702859304561825321497017 1277144478421368991122763)
          ·
            refine ⟨1915716717632053486684145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1277144478421368991122763 1915716717632053486684145)
            ·
              refine ⟨1436787538224040115013109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1915716717632053486684145 1436787538224040115013109)
              ·
                refine ⟨134698831708503760782479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1436787538224040115013109 134698831708503760782479)
                ·
                  rfl

theorem cell21_1770694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_1770694 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1770694 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1770694 prefixEnd_1770694 := by exact prefixLift 1770694
  have htrace : WordTrace (prefixWord ++ tailWord_1770694) baseStart_1770694 baseEnd_1770694 := by
    simpa [prefixWord, tailWord_1770694, baseEnd_1770694] using wordTrace_append hprefix tailTrace_1770694
  have hstable : (prefixWord ++ tailWord_1770694).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770694).length < 2 ^ (prefixWord ++ tailWord_1770694).sum := by decide
  have hdescent : baseEnd_1770694 < baseStart_1770694 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770708 : List Nat := [2, 4, 1, 4, 2, 1, 1, 3, 3]
def baseStart_1770708 : Nat := 118140960795 + 1770708 * 2 ^ 59
def prefixEnd_1770708 : Nat := 4983230072969 + 3 ^ 40 * 1770708 * 2
def baseEnd_1770708 : Nat := 404099690116250369114075

theorem tailTrace_1770708 : CollatzResearch.WordTrace tailWord_1770708 prefixEnd_1770708 404099690116250369114075 := by
  unfold tailWord_1770708
  simp only [CollatzResearch.WordTrace]
  refine ⟨32291513234517401847596389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43055350979356535796795185 32291513234517401847596389)
  ·
    refine ⟨6054658731472012846424323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32291513234517401847596389 6054658731472012846424323)
    ·
      refine ⟨9081988097208019269636485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6054658731472012846424323 9081988097208019269636485)
      ·
        refine ⟨1702872768226503613056841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9081988097208019269636485 1702872768226503613056841)
        ·
          refine ⟨1277154576169877709792631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1702872768226503613056841 1277154576169877709792631)
          ·
            refine ⟨1915731864254816564688947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1277154576169877709792631 1915731864254816564688947)
            ·
              refine ⟨2873597796382224847033421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1915731864254816564688947 2873597796382224847033421)
              ·
                refine ⟨1077599173643334317637533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2873597796382224847033421 1077599173643334317637533)
                ·
                  refine ⟨404099690116250369114075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1077599173643334317637533 404099690116250369114075)
                  ·
                    rfl

theorem cell21_1770708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 3, 3].length) (baseStart_1770708 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1770708 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1770708 prefixEnd_1770708 := by exact prefixLift 1770708
  have htrace : WordTrace (prefixWord ++ tailWord_1770708) baseStart_1770708 baseEnd_1770708 := by
    simpa [prefixWord, tailWord_1770708, baseEnd_1770708] using wordTrace_append hprefix tailTrace_1770708
  have hstable : (prefixWord ++ tailWord_1770708).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770708).length < 2 ^ (prefixWord ++ tailWord_1770708).sum := by decide
  have hdescent : baseEnd_1770708 < baseStart_1770708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770730 : List Nat := [3, 1, 3, 1, 1, 3, 2, 1, 6]
def baseStart_1770730 : Nat := 118140960795 + 1770730 * 2 ^ 59
def prefixEnd_1770730 : Nat := 4983230072969 + 3 ^ 40 * 1770730 * 2
def baseEnd_1770730 : Nat := 404104710815983219747363

theorem tailTrace_1770730 : CollatzResearch.WordTrace tailWord_1770730 prefixEnd_1770730 404104710815983219747363 := by
  unfold tailWord_1770730
  simp only [CollatzResearch.WordTrace]
  refine ⟨16145957218738775363123411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43055885916636734301662429 16145957218738775363123411)
  ·
    refine ⟨24218935828108163044685117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16145957218738775363123411 24218935828108163044685117)
    ·
      refine ⟨9082100935540561141756919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24218935828108163044685117 9082100935540561141756919)
      ·
        refine ⟨13623151403310841712635379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9082100935540561141756919 13623151403310841712635379)
        ·
          refine ⟨20434727104966262568953069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13623151403310841712635379 20434727104966262568953069)
          ·
            refine ⟨7663022664362348463357401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20434727104966262568953069 7663022664362348463357401)
            ·
              refine ⟨5747266998271761347518051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7663022664362348463357401 5747266998271761347518051)
              ·
                refine ⟨8620900497407642021277077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5747266998271761347518051 8620900497407642021277077)
                ·
                  refine ⟨404104710815983219747363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8620900497407642021277077 404104710815983219747363)
                  ·
                    rfl

theorem cell21_1770730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 1, 6].length) (baseStart_1770730 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1770730 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1770730 prefixEnd_1770730 := by exact prefixLift 1770730
  have htrace : WordTrace (prefixWord ++ tailWord_1770730) baseStart_1770730 baseEnd_1770730 := by
    simpa [prefixWord, tailWord_1770730, baseEnd_1770730] using wordTrace_append hprefix tailTrace_1770730
  have hstable : (prefixWord ++ tailWord_1770730).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770730).length < 2 ^ (prefixWord ++ tailWord_1770730).sum := by decide
  have hdescent : baseEnd_1770730 < baseStart_1770730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770733 : List Nat := [1, 5, 1, 2, 2, 3, 1, 1, 5]
def baseStart_1770733 : Nat := 118140960795 + 1770733 * 2 ^ 59
def prefixEnd_1770733 : Nat := 4983230072969 + 3 ^ 40 * 1770733 * 2
def baseEnd_1770733 : Nat := 404105395456855881197357

theorem tailTrace_1770733 : CollatzResearch.WordTrace tailWord_1770733 prefixEnd_1770733 404105395456855881197357 := by
  unfold tailWord_1770733
  simp only [CollatzResearch.WordTrace]
  refine ⟨64583938293944232964852853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43055958862629488643235235 64583938293944232964852853)
  ·
    refine ⟨6054744215057271840454955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 64583938293944232964852853 6054744215057271840454955)
    ·
      refine ⟨9082116322585907760682433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6054744215057271840454955 9082116322585907760682433)
      ·
        refine ⟨6811587241939430820511825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9082116322585907760682433 6811587241939430820511825)
        ·
          refine ⟨5108690431454573115383869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6811587241939430820511825 5108690431454573115383869)
          ·
            refine ⟨1915758911795464918268951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5108690431454573115383869 1915758911795464918268951)
            ·
              refine ⟨2873638367693197377403427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1915758911795464918268951 2873638367693197377403427)
              ·
                refine ⟨4310457551539796066105141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2873638367693197377403427 4310457551539796066105141)
                ·
                  refine ⟨404105395456855881197357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4310457551539796066105141 404105395456855881197357)
                  ·
                    rfl

theorem cell21_1770733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 1, 5].length) (baseStart_1770733 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1770733 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1770733 prefixEnd_1770733 := by exact prefixLift 1770733
  have htrace : WordTrace (prefixWord ++ tailWord_1770733) baseStart_1770733 baseEnd_1770733 := by
    simpa [prefixWord, tailWord_1770733, baseEnd_1770733] using wordTrace_append hprefix tailTrace_1770733
  have hstable : (prefixWord ++ tailWord_1770733).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770733).length < 2 ^ (prefixWord ++ tailWord_1770733).sum := by decide
  have hdescent : baseEnd_1770733 < baseStart_1770733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770851 : List Nat := [1, 1, 1, 5, 2, 2, 1, 3, 5]
def baseStart_1770851 : Nat := 118140960795 + 1770851 * 2 ^ 59
def prefixEnd_1770851 : Nat := 4983230072969 + 3 ^ 40 * 1770851 * 2
def baseEnd_1770851 : Nat := 404132324664513898230449

theorem tailTrace_1770851 : CollatzResearch.WordTrace tailWord_1770851 prefixEnd_1770851 404132324664513898230449 := by
  unfold tailWord_1770851
  simp only [CollatzResearch.WordTrace]
  refine ⟨64588242107516739117648407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43058828071677826078432271 64588242107516739117648407)
  ·
    refine ⟨96882363161275108676472611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64588242107516739117648407 96882363161275108676472611)
    ·
      refine ⟨145323544741912663014708917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96882363161275108676472611 145323544741912663014708917)
      ·
        refine ⟨13624082319554312157628961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 145323544741912663014708917 13624082319554312157628961)
        ·
          refine ⟨10218061739665734118221721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13624082319554312157628961 10218061739665734118221721)
          ·
            refine ⟨7663546304749300588666291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10218061739665734118221721 7663546304749300588666291)
            ·
              refine ⟨11495319457123950882999437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7663546304749300588666291 11495319457123950882999437)
              ·
                refine ⟨4310744796421481581124789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11495319457123950882999437 4310744796421481581124789)
                ·
                  refine ⟨404132324664513898230449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4310744796421481581124789 404132324664513898230449)
                  ·
                    rfl

theorem cell21_1770851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 3, 5].length) (baseStart_1770851 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1770851 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1770851 prefixEnd_1770851 := by exact prefixLift 1770851
  have htrace : WordTrace (prefixWord ++ tailWord_1770851) baseStart_1770851 baseEnd_1770851 := by
    simpa [prefixWord, tailWord_1770851, baseEnd_1770851] using wordTrace_append hprefix tailTrace_1770851
  have hstable : (prefixWord ++ tailWord_1770851).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770851).length < 2 ^ (prefixWord ++ tailWord_1770851).sum := by decide
  have hdescent : baseEnd_1770851 < baseStart_1770851 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770958 : List Nat := [4, 1, 1, 1, 2, 1, 3, 4, 4]
def baseStart_1770958 : Nat := 118140960795 + 1770958 * 2 ^ 59
def prefixEnd_1770958 : Nat := 4983230072969 + 3 ^ 40 * 1770958 * 2
def baseEnd_1770958 : Nat := 404156743522305489946897

theorem tailTrace_1770958 : CollatzResearch.WordTrace tailWord_1770958 prefixEnd_1770958 404156743522305489946897 := by
  unfold tailWord_1770958
  simp only [CollatzResearch.WordTrace]
  refine ⟨8074018089766137048974191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43061429812086064261195685 8074018089766137048974191)
  ·
    refine ⟨12111027134649205573461287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8074018089766137048974191 12111027134649205573461287)
    ·
      refine ⟨18166540701973808360191931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12111027134649205573461287 18166540701973808360191931)
      ·
        refine ⟨27249811052960712540287897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18166540701973808360191931 27249811052960712540287897)
        ·
          refine ⟨20437358289720534405215923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27249811052960712540287897 20437358289720534405215923)
          ·
            refine ⟨30656037434580801607823885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20437358289720534405215923 30656037434580801607823885)
            ·
              refine ⟨11496014037967800602933957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30656037434580801607823885 11496014037967800602933957)
              ·
                refine ⟨2155502632118962613050117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11496014037967800602933957 2155502632118962613050117)
                ·
                  refine ⟨404156743522305489946897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2155502632118962613050117 404156743522305489946897)
                  ·
                    rfl

theorem cell21_1770958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 4, 4].length) (baseStart_1770958 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1770958 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1770958 prefixEnd_1770958 := by exact prefixLift 1770958
  have htrace : WordTrace (prefixWord ++ tailWord_1770958) baseStart_1770958 baseEnd_1770958 := by
    simpa [prefixWord, tailWord_1770958, baseEnd_1770958] using wordTrace_append hprefix tailTrace_1770958
  have hstable : (prefixWord ++ tailWord_1770958).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770958).length < 2 ^ (prefixWord ++ tailWord_1770958).sum := by decide
  have hdescent : baseEnd_1770958 < baseStart_1770958 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771006 : List Nat := [4, 2, 2, 3, 1, 1, 8]
def baseStart_1771006 : Nat := 118140960795 + 1771006 * 2 ^ 59
def prefixEnd_1771006 : Nat := 4983230072969 + 3 ^ 40 * 1771006 * 2
def baseEnd_1771006 : Nat := 44907521975140897016311

theorem tailTrace_1771006 : CollatzResearch.WordTrace tailWord_1771006 prefixEnd_1771006 44907521975140897016311 := by
  unfold tailWord_1771006
  simp only [CollatzResearch.WordTrace]
  refine ⟨8074236927744400073692609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43062596947970133726360581 8074236927744400073692609)
  ·
    refine ⟨6055677695808300055269457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8074236927744400073692609 6055677695808300055269457)
    ·
      refine ⟨4541758271856225041452093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6055677695808300055269457 4541758271856225041452093)
      ·
        refine ⟨1703159351946084390544535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4541758271856225041452093 1703159351946084390544535)
        ·
          refine ⟨2554739027919126585816803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1703159351946084390544535 2554739027919126585816803)
          ·
            refine ⟨3832108541878689878725205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2554739027919126585816803 3832108541878689878725205)
            ·
              refine ⟨44907521975140897016311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3832108541878689878725205 44907521975140897016311)
              ·
                rfl

theorem cell21_1771006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 8].length) (baseStart_1771006 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1771006 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1771006 prefixEnd_1771006 := by exact prefixLift 1771006
  have htrace : WordTrace (prefixWord ++ tailWord_1771006) baseStart_1771006 baseEnd_1771006 := by
    simpa [prefixWord, tailWord_1771006, baseEnd_1771006] using wordTrace_append hprefix tailTrace_1771006
  have hstable : (prefixWord ++ tailWord_1771006).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771006).length < 2 ^ (prefixWord ++ tailWord_1771006).sum := by decide
  have hdescent : baseEnd_1771006 < baseStart_1771006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771017 : List Nat := [1, 2, 1, 1, 3, 1, 5, 1, 6]
def baseStart_1771017 : Nat := 118140960795 + 1771017 * 2 ^ 59
def prefixEnd_1771017 : Nat := 4983230072969 + 3 ^ 40 * 1771017 * 2
def baseEnd_1771017 : Nat := 404170208126134498463443

theorem tailTrace_1771017 : CollatzResearch.WordTrace tailWord_1771017 prefixEnd_1771017 404170208126134498463443 := by
  unfold tailWord_1771017
  simp only [CollatzResearch.WordTrace]
  refine ⟨64594296624915349468191305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43062864416610232978794203 64594296624915349468191305)
  ·
    refine ⟨48445722468686512101143479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64594296624915349468191305 48445722468686512101143479)
    ·
      refine ⟨72668583703029768151715219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48445722468686512101143479 72668583703029768151715219)
      ·
        refine ⟨109002875554544652227572829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72668583703029768151715219 109002875554544652227572829)
        ·
          refine ⟨40876078332954244585339811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109002875554544652227572829 40876078332954244585339811)
          ·
            refine ⟨61314117499431366878009717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40876078332954244585339811 61314117499431366878009717)
            ·
              refine ⟨5748198515571690644813411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61314117499431366878009717 5748198515571690644813411)
              ·
                refine ⟨8622297773357535967220117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5748198515571690644813411 8622297773357535967220117)
                ·
                  refine ⟨404170208126134498463443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8622297773357535967220117 404170208126134498463443)
                  ·
                    rfl

theorem cell21_1771017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 1, 6].length) (baseStart_1771017 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1771017 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1771017 prefixEnd_1771017 := by exact prefixLift 1771017
  have htrace : WordTrace (prefixWord ++ tailWord_1771017) baseStart_1771017 baseEnd_1771017 := by
    simpa [prefixWord, tailWord_1771017, baseEnd_1771017] using wordTrace_append hprefix tailTrace_1771017
  have hstable : (prefixWord ++ tailWord_1771017).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771017).length < 2 ^ (prefixWord ++ tailWord_1771017).sum := by decide
  have hdescent : baseEnd_1771017 < baseStart_1771017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771020 : List Nat := [2, 2, 1, 2, 5, 1, 2, 1, 5]
def baseStart_1771020 : Nat := 118140960795 + 1771020 * 2 ^ 59
def prefixEnd_1771020 : Nat := 4983230072969 + 3 ^ 40 * 1771020 * 2
def baseEnd_1771020 : Nat := 404170892767007159913437

theorem tailTrace_1771020 : CollatzResearch.WordTrace tailWord_1771020 prefixEnd_1771020 404170892767007159913437 := by
  unfold tailWord_1771020
  simp only [CollatzResearch.WordTrace]
  refine ⟨32297203021952240490275257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43062937362602987320367009 32297203021952240490275257)
  ·
    refine ⟨24222902266464180367706443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32297203021952240490275257 24222902266464180367706443)
    ·
      refine ⟨36334353399696270551559665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24222902266464180367706443 36334353399696270551559665)
      ·
        refine ⟨27250765049772202913669749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36334353399696270551559665 27250765049772202913669749)
        ·
          refine ⟨2554759223416144023156539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27250765049772202913669749 2554759223416144023156539)
          ·
            refine ⟨3832138835124216034734809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2554759223416144023156539 3832138835124216034734809)
            ·
              refine ⟨2874104126343162026051107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3832138835124216034734809 2874104126343162026051107)
              ·
                refine ⟨4311156189514743039076661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2874104126343162026051107 4311156189514743039076661)
                ·
                  refine ⟨404170892767007159913437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4311156189514743039076661 404170892767007159913437)
                  ·
                    rfl

theorem cell21_1771020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 1, 5].length) (baseStart_1771020 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1771020 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1771020 prefixEnd_1771020 := by exact prefixLift 1771020
  have htrace : WordTrace (prefixWord ++ tailWord_1771020) baseStart_1771020 baseEnd_1771020 := by
    simpa [prefixWord, tailWord_1771020, baseEnd_1771020] using wordTrace_append hprefix tailTrace_1771020
  have hstable : (prefixWord ++ tailWord_1771020).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771020).length < 2 ^ (prefixWord ++ tailWord_1771020).sum := by decide
  have hdescent : baseEnd_1771020 < baseStart_1771020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771054 : List Nat := [4, 1, 3, 1, 2, 3, 1, 3, 3]
def baseStart_1771054 : Nat := 118140960795 + 1771054 * 2 ^ 59
def prefixEnd_1771054 : Nat := 4983230072969 + 3 ^ 40 * 1771054 * 2
def baseEnd_1771054 : Nat := 404178652030230656346701

theorem tailTrace_1771054 : CollatzResearch.WordTrace tailWord_1771054 prefixEnd_1771054 404178652030230656346701 := by
  unfold tailWord_1771054
  simp only [CollatzResearch.WordTrace]
  refine ⟨8074455765722663098411027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43063764083854203191525477 8074455765722663098411027)
  ·
    refine ⟨12111683648583994647616541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8074455765722663098411027 12111683648583994647616541)
    ·
      refine ⟨4541881368218997992856203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12111683648583994647616541 4541881368218997992856203)
      ·
        refine ⟨6812822052328496989284305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4541881368218997992856203 6812822052328496989284305)
        ·
          refine ⟨5109616539246372741963229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6812822052328496989284305 5109616539246372741963229)
          ·
            refine ⟨1916106202217389778236211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5109616539246372741963229 1916106202217389778236211)
            ·
              refine ⟨2874159303326084667354317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1916106202217389778236211 2874159303326084667354317)
              ·
                refine ⟨1077809738747281750257869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2874159303326084667354317 1077809738747281750257869)
                ·
                  refine ⟨404178652030230656346701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1077809738747281750257869 404178652030230656346701)
                  ·
                    rfl

theorem cell21_1771054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 3, 3].length) (baseStart_1771054 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1771054 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1771054 prefixEnd_1771054 := by exact prefixLift 1771054
  have htrace : WordTrace (prefixWord ++ tailWord_1771054) baseStart_1771054 baseEnd_1771054 := by
    simpa [prefixWord, tailWord_1771054, baseEnd_1771054] using wordTrace_append hprefix tailTrace_1771054
  have hstable : (prefixWord ++ tailWord_1771054).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771054).length < 2 ^ (prefixWord ++ tailWord_1771054).sum := by decide
  have hdescent : baseEnd_1771054 < baseStart_1771054 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771085 : List Nat := [1, 6, 1, 1, 3, 2, 2, 1, 4]
def baseStart_1771085 : Nat := 118140960795 + 1771085 * 2 ^ 59
def prefixEnd_1771085 : Nat := 4983230072969 + 3 ^ 40 * 1771085 * 2
def baseEnd_1771085 : Nat := 404185726652581491329971

theorem tailTrace_1771085 : CollatzResearch.WordTrace tailWord_1771085 prefixEnd_1771085 404185726652581491329971 := by
  unfold tailWord_1771085
  simp only [CollatzResearch.WordTrace]
  refine ⟨64596776788668997081666709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43064517859112664721111139 64596776788668997081666709)
  ·
    refine ⟨3027973911968859238203127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 64596776788668997081666709 3027973911968859238203127)
    ·
      refine ⟨4541960867953288857304691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3027973911968859238203127 4541960867953288857304691)
      ·
        refine ⟨6812941301929933285957037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4541960867953288857304691 6812941301929933285957037)
        ·
          refine ⟨2554852988223724982233889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6812941301929933285957037 2554852988223724982233889)
          ·
            refine ⟨1916139741167793736675417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2554852988223724982233889 1916139741167793736675417)
            ·
              refine ⟨1437104805875845302506563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1916139741167793736675417 1437104805875845302506563)
              ·
                refine ⟨2155657208813767953759845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1437104805875845302506563 2155657208813767953759845)
                ·
                  refine ⟨404185726652581491329971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2155657208813767953759845 404185726652581491329971)
                  ·
                    rfl

theorem cell21_1771085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_1771085 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1771085 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1771085 prefixEnd_1771085 := by exact prefixLift 1771085
  have htrace : WordTrace (prefixWord ++ tailWord_1771085) baseStart_1771085 baseEnd_1771085 := by
    simpa [prefixWord, tailWord_1771085, baseEnd_1771085] using wordTrace_append hprefix tailTrace_1771085
  have hstable : (prefixWord ++ tailWord_1771085).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771085).length < 2 ^ (prefixWord ++ tailWord_1771085).sum := by decide
  have hdescent : baseEnd_1771085 < baseStart_1771085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771172 : List Nat := [2, 3, 1, 2, 2, 2, 1, 5, 3]
def baseStart_1771172 : Nat := 118140960795 + 1771172 * 2 ^ 59
def prefixEnd_1771172 : Nat := 4983230072969 + 3 ^ 40 * 1771172 * 2
def baseEnd_1771172 : Nat := 404205581237888673379793

theorem tailTrace_1771172 : CollatzResearch.WordTrace tailWord_1771172 prefixEnd_1771172 404205581237888673379793 := by
  unfold tailWord_1771172
  simp only [CollatzResearch.WordTrace]
  refine ⟨32299974969676905470041885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43066633292902540626722513 32299974969676905470041885)
  ·
    refine ⟨12112490613628839551265707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32299974969676905470041885 12112490613628839551265707)
    ·
      refine ⟨18168735920443259326898561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12112490613628839551265707 18168735920443259326898561)
      ·
        refine ⟨13626551940332444495173921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18168735920443259326898561 13626551940332444495173921)
        ·
          refine ⟨10219913955249333371380441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13626551940332444495173921 10219913955249333371380441)
          ·
            refine ⟨7664935466437000028535331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10219913955249333371380441 7664935466437000028535331)
            ·
              refine ⟨11497403199655500042802997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7664935466437000028535331 11497403199655500042802997)
              ·
                refine ⟨1077881549967703129012781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11497403199655500042802997 1077881549967703129012781)
                ·
                  refine ⟨404205581237888673379793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1077881549967703129012781 404205581237888673379793)
                  ·
                    rfl

theorem cell21_1771172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 5, 3].length) (baseStart_1771172 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1771172 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1771172 prefixEnd_1771172 := by exact prefixLift 1771172
  have htrace : WordTrace (prefixWord ++ tailWord_1771172) baseStart_1771172 baseEnd_1771172 := by
    simpa [prefixWord, tailWord_1771172, baseEnd_1771172] using wordTrace_append hprefix tailTrace_1771172
  have hstable : (prefixWord ++ tailWord_1771172).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771172).length < 2 ^ (prefixWord ++ tailWord_1771172).sum := by decide
  have hdescent : baseEnd_1771172 < baseStart_1771172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771183 : List Nat := [1, 1, 2, 1, 2, 4, 10]
def baseStart_1771183 : Nat := 118140960795 + 1771183 * 2 ^ 59
def prefixEnd_1771183 : Nat := 4983230072969 + 3 ^ 40 * 1771183 * 2
def baseEnd_1771183 : Nat := 44912010176417233188493

theorem tailTrace_1771183 : CollatzResearch.WordTrace tailWord_1771183 prefixEnd_1771183 44912010176417233188493 := by
  unfold tailWord_1771183
  simp only [CollatzResearch.WordTrace]
  refine ⟨64600351142313959818734203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43066900761542639879156135 64600351142313959818734203)
  ·
    refine ⟨96900526713470939728101305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64600351142313959818734203 96900526713470939728101305)
    ·
      refine ⟨72675395035103204796075979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96900526713470939728101305 72675395035103204796075979)
      ·
        refine ⟨109013092552654807194113969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72675395035103204796075979 109013092552654807194113969)
        ·
          refine ⟨81759819414491105395585477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109013092552654807194113969 81759819414491105395585477)
          ·
            refine ⟨15329966140217082261672277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81759819414491105395585477 15329966140217082261672277)
            ·
              refine ⟨44912010176417233188493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15329966140217082261672277 44912010176417233188493)
              ·
                rfl

theorem cell21_1771183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 10].length) (baseStart_1771183 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1771183 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1771183 prefixEnd_1771183 := by exact prefixLift 1771183
  have htrace : WordTrace (prefixWord ++ tailWord_1771183) baseStart_1771183 baseEnd_1771183 := by
    simpa [prefixWord, tailWord_1771183, baseEnd_1771183] using wordTrace_append hprefix tailTrace_1771183
  have hstable : (prefixWord ++ tailWord_1771183).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771183).length < 2 ^ (prefixWord ++ tailWord_1771183).sum := by decide
  have hdescent : baseEnd_1771183 < baseStart_1771183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771186 : List Nat := [3, 2, 1, 1, 1, 2, 5, 2, 4]
def baseStart_1771186 : Nat := 118140960795 + 1771186 * 2 ^ 59
def prefixEnd_1771186 : Nat := 4983230072969 + 3 ^ 40 * 1771186 * 2
def baseEnd_1771186 : Nat := 404208776228627760146431

theorem tailTrace_1771186 : CollatzResearch.WordTrace tailWord_1771186 prefixEnd_1771186 404208776228627760146431 := by
  unfold tailWord_1771186
  simp only [CollatzResearch.WordTrace]
  refine ⟨16150115140325772832773353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43066973707535394220728941 16150115140325772832773353)
  ·
    refine ⟨12112586355244329624580015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16150115140325772832773353 12112586355244329624580015)
    ·
      refine ⟨18168879532866494436870023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12112586355244329624580015 18168879532866494436870023)
      ·
        refine ⟨27253319299299741655305035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18168879532866494436870023 27253319299299741655305035)
        ·
          refine ⟨40879978948949612482957553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27253319299299741655305035 40879978948949612482957553)
          ·
            refine ⟨30659984211712209362218165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40879978948949612482957553 30659984211712209362218165)
            ·
              refine ⟨2874373519848019627707953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30659984211712209362218165 2874373519848019627707953)
              ·
                refine ⟨2155780139886014720780965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2874373519848019627707953 2155780139886014720780965)
                ·
                  refine ⟨404208776228627760146431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2155780139886014720780965 404208776228627760146431)
                  ·
                    rfl

theorem cell21_1771186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 2, 4].length) (baseStart_1771186 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1771186 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1771186 prefixEnd_1771186 := by exact prefixLift 1771186
  have htrace : WordTrace (prefixWord ++ tailWord_1771186) baseStart_1771186 baseEnd_1771186 := by
    simpa [prefixWord, tailWord_1771186, baseEnd_1771186] using wordTrace_append hprefix tailTrace_1771186
  have hstable : (prefixWord ++ tailWord_1771186).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771186).length < 2 ^ (prefixWord ++ tailWord_1771186).sum := by decide
  have hdescent : baseEnd_1771186 < baseStart_1771186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771217 : List Nat := [1, 2, 2, 1, 2, 6, 2, 5]
def baseStart_1771217 : Nat := 118140960795 + 1771217 * 2 ^ 59
def prefixEnd_1771217 : Nat := 4983230072969 + 3 ^ 40 * 1771217 * 2
def baseEnd_1771217 : Nat := 134738616950326198376567

theorem tailTrace_1771217 : CollatzResearch.WordTrace tailWord_1771217 prefixEnd_1771217 134738616950326198376567 := by
  unfold tailWord_1771217
  simp only [CollatzResearch.WordTrace]
  refine ⟨64601591224190783625471905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43067727482793855750314603 64601591224190783625471905)
  ·
    refine ⟨48451193418143087719103929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64601591224190783625471905 48451193418143087719103929)
    ·
      refine ⟨36338395063607315789327947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48451193418143087719103929 36338395063607315789327947)
      ·
        refine ⟨54507592595410973683991921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36338395063607315789327947 54507592595410973683991921)
        ·
          refine ⟨40880694446558230262993941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54507592595410973683991921 40880694446558230262993941)
          ·
            refine ⟨1916282552182417043577841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 40880694446558230262993941 1916282552182417043577841)
            ·
              refine ⟨1437211914136812782683381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1916282552182417043577841 1437211914136812782683381)
              ·
                refine ⟨134738616950326198376567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1437211914136812782683381 134738616950326198376567)
                ·
                  rfl

theorem cell21_1771217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 2, 5].length) (baseStart_1771217 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1771217 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1771217 prefixEnd_1771217 := by exact prefixLift 1771217
  have htrace : WordTrace (prefixWord ++ tailWord_1771217) baseStart_1771217 baseEnd_1771217 := by
    simpa [prefixWord, tailWord_1771217, baseEnd_1771217] using wordTrace_append hprefix tailTrace_1771217
  have hstable : (prefixWord ++ tailWord_1771217).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771217).length < 2 ^ (prefixWord ++ tailWord_1771217).sum := by decide
  have hdescent : baseEnd_1771217 < baseStart_1771217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771310 : List Nat := [4, 1, 3, 2, 2, 2, 1, 6]
def baseStart_1771310 : Nat := 118140960795 + 1771310 * 2 ^ 59
def prefixEnd_1771310 : Nat := 4983230072969 + 3 ^ 40 * 1771310 * 2
def baseEnd_1771310 : Nat := 134745691572677033359837

theorem tailTrace_1771310 : CollatzResearch.WordTrace tailWord_1771310 prefixEnd_1771310 134745691572677033359837 := by
  unfold tailWord_1771310
  simp only [CollatzResearch.WordTrace]
  refine ⟨8075622901606732563575923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43069988808569240339071589 8075622901606732563575923)
  ·
    refine ⟨12113434352410098845363885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8075622901606732563575923 12113434352410098845363885)
    ·
      refine ⟨4542537882153787067011457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12113434352410098845363885 4542537882153787067011457)
      ·
        refine ⟨3406903411615340300258593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4542537882153787067011457 3406903411615340300258593)
        ·
          refine ⟨2555177558711505225193945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3406903411615340300258593 2555177558711505225193945)
          ·
            refine ⟨1916383169033628918895459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2555177558711505225193945 1916383169033628918895459)
            ·
              refine ⟨2874574753550443378343189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1916383169033628918895459 2874574753550443378343189)
              ·
                refine ⟨134745691572677033359837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2874574753550443378343189 134745691572677033359837)
                ·
                  rfl

theorem cell21_1771310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 6].length) (baseStart_1771310 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1771310 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1771310 prefixEnd_1771310 := by exact prefixLift 1771310
  have htrace : WordTrace (prefixWord ++ tailWord_1771310) baseStart_1771310 baseEnd_1771310 := by
    simpa [prefixWord, tailWord_1771310, baseEnd_1771310] using wordTrace_append hprefix tailTrace_1771310
  have hstable : (prefixWord ++ tailWord_1771310).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771310).length < 2 ^ (prefixWord ++ tailWord_1771310).sum := by decide
  have hdescent : baseEnd_1771310 < baseStart_1771310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771335 : List Nat := [1, 1, 4, 1, 2, 1, 2, 9]
def baseStart_1771335 : Nat := 118140960795 + 1771335 * 2 ^ 59
def prefixEnd_1771335 : Nat := 4983230072969 + 3 ^ 40 * 1771335 * 2
def baseEnd_1771335 : Nat := 134747593352878870720931

theorem tailTrace_1771335 : CollatzResearch.WordTrace tailWord_1771335 prefixEnd_1771335 134747593352878870720931 := by
  unfold tailWord_1771335
  simp only [CollatzResearch.WordTrace]
  refine ⟨64605895037763289778267459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43070596691842193185511639 64605895037763289778267459)
  ·
    refine ⟨96908842556644934667401189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64605895037763289778267459 96908842556644934667401189)
    ·
      refine ⟨18170407979370925250137723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96908842556644934667401189 18170407979370925250137723)
      ·
        refine ⟨27255611969056387875206585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18170407979370925250137723 27255611969056387875206585)
        ·
          refine ⟨20441708976792290906404939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27255611969056387875206585 20441708976792290906404939)
          ·
            refine ⟨30662563465188436359607409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20441708976792290906404939 30662563465188436359607409)
            ·
              refine ⟨22996922598891327269705557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30662563465188436359607409 22996922598891327269705557)
              ·
                refine ⟨134747593352878870720931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22996922598891327269705557 134747593352878870720931)
                ·
                  rfl

theorem cell21_1771335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 9].length) (baseStart_1771335 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1771335 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1771335 prefixEnd_1771335 := by exact prefixLift 1771335
  have htrace : WordTrace (prefixWord ++ tailWord_1771335) baseStart_1771335 baseEnd_1771335 := by
    simpa [prefixWord, tailWord_1771335, baseEnd_1771335] using wordTrace_append hprefix tailTrace_1771335
  have hstable : (prefixWord ++ tailWord_1771335).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771335).length < 2 ^ (prefixWord ++ tailWord_1771335).sum := by decide
  have hdescent : baseEnd_1771335 < baseStart_1771335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771341 : List Nat := [1, 6, 1, 2, 1, 1, 1, 5, 3]
def baseStart_1771341 : Nat := 118140960795 + 1771341 * 2 ^ 59
def prefixEnd_1771341 : Nat := 4983230072969 + 3 ^ 40 * 1771341 * 2
def baseEnd_1771341 : Nat := 404244149340381935062781

theorem tailTrace_1771341 : CollatzResearch.WordTrace tailWord_1771341 prefixEnd_1771341 404244149340381935062781 := by
  unfold tailWord_1771341
  simp only [CollatzResearch.WordTrace]
  refine ⟨64606113875741552802985877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43070742583827701868657251 64606113875741552802985877)
  ·
    refine ⟨3028411587925385287639963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 64606113875741552802985877 3028411587925385287639963)
    ·
      refine ⟨4542617381888077931459945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3028411587925385287639963 4542617381888077931459945)
      ·
        refine ⟨3406963036416058448594959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4542617381888077931459945 3406963036416058448594959)
        ·
          refine ⟨5110444554624087672892439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3406963036416058448594959 5110444554624087672892439)
          ·
            refine ⟨7665666831936131509338659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5110444554624087672892439 7665666831936131509338659)
            ·
              refine ⟨11498500247904197264007989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7665666831936131509338659 11498500247904197264007989)
              ·
                refine ⟨1077984398241018493500749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11498500247904197264007989 1077984398241018493500749)
                ·
                  refine ⟨404244149340381935062781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1077984398241018493500749 404244149340381935062781)
                  ·
                    rfl

theorem cell21_1771341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_1771341 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1771341 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1771341 prefixEnd_1771341 := by exact prefixLift 1771341
  have htrace : WordTrace (prefixWord ++ tailWord_1771341) baseStart_1771341 baseEnd_1771341 := by
    simpa [prefixWord, tailWord_1771341, baseEnd_1771341] using wordTrace_append hprefix tailTrace_1771341
  have hstable : (prefixWord ++ tailWord_1771341).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771341).length < 2 ^ (prefixWord ++ tailWord_1771341).sum := by decide
  have hdescent : baseEnd_1771341 < baseStart_1771341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771428 : List Nat := [2, 3, 1, 2, 1, 4, 2, 6]
def baseStart_1771428 : Nat := 118140960795 + 1771428 * 2 ^ 59
def prefixEnd_1771428 : Nat := 4983230072969 + 3 ^ 40 * 1771428 * 2
def baseEnd_1771428 : Nat := 134754667975229705704201

theorem tailTrace_1771428 : CollatzResearch.WordTrace tailWord_1771428 prefixEnd_1771428 134754667975229705704201 := by
  unfold tailWord_1771428
  simp only [CollatzResearch.WordTrace]
  refine ⟨32304643513213183330701469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43072858017617577774268625 32304643513213183330701469)
  ·
    refine ⟨12114241317454943749013051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32304643513213183330701469 12114241317454943749013051)
    ·
      refine ⟨18171361976182415623519577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12114241317454943749013051 18171361976182415623519577)
      ·
        refine ⟨13628521482136811717639683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18171361976182415623519577 13628521482136811717639683)
        ·
          refine ⟨20442782223205217576459525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13628521482136811717639683 20442782223205217576459525)
          ·
            refine ⟨3833021666850978295586161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20442782223205217576459525 3833021666850978295586161)
            ·
              refine ⟨2874766250138233721689621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3833021666850978295586161 2874766250138233721689621)
              ·
                refine ⟨134754667975229705704201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2874766250138233721689621 134754667975229705704201)
                ·
                  rfl

theorem cell21_1771428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 6].length) (baseStart_1771428 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1771428 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1771428 prefixEnd_1771428 := by exact prefixLift 1771428
  have htrace : WordTrace (prefixWord ++ tailWord_1771428) baseStart_1771428 baseEnd_1771428 := by
    simpa [prefixWord, tailWord_1771428, baseEnd_1771428] using wordTrace_append hprefix tailTrace_1771428
  have hstable : (prefixWord ++ tailWord_1771428).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771428).length < 2 ^ (prefixWord ++ tailWord_1771428).sum := by decide
  have hdescent : baseEnd_1771428 < baseStart_1771428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771431 : List Nat := [1, 1, 6, 1, 2, 1, 4, 1, 4]
def baseStart_1771431 : Nat := 118140960795 + 1771431 * 2 ^ 59
def prefixEnd_1771431 : Nat := 4983230072969 + 3 ^ 40 * 1771431 * 2
def baseEnd_1771431 : Nat := 404264688566561778562597

theorem tailTrace_1771431 : CollatzResearch.WordTrace tailWord_1771431 prefixEnd_1771431 404264688566561778562597 := by
  unfold tailWord_1771431
  simp only [CollatzResearch.WordTrace]
  refine ⟨64609396445415498173762147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43072930963610332115841431 64609396445415498173762147)
  ·
    refine ⟨96914094668123247260643221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64609396445415498173762147 96914094668123247260643221)
    ·
      refine ⟨4542848187568277215342651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 96914094668123247260643221 4542848187568277215342651)
      ·
        refine ⟨6814272281352415823013977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4542848187568277215342651 6814272281352415823013977)
        ·
          refine ⟨5110704211014311867260483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6814272281352415823013977 5110704211014311867260483)
          ·
            refine ⟨7666056316521467800890725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5110704211014311867260483 7666056316521467800890725)
            ·
              refine ⟨1437385559347775212667011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7666056316521467800890725 1437385559347775212667011)
              ·
                refine ⟨2156078339021662819000517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1437385559347775212667011 2156078339021662819000517)
                ·
                  refine ⟨404264688566561778562597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2156078339021662819000517 404264688566561778562597)
                  ·
                    rfl

theorem cell21_1771431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 4, 1, 4].length) (baseStart_1771431 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1771431 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1771431 prefixEnd_1771431 := by exact prefixLift 1771431
  have htrace : WordTrace (prefixWord ++ tailWord_1771431) baseStart_1771431 baseEnd_1771431 := by
    simpa [prefixWord, tailWord_1771431, baseEnd_1771431] using wordTrace_append hprefix tailTrace_1771431
  have hstable : (prefixWord ++ tailWord_1771431).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771431).length < 2 ^ (prefixWord ++ tailWord_1771431).sum := by decide
  have hdescent : baseEnd_1771431 < baseStart_1771431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771442 : List Nat := [3, 2, 1, 1, 1, 1, 1, 6, 5]
def baseStart_1771442 : Nat := 118140960795 + 1771442 * 2 ^ 59
def prefixEnd_1771442 : Nat := 4983230072969 + 3 ^ 40 * 1771442 * 2
def baseEnd_1771442 : Nat := 404267198916428203879241

theorem tailTrace_1771442 : CollatzResearch.WordTrace tailWord_1771442 prefixEnd_1771442 404267198916428203879241 := by
  unfold tailWord_1771442
  simp only [CollatzResearch.WordTrace]
  refine ⟨16152449412093911763103145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43073198432250431368275053 16152449412093911763103145)
  ·
    refine ⟨12114337059070433822327359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16152449412093911763103145 12114337059070433822327359)
    ·
      refine ⟨18171505588605650733491039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12114337059070433822327359 18171505588605650733491039)
      ·
        refine ⟨27257258382908476100236559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18171505588605650733491039 27257258382908476100236559)
        ·
          refine ⟨40885887574362714150354839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27257258382908476100236559 40885887574362714150354839)
          ·
            refine ⟨61328831361544071225532259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40885887574362714150354839 61328831361544071225532259)
            ·
              refine ⟨91993247042316106838298389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61328831361544071225532259 91993247042316106838298389)
              ·
                refine ⟨4312183455108567508045237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 91993247042316106838298389 4312183455108567508045237)
                ·
                  refine ⟨404267198916428203879241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4312183455108567508045237 404267198916428203879241)
                  ·
                    rfl

theorem cell21_1771442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 6, 5].length) (baseStart_1771442 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1771442 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1771442 prefixEnd_1771442 := by exact prefixLift 1771442
  have htrace : WordTrace (prefixWord ++ tailWord_1771442) baseStart_1771442 baseEnd_1771442 := by
    simpa [prefixWord, tailWord_1771442, baseEnd_1771442] using wordTrace_append hprefix tailTrace_1771442
  have hstable : (prefixWord ++ tailWord_1771442).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771442).length < 2 ^ (prefixWord ++ tailWord_1771442).sum := by decide
  have hdescent : baseEnd_1771442 < baseStart_1771442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771476 : List Nat := [2, 4, 1, 2, 1, 1, 3, 4, 3]
def baseStart_1771476 : Nat := 118140960795 + 1771476 * 2 ^ 59
def prefixEnd_1771476 : Nat := 4983230072969 + 3 ^ 40 * 1771476 * 2
def baseEnd_1771476 : Nat := 404274958179651700312505

theorem tailTrace_1771476 : CollatzResearch.WordTrace tailWord_1771476 prefixEnd_1771476 404274958179651700312505 := by
  unfold tailWord_1771476
  simp only [CollatzResearch.WordTrace]
  refine ⟨32305518865126235429575141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43074025153501647239433521 32305518865126235429575141)
  ·
    refine ⟨6057284787211169143045339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32305518865126235429575141 6057284787211169143045339)
    ·
      refine ⟨9085927180816753714568009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6057284787211169143045339 9085927180816753714568009)
      ·
        refine ⟨6814445385612565285926007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9085927180816753714568009 6814445385612565285926007)
        ·
          refine ⟨10221668078418847928889011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6814445385612565285926007 10221668078418847928889011)
          ·
            refine ⟨15332502117628271893333517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10221668078418847928889011 15332502117628271893333517)
            ·
              refine ⟨5749688294110601960000069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15332502117628271893333517 5749688294110601960000069)
              ·
                refine ⟨1078066555145737867500013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5749688294110601960000069 1078066555145737867500013)
                ·
                  refine ⟨404274958179651700312505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1078066555145737867500013 404274958179651700312505)
                  ·
                    rfl

theorem cell21_1771476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 4, 3].length) (baseStart_1771476 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1771476 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1771476 prefixEnd_1771476 := by exact prefixLift 1771476
  have htrace : WordTrace (prefixWord ++ tailWord_1771476) baseStart_1771476 baseEnd_1771476 := by
    simpa [prefixWord, tailWord_1771476, baseEnd_1771476] using wordTrace_append hprefix tailTrace_1771476
  have hstable : (prefixWord ++ tailWord_1771476).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771476).length < 2 ^ (prefixWord ++ tailWord_1771476).sum := by decide
  have hdescent : baseEnd_1771476 < baseStart_1771476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771524 : List Nat := [2, 3, 2, 4, 1, 2, 1, 2, 4]
def baseStart_1771524 : Nat := 118140960795 + 1771524 * 2 ^ 59
def prefixEnd_1771524 : Nat := 4983230072969 + 3 ^ 40 * 1771524 * 2
def baseEnd_1771524 : Nat := 404285912433614283512407

theorem tailTrace_1771524 : CollatzResearch.WordTrace tailWord_1771524 prefixEnd_1771524 404285912433614283512407 := by
  unfold tailWord_1771524
  simp only [CollatzResearch.WordTrace]
  refine ⟨32306394217039287528448813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43075192289385716704598417 32306394217039287528448813)
  ·
    refine ⟨12114897831389732823168305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32306394217039287528448813 12114897831389732823168305)
    ·
      refine ⟨9086173373542299617376229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12114897831389732823168305 9086173373542299617376229)
      ·
        refine ⟨1703657507539181178258043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9086173373542299617376229 1703657507539181178258043)
        ·
          refine ⟨2555486261308771767387065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1703657507539181178258043 2555486261308771767387065)
          ·
            refine ⟨1916614695981578825540299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2555486261308771767387065 1916614695981578825540299)
            ·
              refine ⟨2874922043972368238310449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1916614695981578825540299 2874922043972368238310449)
              ·
                refine ⟨2156191532979276178732837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2874922043972368238310449 2156191532979276178732837)
                ·
                  refine ⟨404285912433614283512407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2156191532979276178732837 404285912433614283512407)
                  ·
                    rfl

theorem cell21_1771524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 2, 4].length) (baseStart_1771524 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1771524 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1771524 prefixEnd_1771524 := by exact prefixLift 1771524
  have htrace : WordTrace (prefixWord ++ tailWord_1771524) baseStart_1771524 baseEnd_1771524 := by
    simpa [prefixWord, tailWord_1771524, baseEnd_1771524] using wordTrace_append hprefix tailTrace_1771524
  have hstable : (prefixWord ++ tailWord_1771524).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771524).length < 2 ^ (prefixWord ++ tailWord_1771524).sum := by decide
  have hdescent : baseEnd_1771524 < baseStart_1771524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771645 : List Nat := [1, 4, 1, 1, 3, 4, 2, 2, 3]
def baseStart_1771645 : Nat := 118140960795 + 1771645 * 2 ^ 59
def prefixEnd_1771645 : Nat := 4983230072969 + 3 ^ 40 * 1771645 * 2
def baseEnd_1771645 : Nat := 404313526282144961995493

theorem tailTrace_1771645 : CollatzResearch.WordTrace tailWord_1771645 prefixEnd_1771645 404313526282144961995493 := by
  unfold tailWord_1771645
  simp only [CollatzResearch.WordTrace]
  refine ⟨64617201666640212722052389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43078134444426808481368259 64617201666640212722052389)
  ·
    refine ⟨12115725312495039885384823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64617201666640212722052389 12115725312495039885384823)
    ·
      refine ⟨18173587968742559828077235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12115725312495039885384823 18173587968742559828077235)
      ·
        refine ⟨27260381953113839742115853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18173587968742559828077235 27260381953113839742115853)
        ·
          refine ⟨10222643232417689903293445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27260381953113839742115853 10222643232417689903293445)
          ·
            refine ⟨1916745606078316856867521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10222643232417689903293445 1916745606078316856867521)
            ·
              refine ⟨1437559204558737642650641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1916745606078316856867521 1437559204558737642650641)
              ·
                refine ⟨1078169403419053231987981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1437559204558737642650641 1078169403419053231987981)
                ·
                  refine ⟨404313526282144961995493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1078169403419053231987981 404313526282144961995493)
                  ·
                    rfl

theorem cell21_1771645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 2, 2, 3].length) (baseStart_1771645 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1771645 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1771645 prefixEnd_1771645 := by exact prefixLift 1771645
  have htrace : WordTrace (prefixWord ++ tailWord_1771645) baseStart_1771645 baseEnd_1771645 := by
    simpa [prefixWord, tailWord_1771645, baseEnd_1771645] using wordTrace_append hprefix tailTrace_1771645
  have hstable : (prefixWord ++ tailWord_1771645).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771645).length < 2 ^ (prefixWord ++ tailWord_1771645).sum := by decide
  have hdescent : baseEnd_1771645 < baseStart_1771645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771656 : List Nat := [2, 1, 3, 4, 1, 1, 3, 6]
def baseStart_1771656 : Nat := 118140960795 + 1771656 * 2 ^ 59
def prefixEnd_1771656 : Nat := 4983230072969 + 3 ^ 40 * 1771656 * 2
def baseEnd_1771656 : Nat := 134772012210670462437379

theorem tailTrace_1771656 : CollatzResearch.WordTrace tailWord_1771656 prefixEnd_1771656 134772012210670462437379 := by
  unfold tailWord_1771656
  simp only [CollatzResearch.WordTrace]
  refine ⟨32308801434800180800351411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43078401913066907733801881 32308801434800180800351411)
  ·
    refine ⟨48463202152200271200527117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32308801434800180800351411 48463202152200271200527117)
    ·
      refine ⟨18173700807075101700197669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48463202152200271200527117 18173700807075101700197669)
      ·
        refine ⟨3407568901326581568787063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18173700807075101700197669 3407568901326581568787063)
        ·
          refine ⟨5111353351989872353180595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3407568901326581568787063 5111353351989872353180595)
          ·
            refine ⟨7667030027984808529770893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5111353351989872353180595 7667030027984808529770893)
            ·
              refine ⟨2875136260494303198664085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7667030027984808529770893 2875136260494303198664085)
              ·
                refine ⟨134772012210670462437379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2875136260494303198664085 134772012210670462437379)
                ·
                  rfl

theorem cell21_1771656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 6].length) (baseStart_1771656 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1771656 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1771656 prefixEnd_1771656 := by exact prefixLift 1771656
  have htrace : WordTrace (prefixWord ++ tailWord_1771656) baseStart_1771656 baseEnd_1771656 := by
    simpa [prefixWord, tailWord_1771656, baseEnd_1771656] using wordTrace_append hprefix tailTrace_1771656
  have hstable : (prefixWord ++ tailWord_1771656).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771656).length < 2 ^ (prefixWord ++ tailWord_1771656).sum := by decide
  have hdescent : baseEnd_1771656 < baseStart_1771656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771777 : List Nat := [1, 2, 4, 1, 1, 2, 3, 3, 4]
def baseStart_1771777 : Nat := 118140960795 + 1771777 * 2 ^ 59
def prefixEnd_1771777 : Nat := 4983230072969 + 3 ^ 40 * 1771777 * 2
def baseEnd_1771777 : Nat := 404343650480542065795223

theorem tailTrace_1771777 : CollatzResearch.WordTrace tailWord_1771777 prefixEnd_1771777 404343650480542065795223 := by
  unfold tailWord_1771777
  simp only [CollatzResearch.WordTrace]
  refine ⟨64622016102161999265857585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43081344068107999510571723 64622016102161999265857585)
  ·
    refine ⟨48466512076621499449393189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64622016102161999265857585 48466512076621499449393189)
    ·
      refine ⟨9087471014366531146761223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48466512076621499449393189 9087471014366531146761223)
      ·
        refine ⟨13631206521549796720141835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9087471014366531146761223 13631206521549796720141835)
        ·
          refine ⟨20446809782324695080212753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13631206521549796720141835 20446809782324695080212753)
          ·
            refine ⟨15335107336743521310159565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20446809782324695080212753 15335107336743521310159565)
            ·
              refine ⟨5750665251278820491309837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15335107336743521310159565 5750665251278820491309837)
              ·
                refine ⟨2156499469229557684241189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5750665251278820491309837 2156499469229557684241189)
                ·
                  refine ⟨404343650480542065795223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2156499469229557684241189 404343650480542065795223)
                  ·
                    rfl

theorem cell21_1771777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 3, 4].length) (baseStart_1771777 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1771777 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1771777 prefixEnd_1771777 := by exact prefixLift 1771777
  have htrace : WordTrace (prefixWord ++ tailWord_1771777) baseStart_1771777 baseEnd_1771777 := by
    simpa [prefixWord, tailWord_1771777, baseEnd_1771777] using wordTrace_append hprefix tailTrace_1771777
  have hstable : (prefixWord ++ tailWord_1771777).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771777).length < 2 ^ (prefixWord ++ tailWord_1771777).sum := by decide
  have hdescent : baseEnd_1771777 < baseStart_1771777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771825 : List Nat := [1, 2, 2, 3, 5, 1, 1, 6]
def baseStart_1771825 : Nat := 118140960795 + 1771825 * 2 ^ 59
def prefixEnd_1771825 : Nat := 4983230072969 + 3 ^ 40 * 1771825 * 2
def baseEnd_1771825 : Nat := 134784868244834882998375

theorem tailTrace_1771825 : CollatzResearch.WordTrace tailWord_1771825 prefixEnd_1771825 134784868244834882998375 := by
  unfold tailWord_1771825
  simp only [CollatzResearch.WordTrace]
  refine ⟨64623766805988103463604929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43082511203992068975736619 64623766805988103463604929)
  ·
    refine ⟨48467825104491077597703697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64623766805988103463604929 48467825104491077597703697)
    ·
      refine ⟨36350868828368308198277773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48467825104491077597703697 36350868828368308198277773)
      ·
        refine ⟨13631575810638115574354165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36350868828368308198277773 13631575810638115574354165)
        ·
          refine ⟨1277960232247323335095703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13631575810638115574354165 1277960232247323335095703)
          ·
            refine ⟨1916940348370985002643555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1277960232247323335095703 1916940348370985002643555)
            ·
              refine ⟨2875410522556477503965333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1916940348370985002643555 2875410522556477503965333)
              ·
                refine ⟨134784868244834882998375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2875410522556477503965333 134784868244834882998375)
                ·
                  rfl

theorem cell21_1771825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 6].length) (baseStart_1771825 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1771825 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1771825 prefixEnd_1771825 := by exact prefixLift 1771825
  have htrace : WordTrace (prefixWord ++ tailWord_1771825) baseStart_1771825 baseEnd_1771825 := by
    simpa [prefixWord, tailWord_1771825, baseEnd_1771825] using wordTrace_append hprefix tailTrace_1771825
  have hstable : (prefixWord ++ tailWord_1771825).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771825).length < 2 ^ (prefixWord ++ tailWord_1771825).sum := by decide
  have hdescent : baseEnd_1771825 < baseStart_1771825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771912 : List Nat := [2, 1, 3, 3, 1, 1, 1, 1, 8]
def baseStart_1771912 : Nat := 118140960795 + 1771912 * 2 ^ 59
def prefixEnd_1771912 : Nat := 4983230072969 + 3 ^ 40 * 1771912 * 2
def baseEnd_1771912 : Nat := 404374459319811831044947

theorem tailTrace_1771912 : CollatzResearch.WordTrace tailWord_1771912 prefixEnd_1771912 404374459319811831044947 := by
  unfold tailWord_1771912
  simp only [CollatzResearch.WordTrace]
  refine ⟨32313469978336458661010995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43084626637781944881347993 32313469978336458661010995)
  ·
    refine ⟨48470204967504687991516493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32313469978336458661010995 48470204967504687991516493)
    ·
      refine ⟨18176326862814257996818685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48470204967504687991516493 18176326862814257996818685)
      ·
        refine ⟨6816122573555346748807007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18176326862814257996818685 6816122573555346748807007)
        ·
          refine ⟨10224183860333020123210511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6816122573555346748807007 10224183860333020123210511)
          ·
            refine ⟨15336275790499530184815767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10224183860333020123210511 15336275790499530184815767)
            ·
              refine ⟨23004413685749295277223651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15336275790499530184815767 23004413685749295277223651)
              ·
                refine ⟨34506620528623942915835477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23004413685749295277223651 34506620528623942915835477)
                ·
                  refine ⟨404374459319811831044947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34506620528623942915835477 404374459319811831044947)
                  ·
                    rfl

theorem cell21_1771912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 8].length) (baseStart_1771912 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1771912 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1771912 prefixEnd_1771912 := by exact prefixLift 1771912
  have htrace : WordTrace (prefixWord ++ tailWord_1771912) baseStart_1771912 baseEnd_1771912 := by
    simpa [prefixWord, tailWord_1771912, baseEnd_1771912] using wordTrace_append hprefix tailTrace_1771912
  have hstable : (prefixWord ++ tailWord_1771912).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771912).length < 2 ^ (prefixWord ++ tailWord_1771912).sum := by decide
  have hdescent : baseEnd_1771912 < baseStart_1771912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771915 : List Nat := [1, 1, 1, 1, 4, 4, 3, 3, 3]
def baseStart_1771915 : Nat := 118140960795 + 1771915 * 2 ^ 59
def prefixEnd_1771915 : Nat := 4983230072969 + 3 ^ 40 * 1771915 * 2
def baseEnd_1771915 : Nat := 404375143960684492494941

theorem tailTrace_1771915 : CollatzResearch.WordTrace tailWord_1771915 prefixEnd_1771915 404375143960684492494941 := by
  unfold tailWord_1771915
  simp only [CollatzResearch.WordTrace]
  refine ⟨64627049375662048834381199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43084699583774699222920799 64627049375662048834381199)
  ·
    refine ⟨96940574063493073251571799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64627049375662048834381199 96940574063493073251571799)
    ·
      refine ⟨145410861095239609877357699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96940574063493073251571799 145410861095239609877357699)
      ·
        refine ⟨218116291642859414816036549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145410861095239609877357699 218116291642859414816036549)
        ·
          refine ⟨40896804683036140278006853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 218116291642859414816036549 40896804683036140278006853)
          ·
            refine ⟨7668150878069276302126285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40896804683036140278006853 7668150878069276302126285)
            ·
              refine ⟨2875556579275978613297357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7668150878069276302126285 2875556579275978613297357)
              ·
                refine ⟨1078333717228491979986509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2875556579275978613297357 1078333717228491979986509)
                ·
                  refine ⟨404375143960684492494941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1078333717228491979986509 404375143960684492494941)
                  ·
                    rfl

theorem cell21_1771915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 3, 3].length) (baseStart_1771915 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1771915 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1771915 prefixEnd_1771915 := by exact prefixLift 1771915
  have htrace : WordTrace (prefixWord ++ tailWord_1771915) baseStart_1771915 baseEnd_1771915 := by
    simpa [prefixWord, tailWord_1771915, baseEnd_1771915] using wordTrace_append hprefix tailTrace_1771915
  have hstable : (prefixWord ++ tailWord_1771915).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771915).length < 2 ^ (prefixWord ++ tailWord_1771915).sum := by decide
  have hdescent : baseEnd_1771915 < baseStart_1771915 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771943 : List Nat := [1, 1, 6, 1, 1, 2, 1, 8]
def baseStart_1771943 : Nat := 118140960795 + 1771943 * 2 ^ 59
def prefixEnd_1771943 : Nat := 4983230072969 + 3 ^ 40 * 1771943 * 2
def baseEnd_1771943 : Nat := 134793844647387555342739

theorem tailTrace_1771943 : CollatzResearch.WordTrace tailWord_1771943 prefixEnd_1771943 134793844647387555342739 := by
  unfold tailWord_1771943
  simp only [CollatzResearch.WordTrace]
  refine ⟨64628070619560609616400483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43085380413040406410933655 64628070619560609616400483)
  ·
    refine ⟨96942105929340914424600725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64628070619560609616400483 96942105929340914424600725)
    ·
      refine ⟨4544161215437855363653159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 96942105929340914424600725 4544161215437855363653159)
      ·
        refine ⟨6816241823156783045479739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4544161215437855363653159 6816241823156783045479739)
        ·
          refine ⟨10224362734735174568219609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6816241823156783045479739 10224362734735174568219609)
          ·
            refine ⟨7668272051051380926164707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10224362734735174568219609 7668272051051380926164707)
            ·
              refine ⟨11502408076577071389247061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7668272051051380926164707 11502408076577071389247061)
              ·
                refine ⟨134793844647387555342739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11502408076577071389247061 134793844647387555342739)
                ·
                  rfl

theorem cell21_1771943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 8].length) (baseStart_1771943 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1771943 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1771943 prefixEnd_1771943 := by exact prefixLift 1771943
  have htrace : WordTrace (prefixWord ++ tailWord_1771943) baseStart_1771943 baseEnd_1771943 := by
    simpa [prefixWord, tailWord_1771943, baseEnd_1771943] using wordTrace_append hprefix tailTrace_1771943
  have hstable : (prefixWord ++ tailWord_1771943).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771943).length < 2 ^ (prefixWord ++ tailWord_1771943).sum := by decide
  have hdescent : baseEnd_1771943 < baseStart_1771943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1772019 : List Nat := [1, 1, 1, 2, 2, 2, 7, 5]
def baseStart_1772019 : Nat := 118140960795 + 1772019 * 2 ^ 59
def prefixEnd_1772019 : Nat := 4983230072969 + 3 ^ 40 * 1772019 * 2
def baseEnd_1772019 : Nat := 134799626059201140920465

theorem tailTrace_1772019 : CollatzResearch.WordTrace tailWord_1772019 prefixEnd_1772019 134799626059201140920465 := by
  unfold tailWord_1772019
  simp only [CollatzResearch.WordTrace]
  refine ⟨64630842567285274596167111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43087228378190183064111407 64630842567285274596167111)
  ·
    refine ⟨96946263850927911894250667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64630842567285274596167111 96946263850927911894250667)
    ·
      refine ⟨145419395776391867841376001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96946263850927911894250667 145419395776391867841376001)
      ·
        refine ⟨109064546832293900881032001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145419395776391867841376001 109064546832293900881032001)
        ·
          refine ⟨81798410124220425660774001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109064546832293900881032001 81798410124220425660774001)
          ·
            refine ⟨61348807593165319245580501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81798410124220425660774001 61348807593165319245580501)
            ·
              refine ⟨1437862677964812169818293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 61348807593165319245580501 1437862677964812169818293)
              ·
                refine ⟨134799626059201140920465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1437862677964812169818293 134799626059201140920465)
                ·
                  rfl

theorem cell21_1772019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 7, 5].length) (baseStart_1772019 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1772019 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1772019 prefixEnd_1772019 := by exact prefixLift 1772019
  have htrace : WordTrace (prefixWord ++ tailWord_1772019) baseStart_1772019 baseEnd_1772019 := by
    simpa [prefixWord, tailWord_1772019, baseEnd_1772019] using wordTrace_append hprefix tailTrace_1772019
  have hstable : (prefixWord ++ tailWord_1772019).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1772019).length < 2 ^ (prefixWord ++ tailWord_1772019).sum := by decide
  have hdescent : baseEnd_1772019 < baseStart_1772019 := by decide
  rcases family_descends (prefixWord ++ tailWord_1772019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1772039 : List Nat := [1, 1, 4, 3, 4, 1, 1, 2, 4]
def baseStart_1772039 : Nat := 118140960795 + 1772039 * 2 ^ 59
def prefixEnd_1772039 : Nat := 4983230072969 + 3 ^ 40 * 1772039 * 2
def baseEnd_1772039 : Nat := 404403442450087832428021

theorem tailTrace_1772039 : CollatzResearch.WordTrace tailWord_1772039 prefixEnd_1772039 404403442450087832428021 := by
  unfold tailWord_1772039
  simp only [CollatzResearch.WordTrace]
  refine ⟨64631572027212818011895171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43087714684808545341263447 64631572027212818011895171)
  ·
    refine ⟨96947358040819227017842757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64631572027212818011895171 96947358040819227017842757)
    ·
      refine ⟨18177629632653605065845517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96947358040819227017842757 18177629632653605065845517)
      ·
        refine ⟨6816611112245101899692069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18177629632653605065845517 6816611112245101899692069)
        ·
          refine ⟨1278114583545956606192263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6816611112245101899692069 1278114583545956606192263)
          ·
            refine ⟨1917171875318934909288395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1278114583545956606192263 1917171875318934909288395)
            ·
              refine ⟨2875757812978402363932593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1917171875318934909288395 2875757812978402363932593)
              ·
                refine ⟨2156818359733801772949445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2875757812978402363932593 2156818359733801772949445)
                ·
                  refine ⟨404403442450087832428021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2156818359733801772949445 404403442450087832428021)
                  ·
                    rfl

theorem cell21_1772039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 2, 4].length) (baseStart_1772039 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1772039 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1772039 prefixEnd_1772039 := by exact prefixLift 1772039
  have htrace : WordTrace (prefixWord ++ tailWord_1772039) baseStart_1772039 baseEnd_1772039 := by
    simpa [prefixWord, tailWord_1772039, baseEnd_1772039] using wordTrace_append hprefix tailTrace_1772039
  have hstable : (prefixWord ++ tailWord_1772039).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1772039).length < 2 ^ (prefixWord ++ tailWord_1772039).sum := by decide
  have hdescent : baseEnd_1772039 < baseStart_1772039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1772039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1772160 : List Nat := [2, 1, 1, 2, 1, 7, 2, 2, 3]
def baseStart_1772160 : Nat := 118140960795 + 1772160 * 2 ^ 59
def prefixEnd_1772160 : Nat := 4983230072969 + 3 ^ 40 * 1772160 * 2
def baseEnd_1772160 : Nat := 404431056298618510911107

theorem tailTrace_1772160 : CollatzResearch.WordTrace tailWord_1772160 prefixEnd_1772160 404431056298618510911107 := by
  unfold tailWord_1772160
  simp only [CollatzResearch.WordTrace]
  refine ⟨32317992629887227838524967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43090656839849637118033289 32317992629887227838524967)
  ·
    refine ⟨48476988944830841757787451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32317992629887227838524967 48476988944830841757787451)
    ·
      refine ⟨72715483417246262636681177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48476988944830841757787451 72715483417246262636681177)
      ·
        refine ⟨54536612562934696977510883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72715483417246262636681177 54536612562934696977510883)
        ·
          refine ⟨81804918844402045466266325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54536612562934696977510883 81804918844402045466266325)
          ·
            refine ⟨1917302785415672940615617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 81804918844402045466266325 1917302785415672940615617)
            ·
              refine ⟨1437977089061754705461713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1917302785415672940615617 1437977089061754705461713)
              ·
                refine ⟨1078482816796316029096285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1437977089061754705461713 1078482816796316029096285)
                ·
                  refine ⟨404431056298618510911107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1078482816796316029096285 404431056298618510911107)
                  ·
                    rfl

theorem cell21_1772160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 2, 2, 3].length) (baseStart_1772160 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1772160 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1772160 prefixEnd_1772160 := by exact prefixLift 1772160
  have htrace : WordTrace (prefixWord ++ tailWord_1772160) baseStart_1772160 baseEnd_1772160 := by
    simpa [prefixWord, tailWord_1772160, baseEnd_1772160] using wordTrace_append hprefix tailTrace_1772160
  have hstable : (prefixWord ++ tailWord_1772160).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1772160).length < 2 ^ (prefixWord ++ tailWord_1772160).sum := by decide
  have hdescent : baseEnd_1772160 < baseStart_1772160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1772160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1772185 : List Nat := [1, 2, 1, 2, 1, 2, 5, 2, 5]
def baseStart_1772185 : Nat := 118140960795 + 1772185 * 2 ^ 59
def prefixEnd_1772185 : Nat := 4983230072969 + 3 ^ 40 * 1772185 * 2
def baseEnd_1772185 : Nat := 404436761639224022994389

theorem tailTrace_1772185 : CollatzResearch.WordTrace tailWord_1772185 prefixEnd_1772185 404436761639224022994389 := by
  unfold tailWord_1772185
  simp only [CollatzResearch.WordTrace]
  refine ⟨64636897084683884946710009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43091264723122589964473339 64636897084683884946710009)
  ·
    refine ⟨48477672813512913710032507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64636897084683884946710009 48477672813512913710032507)
    ·
      refine ⟨72716509220269370565048761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48477672813512913710032507 72716509220269370565048761)
      ·
        refine ⟨54537381915202027923786571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72716509220269370565048761 54537381915202027923786571)
        ·
          refine ⟨81806072872803041885679857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54537381915202027923786571 81806072872803041885679857)
          ·
            refine ⟨61354554654602281414259893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81806072872803041885679857 61354554654602281414259893)
            ·
              refine ⟨5751989498868963882586865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61354554654602281414259893 5751989498868963882586865)
              ·
                refine ⟨4313992124151722911940149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5751989498868963882586865 4313992124151722911940149)
                ·
                  refine ⟨404436761639224022994389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4313992124151722911940149 404436761639224022994389)
                  ·
                    rfl

theorem cell21_1772185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 2, 5].length) (baseStart_1772185 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1772185 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1772185 prefixEnd_1772185 := by exact prefixLift 1772185
  have htrace : WordTrace (prefixWord ++ tailWord_1772185) baseStart_1772185 baseEnd_1772185 := by
    simpa [prefixWord, tailWord_1772185, baseEnd_1772185] using wordTrace_append hprefix tailTrace_1772185
  have hstable : (prefixWord ++ tailWord_1772185).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1772185).length < 2 ^ (prefixWord ++ tailWord_1772185).sum := by decide
  have hdescent : baseEnd_1772185 < baseStart_1772185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1772185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1772188 : List Nat := [2, 2, 3, 2, 2, 2, 3, 5]
def baseStart_1772188 : Nat := 118140960795 + 1772188 * 2 ^ 59
def prefixEnd_1772188 : Nat := 4983230072969 + 3 ^ 40 * 1772188 * 2
def baseEnd_1772188 : Nat := 134812482093365561481461

theorem tailTrace_1772188 : CollatzResearch.WordTrace tailWord_1772188 prefixEnd_1772188 134812482093365561481461 := by
  unfold tailWord_1772188
  simp only [CollatzResearch.WordTrace]
  refine ⟨32318503251836508229534609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43091337669115344306046145 32318503251836508229534609)
  ·
    refine ⟨24238877438877381172150957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32318503251836508229534609 24238877438877381172150957)
    ·
      refine ⟨9089579039579017939556609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24238877438877381172150957 9089579039579017939556609)
      ·
        refine ⟨6817184279684263454667457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9089579039579017939556609 6817184279684263454667457)
        ·
          refine ⟨5112888209763197591000593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6817184279684263454667457 5112888209763197591000593)
          ·
            refine ⟨3834666157322398193250445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5112888209763197591000593 3834666157322398193250445)
            ·
              refine ⟨1437999808995899322468917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3834666157322398193250445 1437999808995899322468917)
              ·
                refine ⟨134812482093365561481461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1437999808995899322468917 134812482093365561481461)
                ·
                  rfl

theorem cell21_1772188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 3, 5].length) (baseStart_1772188 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1772188 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1772188 prefixEnd_1772188 := by exact prefixLift 1772188
  have htrace : WordTrace (prefixWord ++ tailWord_1772188) baseStart_1772188 baseEnd_1772188 := by
    simpa [prefixWord, tailWord_1772188, baseEnd_1772188] using wordTrace_append hprefix tailTrace_1772188
  have hstable : (prefixWord ++ tailWord_1772188).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1772188).length < 2 ^ (prefixWord ++ tailWord_1772188).sum := by decide
  have hdescent : baseEnd_1772188 < baseStart_1772188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1772188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1772247 : List Nat := [1, 1, 3, 2, 1, 4, 4, 5]
def baseStart_1772247 : Nat := 118140960795 + 1772247 * 2 ^ 59
def prefixEnd_1772247 : Nat := 4983230072969 + 3 ^ 40 * 1772247 * 2
def baseEnd_1772247 : Nat := 134816970294641897653643

theorem tailTrace_1772247 : CollatzResearch.WordTrace tailWord_1772247 prefixEnd_1772247 134816970294641897653643 := by
  unfold tailWord_1772247
  simp only [CollatzResearch.WordTrace]
  refine ⟨64639158410459269535466995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43092772273639513023644663 64639158410459269535466995)
  ·
    refine ⟨96958737615688904303200493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64639158410459269535466995 96958737615688904303200493)
    ·
      refine ⟨36359526605883339113700185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96958737615688904303200493 36359526605883339113700185)
      ·
        refine ⟨27269644954412504335275139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36359526605883339113700185 27269644954412504335275139)
        ·
          refine ⟨40904467431618756502912709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27269644954412504335275139 40904467431618756502912709)
          ·
            refine ⟨7669587643428516844296133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40904467431618756502912709 7669587643428516844296133)
            ·
              refine ⟨1438047683142846908305525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7669587643428516844296133 1438047683142846908305525)
              ·
                refine ⟨134816970294641897653643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1438047683142846908305525 134816970294641897653643)
                ·
                  rfl

theorem cell21_1772247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 4, 5].length) (baseStart_1772247 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1772247 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1772247 prefixEnd_1772247 := by exact prefixLift 1772247
  have htrace : WordTrace (prefixWord ++ tailWord_1772247) baseStart_1772247 baseEnd_1772247 := by
    simpa [prefixWord, tailWord_1772247, baseEnd_1772247] using wordTrace_append hprefix tailTrace_1772247
  have hstable : (prefixWord ++ tailWord_1772247).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1772247).length < 2 ^ (prefixWord ++ tailWord_1772247).sum := by decide
  have hdescent : baseEnd_1772247 < baseStart_1772247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1772247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1772264 : List Nat := [2, 1, 4, 1, 5, 1, 7]
def baseStart_1772264 : Nat := 118140960795 + 1772264 * 2 ^ 59
def prefixEnd_1772264 : Nat := 4983230072969 + 3 ^ 40 * 1772264 * 2
def baseEnd_1772264 : Nat := 44939421168393049019729

theorem tailTrace_1772264 : CollatzResearch.WordTrace tailWord_1772264 prefixEnd_1772264 44939421168393049019729 := by
  unfold tailWord_1772264
  simp only [CollatzResearch.WordTrace]
  refine ⟨32319889225698840719417923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43093185634265120959223897 32319889225698840719417923)
  ·
    refine ⟨48479833838548261079126885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32319889225698840719417923 48479833838548261079126885)
    ·
      refine ⟨9089968844727798952336291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48479833838548261079126885 9089968844727798952336291)
      ·
        refine ⟨13634953267091698428504437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9089968844727798952336291 13634953267091698428504437)
        ·
          refine ⟨1278276868789846727672291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13634953267091698428504437 1278276868789846727672291)
          ·
            refine ⟨1917415303184770091508437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1278276868789846727672291 1917415303184770091508437)
            ·
              refine ⟨44939421168393049019729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1917415303184770091508437 44939421168393049019729)
              ·
                rfl

theorem cell21_1772264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 7].length) (baseStart_1772264 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1772264 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1772264 prefixEnd_1772264 := by exact prefixLift 1772264
  have htrace : WordTrace (prefixWord ++ tailWord_1772264) baseStart_1772264 baseEnd_1772264 := by
    simpa [prefixWord, tailWord_1772264, baseEnd_1772264] using wordTrace_append hprefix tailTrace_1772264
  have hstable : (prefixWord ++ tailWord_1772264).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1772264).length < 2 ^ (prefixWord ++ tailWord_1772264).sum := by decide
  have hdescent : baseEnd_1772264 < baseStart_1772264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1772264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1772337 : List Nat := [1, 2, 2, 3, 2, 1, 2, 3, 5]
def baseStart_1772337 : Nat := 118140960795 + 1772337 * 2 ^ 59
def prefixEnd_1772337 : Nat := 4983230072969 + 3 ^ 40 * 1772337 * 2
def baseEnd_1772337 : Nat := 404471450110105536460745

theorem tailTrace_1772337 : CollatzResearch.WordTrace tailWord_1772337 prefixEnd_1772337 404471450110105536460745 := by
  unfold tailWord_1772337
  simp only [CollatzResearch.WordTrace]
  refine ⟨64642440980133214906243265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43094960653422143270828843 64642440980133214906243265)
  ·
    refine ⟨48481830735099911179682449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64642440980133214906243265 48481830735099911179682449)
    ·
      refine ⟨36361373051324933384761837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48481830735099911179682449 36361373051324933384761837)
      ·
        refine ⟨13635514894246850019285689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36361373051324933384761837 13635514894246850019285689)
        ·
          refine ⟨10226636170685137514464267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13635514894246850019285689 10226636170685137514464267)
          ·
            refine ⟨15339954256027706271696401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10226636170685137514464267 15339954256027706271696401)
            ·
              refine ⟨11504965692020779703772301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15339954256027706271696401 11504965692020779703772301)
              ·
                refine ⟨4314362134507792388914613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11504965692020779703772301 4314362134507792388914613)
                ·
                  refine ⟨404471450110105536460745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4314362134507792388914613 404471450110105536460745)
                  ·
                    rfl

theorem cell21_1772337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 3, 5].length) (baseStart_1772337 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1772337 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1772337 prefixEnd_1772337 := by exact prefixLift 1772337
  have htrace : WordTrace (prefixWord ++ tailWord_1772337) baseStart_1772337 baseEnd_1772337 := by
    simpa [prefixWord, tailWord_1772337, baseEnd_1772337] using wordTrace_append hprefix tailTrace_1772337
  have hstable : (prefixWord ++ tailWord_1772337).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1772337).length < 2 ^ (prefixWord ++ tailWord_1772337).sum := by decide
  have hdescent : baseEnd_1772337 < baseStart_1772337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1772337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1772413 : List Nat := [1, 4, 1, 1, 2, 1, 4, 2, 5]
def baseStart_1772413 : Nat := 118140960795 + 1772413 * 2 ^ 59
def prefixEnd_1772413 : Nat := 4983230072969 + 3 ^ 40 * 1772413 * 2
def baseEnd_1772413 : Nat := 404488794345546293193923

theorem tailTrace_1772413 : CollatzResearch.WordTrace tailWord_1772413 prefixEnd_1772413 404488794345546293193923 := by
  unfold tailWord_1772413
  simp only [CollatzResearch.WordTrace]
  refine ⟨64645212927857879886009893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43096808618571919924006595 64645212927857879886009893)
  ·
    refine ⟨12120977423973352478626855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64645212927857879886009893 12120977423973352478626855)
    ·
      refine ⟨18181466135960028717940283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12120977423973352478626855 18181466135960028717940283)
      ·
        refine ⟨27272199203940043076910425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18181466135960028717940283 27272199203940043076910425)
        ·
          refine ⟨20454149402955032307682819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27272199203940043076910425 20454149402955032307682819)
          ·
            refine ⟨30681224104432548461524229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20454149402955032307682819 30681224104432548461524229)
            ·
              refine ⟨5752729519581102836535793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30681224104432548461524229 5752729519581102836535793)
              ·
                refine ⟨4314547139685827127401845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5752729519581102836535793 4314547139685827127401845)
                ·
                  refine ⟨404488794345546293193923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4314547139685827127401845 404488794345546293193923)
                  ·
                    rfl

theorem cell21_1772413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 2, 5].length) (baseStart_1772413 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1772413 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1772413 prefixEnd_1772413 := by exact prefixLift 1772413
  have htrace : WordTrace (prefixWord ++ tailWord_1772413) baseStart_1772413 baseEnd_1772413 := by
    simpa [prefixWord, tailWord_1772413, baseEnd_1772413] using wordTrace_append hprefix tailTrace_1772413
  have hstable : (prefixWord ++ tailWord_1772413).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1772413).length < 2 ^ (prefixWord ++ tailWord_1772413).sum := by decide
  have hdescent : baseEnd_1772413 < baseStart_1772413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1772413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1772427 : List Nat := [1, 1, 1, 1, 4, 2, 3, 2, 6]
def baseStart_1772427 : Nat := 118140960795 + 1772427 * 2 ^ 59
def prefixEnd_1772427 : Nat := 4983230072969 + 3 ^ 40 * 1772427 * 2
def baseEnd_1772427 : Nat := 404491989336285379960561

theorem tailTrace_1772427 : CollatzResearch.WordTrace tailWord_1772427 prefixEnd_1772427 404491989336285379960561 := by
  unfold tailWord_1772427
  simp only [CollatzResearch.WordTrace]
  refine ⟨64645723549807160277019535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43097149033204773518013023 64645723549807160277019535)
  ·
    refine ⟨96968585324710740415529303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64645723549807160277019535 96968585324710740415529303)
    ·
      refine ⟨145452877987066110623293955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96968585324710740415529303 145452877987066110623293955)
      ·
        refine ⟨218179316980599165934940933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145452877987066110623293955 218179316980599165934940933)
        ·
          refine ⟨40908621933862343612801425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 218179316980599165934940933 40908621933862343612801425)
          ·
            refine ⟨30681466450396757709601069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40908621933862343612801425 30681466450396757709601069)
            ·
              refine ⟨11505549918898784141100401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30681466450396757709601069 11505549918898784141100401)
              ·
                refine ⟨8629162439174088105825301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11505549918898784141100401 8629162439174088105825301)
                ·
                  refine ⟨404491989336285379960561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8629162439174088105825301 404491989336285379960561)
                  ·
                    rfl

theorem cell21_1772427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 2, 6].length) (baseStart_1772427 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1772427 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1772427 prefixEnd_1772427 := by exact prefixLift 1772427
  have htrace : WordTrace (prefixWord ++ tailWord_1772427) baseStart_1772427 baseEnd_1772427 := by
    simpa [prefixWord, tailWord_1772427, baseEnd_1772427] using wordTrace_append hprefix tailTrace_1772427
  have hstable : (prefixWord ++ tailWord_1772427).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1772427).length < 2 ^ (prefixWord ++ tailWord_1772427).sum := by decide
  have hdescent : baseEnd_1772427 < baseStart_1772427 := by decide
  rcases family_descends (prefixWord ++ tailWord_1772427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1772520 : List Nat := [2, 1, 4, 1, 1, 1, 4, 3, 4]
def baseStart_1772520 : Nat := 118140960795 + 1772520 * 2 ^ 59
def prefixEnd_1772520 : Nat := 4983230072969 + 3 ^ 40 * 1772520 * 2
def baseEnd_1772520 : Nat := 404513213203337884910371

theorem tailTrace_1772520 : CollatzResearch.WordTrace tailWord_1772520 prefixEnd_1772520 404513213203337884910371 := by
  unfold tailWord_1772520
  simp only [CollatzResearch.WordTrace]
  refine ⟨32324557769235118580077507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43099410358980158106770009 32324557769235118580077507)
  ·
    refine ⟨48486836653852677870116261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32324557769235118580077507 48486836653852677870116261)
    ·
      refine ⟨9091281872597377100646799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48486836653852677870116261 9091281872597377100646799)
      ·
        refine ⟨13636922808896065650970199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9091281872597377100646799 13636922808896065650970199)
        ·
          refine ⟨20455384213344098476455299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13636922808896065650970199 20455384213344098476455299)
          ·
            refine ⟨30683076320016147714682949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20455384213344098476455299 30683076320016147714682949)
            ·
              refine ⟨5753076810003027696503053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30683076320016147714682949 5753076810003027696503053)
              ·
                refine ⟨2157403803751135386188645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5753076810003027696503053 2157403803751135386188645)
                ·
                  refine ⟨404513213203337884910371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2157403803751135386188645 404513213203337884910371)
                  ·
                    rfl

theorem cell21_1772520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 3, 4].length) (baseStart_1772520 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1772520 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1772520 prefixEnd_1772520 := by exact prefixLift 1772520
  have htrace : WordTrace (prefixWord ++ tailWord_1772520) baseStart_1772520 baseEnd_1772520 := by
    simpa [prefixWord, tailWord_1772520, baseEnd_1772520] using wordTrace_append hprefix tailTrace_1772520
  have hstable : (prefixWord ++ tailWord_1772520).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1772520).length < 2 ^ (prefixWord ++ tailWord_1772520).sum := by decide
  have hdescent : baseEnd_1772520 < baseStart_1772520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1772520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1772565 : List Nat := [1, 3, 2, 1, 4, 1, 1, 3, 5]
def baseStart_1772565 : Nat := 118140960795 + 1772565 * 2 ^ 59
def prefixEnd_1772565 : Nat := 4983230072969 + 3 ^ 40 * 1772565 * 2
def baseEnd_1772565 : Nat := 404523482816427806660279

theorem tailTrace_1772565 : CollatzResearch.WordTrace tailWord_1772565 prefixEnd_1772565 404523482816427806660279 := by
  unfold tailWord_1772565
  simp only [CollatzResearch.WordTrace]
  refine ⟨64650756823307209845543149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43100504548871473230362099 64650756823307209845543149)
  ·
    refine ⟨24244033808740203692078681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64650756823307209845543149 24244033808740203692078681)
    ·
      refine ⟨18183025356555152769059011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24244033808740203692078681 18183025356555152769059011)
      ·
        refine ⟨27274538034832729153588517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18183025356555152769059011 27274538034832729153588517)
        ·
          refine ⟨5113975881531136716297847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27274538034832729153588517 5113975881531136716297847)
          ·
            refine ⟨7670963822296705074446771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5113975881531136716297847 7670963822296705074446771)
            ·
              refine ⟨11506445733445057611670157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7670963822296705074446771 11506445733445057611670157)
              ·
                refine ⟨4314917150041896604376309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11506445733445057611670157 4314917150041896604376309)
                ·
                  refine ⟨404523482816427806660279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4314917150041896604376309 404523482816427806660279)
                  ·
                    rfl

theorem cell21_1772565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 3, 5].length) (baseStart_1772565 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1772565 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1772565 prefixEnd_1772565 := by exact prefixLift 1772565
  have htrace : WordTrace (prefixWord ++ tailWord_1772565) baseStart_1772565 baseEnd_1772565 := by
    simpa [prefixWord, tailWord_1772565, baseEnd_1772565] using wordTrace_append hprefix tailTrace_1772565
  have hstable : (prefixWord ++ tailWord_1772565).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1772565).length < 2 ^ (prefixWord ++ tailWord_1772565).sum := by decide
  have hdescent : baseEnd_1772565 < baseStart_1772565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1772565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1772658 : List Nat := [3, 2, 1, 2, 2, 1, 2, 5, 3]
def baseStart_1772658 : Nat := 118140960795 + 1772658 * 2 ^ 59
def prefixEnd_1772658 : Nat := 4983230072969 + 3 ^ 40 * 1772658 * 2
def baseEnd_1772658 : Nat := 404544706683480311610089

theorem tailTrace_1772658 : CollatzResearch.WordTrace tailWord_1772658 prefixEnd_1772658 404544706683480311610089 := by
  unfold tailWord_1772658
  simp only [CollatzResearch.WordTrace]
  refine ⟨16163537202992571682169657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43102765874646857819119085 16163537202992571682169657)
  ·
    refine ⟨12122652902244428761627243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16163537202992571682169657 12122652902244428761627243)
    ·
      refine ⟨18183979353366643142440865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12122652902244428761627243 18183979353366643142440865)
      ·
        refine ⟨13637984515024982356830649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18183979353366643142440865 13637984515024982356830649)
        ·
          refine ⟨10228488386268736767622987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13637984515024982356830649 10228488386268736767622987)
          ·
            refine ⟨15342732579403105151434481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10228488386268736767622987 15342732579403105151434481)
            ·
              refine ⟨11507049434552328863575861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15342732579403105151434481 11507049434552328863575861)
              ·
                refine ⟨1078785884489280830960237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11507049434552328863575861 1078785884489280830960237)
                ·
                  refine ⟨404544706683480311610089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1078785884489280830960237 404544706683480311610089)
                  ·
                    rfl

theorem cell21_1772658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 5, 3].length) (baseStart_1772658 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1772658 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1772658 prefixEnd_1772658 := by exact prefixLift 1772658
  have htrace : WordTrace (prefixWord ++ tailWord_1772658) baseStart_1772658 baseEnd_1772658 := by
    simpa [prefixWord, tailWord_1772658, baseEnd_1772658] using wordTrace_append hprefix tailTrace_1772658
  have hstable : (prefixWord ++ tailWord_1772658).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1772658).length < 2 ^ (prefixWord ++ tailWord_1772658).sum := by decide
  have hdescent : baseEnd_1772658 < baseStart_1772658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1772658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1772731 : List Nat := [1, 1, 1, 1, 1, 2, 4, 6, 4]
def baseStart_1772731 : Nat := 118140960795 + 1772731 * 2 ^ 59
def prefixEnd_1772731 : Nat := 4983230072969 + 3 ^ 40 * 1772731 * 2
def baseEnd_1772731 : Nat := 404561366278048406893273

theorem tailTrace_1772731 : CollatzResearch.WordTrace tailWord_1772731 prefixEnd_1772731 404561366278048406893273 := by
  unfold tailWord_1772731
  simp only [CollatzResearch.WordTrace]
  refine ⟨64656811340705820196086047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43104540893803880130724031 64656811340705820196086047)
  ·
    refine ⟨96985217011058730294129071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64656811340705820196086047 96985217011058730294129071)
    ·
      refine ⟨145477825516588095441193607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96985217011058730294129071 145477825516588095441193607)
      ·
        refine ⟨218216738274882143161790411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145477825516588095441193607 218216738274882143161790411)
        ·
          refine ⟨327325107412323214742685617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218216738274882143161790411 327325107412323214742685617)
          ·
            refine ⟨245493830559242411057014213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 327325107412323214742685617 245493830559242411057014213)
            ·
              refine ⟨46030093229857952073190165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 245493830559242411057014213 46030093229857952073190165)
              ·
                refine ⟨2157660620149591503430789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 46030093229857952073190165 2157660620149591503430789)
                ·
                  refine ⟨404561366278048406893273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2157660620149591503430789 404561366278048406893273)
                  ·
                    rfl

theorem cell21_1772731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 6, 4].length) (baseStart_1772731 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1772731 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1772731 prefixEnd_1772731 := by exact prefixLift 1772731
  have htrace : WordTrace (prefixWord ++ tailWord_1772731) baseStart_1772731 baseEnd_1772731 := by
    simpa [prefixWord, tailWord_1772731, baseEnd_1772731] using wordTrace_append hprefix tailTrace_1772731
  have hstable : (prefixWord ++ tailWord_1772731).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1772731).length < 2 ^ (prefixWord ++ tailWord_1772731).sum := by decide
  have hdescent : baseEnd_1772731 < baseStart_1772731 := by decide
  rcases family_descends (prefixWord ++ tailWord_1772731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1772734 : List Nat := [4, 2, 1, 1, 3, 2, 2, 1, 5]
def baseStart_1772734 : Nat := 118140960795 + 1772734 * 2 ^ 59
def prefixEnd_1772734 : Nat := 4983230072969 + 3 ^ 40 * 1772734 * 2
def baseEnd_1772734 : Nat := 404562050918921068343267

theorem tailTrace_1772734 : CollatzResearch.WordTrace tailWord_1772734 prefixEnd_1772734 404562050918921068343267 := by
  unfold tailWord_1772734
  simp only [CollatzResearch.WordTrace]
  refine ⟨8082115094961868963555657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43104613839796634472296837 8082115094961868963555657)
  ·
    refine ⟨6061586321221401722666743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8082115094961868963555657 6061586321221401722666743)
    ·
      refine ⟨9092379481832102584000115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6061586321221401722666743 9092379481832102584000115)
      ·
        refine ⟨13638569222748153876000173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9092379481832102584000115 13638569222748153876000173)
        ·
          refine ⟨5114463458530557703500065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13638569222748153876000173 5114463458530557703500065)
          ·
            refine ⟨3835847593897918277625049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5114463458530557703500065 3835847593897918277625049)
            ·
              refine ⟨2876885695423438708218787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3835847593897918277625049 2876885695423438708218787)
              ·
                refine ⟨4315328543135158062328181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2876885695423438708218787 4315328543135158062328181)
                ·
                  refine ⟨404562050918921068343267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4315328543135158062328181 404562050918921068343267)
                  ·
                    rfl

theorem cell21_1772734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_1772734 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1772734 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1772734 prefixEnd_1772734 := by exact prefixLift 1772734
  have htrace : WordTrace (prefixWord ++ tailWord_1772734) baseStart_1772734 baseEnd_1772734 := by
    simpa [prefixWord, tailWord_1772734, baseEnd_1772734] using wordTrace_append hprefix tailTrace_1772734
  have hstable : (prefixWord ++ tailWord_1772734).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1772734).length < 2 ^ (prefixWord ++ tailWord_1772734).sum := by decide
  have hdescent : baseEnd_1772734 < baseStart_1772734 := by decide
  rcases family_descends (prefixWord ++ tailWord_1772734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1772900 : List Nat := [2, 3, 1, 1, 3, 2, 3, 2, 4]
def baseStart_1772900 : Nat := 118140960795 + 1772900 * 2 ^ 59
def prefixEnd_1772900 : Nat := 4983230072969 + 3 ^ 40 * 1772900 * 2
def baseEnd_1772900 : Nat := 404599934380541668576261

theorem tailTrace_1772900 : CollatzResearch.WordTrace tailWord_1772900 prefixEnd_1772900 404599934380541668576261 := by
  unfold tailWord_1772900
  simp only [CollatzResearch.WordTrace]
  refine ⟨32331487638546781029494077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43108650184729041372658769 32331487638546781029494077)
  ·
    refine ⟨12124307864455042886060279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32331487638546781029494077 12124307864455042886060279)
    ·
      refine ⟨18186461796682564329090419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12124307864455042886060279 18186461796682564329090419)
      ·
        refine ⟨27279692695023846493635629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18186461796682564329090419 27279692695023846493635629)
        ·
          refine ⟨10229884760633942435113361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27279692695023846493635629 10229884760633942435113361)
          ·
            refine ⟨7672413570475456826335021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10229884760633942435113361 7672413570475456826335021)
            ·
              refine ⟨2877155088928296309875633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7672413570475456826335021 2877155088928296309875633)
              ·
                refine ⟨2157866316696222232406725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2877155088928296309875633 2157866316696222232406725)
                ·
                  refine ⟨404599934380541668576261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2157866316696222232406725 404599934380541668576261)
                  ·
                    rfl

theorem cell21_1772900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 2, 4].length) (baseStart_1772900 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1772900 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1772900 prefixEnd_1772900 := by exact prefixLift 1772900
  have htrace : WordTrace (prefixWord ++ tailWord_1772900) baseStart_1772900 baseEnd_1772900 := by
    simpa [prefixWord, tailWord_1772900, baseEnd_1772900] using wordTrace_append hprefix tailTrace_1772900
  have hstable : (prefixWord ++ tailWord_1772900).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1772900).length < 2 ^ (prefixWord ++ tailWord_1772900).sum := by decide
  have hdescent : baseEnd_1772900 < baseStart_1772900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1772900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1772931 : List Nat := [1, 1, 1, 3, 5, 3, 2, 5]
def baseStart_1772931 : Nat := 118140960795 + 1772931 * 2 ^ 59
def prefixEnd_1772931 : Nat := 4983230072969 + 3 ^ 40 * 1772931 * 2
def baseEnd_1772931 : Nat := 134869003000964167853177

theorem tailTrace_1772931 : CollatzResearch.WordTrace tailWord_1772931 prefixEnd_1772931 134869003000964167853177 := by
  unfold tailWord_1772931
  simp only [CollatzResearch.WordTrace]
  refine ⟨64664105939981254353366647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43109403959987502902244431 64664105939981254353366647)
  ·
    refine ⟨96996158909971881530049971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64664105939981254353366647 96996158909971881530049971)
    ·
      refine ⟨145494238364957822295074957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96996158909971881530049971 145494238364957822295074957)
      ·
        refine ⟨54560339386859183360653109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145494238364957822295074957 54560339386859183360653109)
        ·
          refine ⟨5115031817518048440061229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54560339386859183360653109 5115031817518048440061229)
          ·
            refine ⟨1918136931569268165022961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5115031817518048440061229 1918136931569268165022961)
            ·
              refine ⟨1438602698676951123767221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1918136931569268165022961 1438602698676951123767221)
              ·
                refine ⟨134869003000964167853177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1438602698676951123767221 134869003000964167853177)
                ·
                  rfl

theorem cell21_1772931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 2, 5].length) (baseStart_1772931 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1772931 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1772931 prefixEnd_1772931 := by exact prefixLift 1772931
  have htrace : WordTrace (prefixWord ++ tailWord_1772931) baseStart_1772931 baseEnd_1772931 := by
    simpa [prefixWord, tailWord_1772931, baseEnd_1772931] using wordTrace_append hprefix tailTrace_1772931
  have hstable : (prefixWord ++ tailWord_1772931).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1772931).length < 2 ^ (prefixWord ++ tailWord_1772931).sum := by decide
  have hdescent : baseEnd_1772931 < baseStart_1772931 := by decide
  rcases family_descends (prefixWord ++ tailWord_1772931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1772959 : List Nat := [1, 1, 2, 5, 1, 2, 2, 1, 6]
def baseStart_1772959 : Nat := 118140960795 + 1772959 * 2 ^ 59
def prefixEnd_1772959 : Nat := 4983230072969 + 3 ^ 40 * 1772959 * 2
def baseEnd_1772959 : Nat := 404613398984370677092807

theorem tailTrace_1772959 : CollatzResearch.WordTrace tailWord_1772959 prefixEnd_1772959 404613398984370677092807 := by
  unfold tailWord_1772959
  simp only [CollatzResearch.WordTrace]
  refine ⟨64665127183879815135385931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43110084789253210090257287 64665127183879815135385931)
  ·
    refine ⟨96997690775819722703078897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64665127183879815135385931 96997690775819722703078897)
    ·
      refine ⟨72748268081864792027309173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96997690775819722703078897 72748268081864792027309173)
      ·
        refine ⟨6820150132674824252560235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72748268081864792027309173 6820150132674824252560235)
        ·
          refine ⟨10230225199012236378840353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6820150132674824252560235 10230225199012236378840353)
          ·
            refine ⟨7672668899259177284130265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10230225199012236378840353 7672668899259177284130265)
            ·
              refine ⟨5754501674444382963097699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7672668899259177284130265 5754501674444382963097699)
              ·
                refine ⟨8631752511666574444646549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5754501674444382963097699 8631752511666574444646549)
                ·
                  refine ⟨404613398984370677092807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8631752511666574444646549 404613398984370677092807)
                  ·
                    rfl

theorem cell21_1772959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 1, 6].length) (baseStart_1772959 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1772959 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1772959 prefixEnd_1772959 := by exact prefixLift 1772959
  have htrace : WordTrace (prefixWord ++ tailWord_1772959) baseStart_1772959 baseEnd_1772959 := by
    simpa [prefixWord, tailWord_1772959, baseEnd_1772959] using wordTrace_append hprefix tailTrace_1772959
  have hstable : (prefixWord ++ tailWord_1772959).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1772959).length < 2 ^ (prefixWord ++ tailWord_1772959).sum := by decide
  have hdescent : baseEnd_1772959 < baseStart_1772959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1772959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1772962 : List Nat := [3, 3, 1, 2, 1, 4, 1, 1, 5]
def baseStart_1772962 : Nat := 118140960795 + 1772962 * 2 ^ 59
def prefixEnd_1772962 : Nat := 4983230072969 + 3 ^ 40 * 1772962 * 2
def baseEnd_1772962 : Nat := 404614083625243338542801

theorem tailTrace_1772962 : CollatzResearch.WordTrace tailWord_1772962 prefixEnd_1772962 404614083625243338542801 := by
  unfold tailWord_1772962
  simp only [CollatzResearch.WordTrace]
  refine ⟨16166309150717236661936285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43110157735245964431830093 16166309150717236661936285)
  ·
    refine ⟨6062365931518963748226107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16166309150717236661936285 6062365931518963748226107)
    ·
      refine ⟨9093548897278445622339161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6062365931518963748226107 9093548897278445622339161)
      ·
        refine ⟨6820161672958834216754371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9093548897278445622339161 6820161672958834216754371)
        ·
          refine ⟨10230242509438251325131557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6820161672958834216754371 10230242509438251325131557)
          ·
            refine ⟨1918170470519672123462167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10230242509438251325131557 1918170470519672123462167)
            ·
              refine ⟨2877255705779508185193251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1918170470519672123462167 2877255705779508185193251)
              ·
                refine ⟨4315883558669262277789877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2877255705779508185193251 4315883558669262277789877)
                ·
                  refine ⟨404614083625243338542801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4315883558669262277789877 404614083625243338542801)
                  ·
                    rfl

theorem cell21_1772962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 1, 5].length) (baseStart_1772962 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1772962 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1772962 prefixEnd_1772962 := by exact prefixLift 1772962
  have htrace : WordTrace (prefixWord ++ tailWord_1772962) baseStart_1772962 baseEnd_1772962 := by
    simpa [prefixWord, tailWord_1772962, baseEnd_1772962] using wordTrace_append hprefix tailTrace_1772962
  have hstable : (prefixWord ++ tailWord_1772962).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1772962).length < 2 ^ (prefixWord ++ tailWord_1772962).sum := by decide
  have hdescent : baseEnd_1772962 < baseStart_1772962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1772962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773139 : List Nat := [1, 1, 1, 2, 1, 1, 2, 1, 11]
def baseStart_1773139 : Nat := 118140960795 + 1773139 * 2 ^ 59
def prefixEnd_1773139 : Nat := 4983230072969 + 3 ^ 40 * 1773139 * 2
def baseEnd_1773139 : Nat := 404654477436730364092439

theorem tailTrace_1773139 : CollatzResearch.WordTrace tailWord_1773139 prefixEnd_1773139 404654477436730364092439 := by
  unfold tailWord_1773139
  simp only [CollatzResearch.WordTrace]
  refine ⟨64671692323227705876938471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43114461548818470584625647 64671692323227705876938471)
  ·
    refine ⟨97007538484841558815407707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64671692323227705876938471 97007538484841558815407707)
    ·
      refine ⟨145511307727262338223111561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97007538484841558815407707 145511307727262338223111561)
      ·
        refine ⟨109133480795446753667333671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145511307727262338223111561 109133480795446753667333671)
        ·
          refine ⟨163700221193170130501000507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109133480795446753667333671 163700221193170130501000507)
          ·
            refine ⟨245550331789755195751500761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163700221193170130501000507 245550331789755195751500761)
            ·
              refine ⟨184162748842316396813625571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 245550331789755195751500761 184162748842316396813625571)
              ·
                refine ⟨276244123263474595220438357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184162748842316396813625571 276244123263474595220438357)
                ·
                  refine ⟨404654477436730364092439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 276244123263474595220438357 404654477436730364092439)
                  ·
                    rfl

theorem cell21_1773139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 11].length) (baseStart_1773139 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1773139 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1773139 prefixEnd_1773139 := by exact prefixLift 1773139
  have htrace : WordTrace (prefixWord ++ tailWord_1773139) baseStart_1773139 baseEnd_1773139 := by
    simpa [prefixWord, tailWord_1773139, baseEnd_1773139] using wordTrace_append hprefix tailTrace_1773139
  have hstable : (prefixWord ++ tailWord_1773139).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773139).length < 2 ^ (prefixWord ++ tailWord_1773139).sum := by decide
  have hdescent : baseEnd_1773139 < baseStart_1773139 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773238 : List Nat := [5, 1, 3, 1, 1, 3, 1, 2, 4]
def baseStart_1773238 : Nat := 118140960795 + 1773238 * 2 ^ 59
def prefixEnd_1773238 : Nat := 4983230072969 + 3 ^ 40 * 1773238 * 2
def baseEnd_1773238 : Nat := 404677070585528191942237

theorem tailTrace_1773238 : CollatzResearch.WordTrace tailWord_1773238 prefixEnd_1773238 404677070585528191942237 := by
  unfold tailWord_1773238
  simp only [CollatzResearch.WordTrace]
  refine ⟨4042206446866815361549523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43116868766579363856528245 4042206446866815361549523)
  ·
    refine ⟨6063309670300223042324285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4042206446866815361549523 6063309670300223042324285)
    ·
      refine ⟨2273741126362583640871607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6063309670300223042324285 2273741126362583640871607)
      ·
        refine ⟨3410611689543875461307411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2273741126362583640871607 3410611689543875461307411)
        ·
          refine ⟨5115917534315813191961117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3410611689543875461307411 5115917534315813191961117)
          ·
            refine ⟨1918469075368429946985419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5115917534315813191961117 1918469075368429946985419)
            ·
              refine ⟨2877703613052644920478129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1918469075368429946985419 2877703613052644920478129)
              ·
                refine ⟨2158277709789483690358597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2877703613052644920478129 2158277709789483690358597)
                ·
                  refine ⟨404677070585528191942237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2158277709789483690358597 404677070585528191942237)
                  ·
                    rfl

theorem cell21_1773238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 2, 4].length) (baseStart_1773238 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1773238 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1773238 prefixEnd_1773238 := by exact prefixLift 1773238
  have htrace : WordTrace (prefixWord ++ tailWord_1773238) baseStart_1773238 baseEnd_1773238 := by
    simpa [prefixWord, tailWord_1773238, baseEnd_1773238] using wordTrace_append hprefix tailTrace_1773238
  have hstable : (prefixWord ++ tailWord_1773238).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773238).length < 2 ^ (prefixWord ++ tailWord_1773238).sum := by decide
  have hdescent : baseEnd_1773238 < baseStart_1773238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773283 : List Nat := [1, 1, 1, 7, 2, 2, 1, 3, 3]
def baseStart_1773283 : Nat := 118140960795 + 1773283 * 2 ^ 59
def prefixEnd_1773283 : Nat := 4983230072969 + 3 ^ 40 * 1773283 * 2
def baseEnd_1773283 : Nat := 404687340198618113692145

theorem tailTrace_1773283 : CollatzResearch.WordTrace tailWord_1773283 prefixEnd_1773283 404687340198618113692145 := by
  unfold tailWord_1773283
  simp only [CollatzResearch.WordTrace]
  refine ⟨64676944434706018470180503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43117962956470678980120335 64676944434706018470180503)
  ·
    refine ⟨97015416652059027705270755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64676944434706018470180503 97015416652059027705270755)
    ·
      refine ⟨145523124978088541557906133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97015416652059027705270755 145523124978088541557906133)
      ·
        refine ⟨3410698241673950192763425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 145523124978088541557906133 3410698241673950192763425)
        ·
          refine ⟨2558023681255462644572569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3410698241673950192763425 2558023681255462644572569)
          ·
            refine ⟨1918517760941596983429427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2558023681255462644572569 1918517760941596983429427)
            ·
              refine ⟨2877776641412395475144141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1918517760941596983429427 2877776641412395475144141)
              ·
                refine ⟨1079166240529648303179053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2877776641412395475144141 1079166240529648303179053)
                ·
                  refine ⟨404687340198618113692145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1079166240529648303179053 404687340198618113692145)
                  ·
                    rfl

theorem cell21_1773283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 3, 3].length) (baseStart_1773283 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1773283 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1773283 prefixEnd_1773283 := by exact prefixLift 1773283
  have htrace : WordTrace (prefixWord ++ tailWord_1773283) baseStart_1773283 baseEnd_1773283 := by
    simpa [prefixWord, tailWord_1773283, baseEnd_1773283] using wordTrace_append hprefix tailTrace_1773283
  have hstable : (prefixWord ++ tailWord_1773283).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773283).length < 2 ^ (prefixWord ++ tailWord_1773283).sum := by decide
  have hdescent : baseEnd_1773283 < baseStart_1773283 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773291 : List Nat := [1, 1, 1, 1, 2, 4, 2, 2, 7]
def baseStart_1773291 : Nat := 118140960795 + 1773291 * 2 ^ 59
def prefixEnd_1773291 : Nat := 4983230072969 + 3 ^ 40 * 1773291 * 2
def baseEnd_1773291 : Nat := 404689165907611877558795

theorem tailTrace_1773291 : CollatzResearch.WordTrace tailWord_1773291 prefixEnd_1773291 404689165907611877558795 := by
  unfold tailWord_1773291
  simp only [CollatzResearch.WordTrace]
  refine ⟨64677236218677035836471727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43118157479118023890981151 64677236218677035836471727)
  ·
    refine ⟨97015854328015553754707591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64677236218677035836471727 97015854328015553754707591)
    ·
      refine ⟨145523781492023330632061387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97015854328015553754707591 145523781492023330632061387)
      ·
        refine ⟨218285672238034995948092081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145523781492023330632061387 218285672238034995948092081)
        ·
          refine ⟨163714254178526246961069061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218285672238034995948092081 163714254178526246961069061)
          ·
            refine ⟨30696422658473671305200449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 163714254178526246961069061 30696422658473671305200449)
            ·
              refine ⟨23022316993855253478900337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30696422658473671305200449 23022316993855253478900337)
              ·
                refine ⟨17266737745391440109175253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23022316993855253478900337 17266737745391440109175253)
                ·
                  refine ⟨404689165907611877558795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17266737745391440109175253 404689165907611877558795)
                  ·
                    rfl

theorem cell21_1773291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 7].length) (baseStart_1773291 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1773291 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1773291 prefixEnd_1773291 := by exact prefixLift 1773291
  have htrace : WordTrace (prefixWord ++ tailWord_1773291) baseStart_1773291 baseEnd_1773291 := by
    simpa [prefixWord, tailWord_1773291, baseEnd_1773291] using wordTrace_append hprefix tailTrace_1773291
  have hstable : (prefixWord ++ tailWord_1773291).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773291).length < 2 ^ (prefixWord ++ tailWord_1773291).sum := by decide
  have hdescent : baseEnd_1773291 < baseStart_1773291 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773370 : List Nat := [3, 1, 1, 1, 5, 3, 1, 6]
def baseStart_1773370 : Nat := 118140960795 + 1773370 * 2 ^ 59
def prefixEnd_1773370 : Nat := 4983230072969 + 3 ^ 40 * 1773370 * 2
def baseEnd_1773370 : Nat := 134902398261308431913989

theorem tailTrace_1773370 : CollatzResearch.WordTrace tailWord_1773370 prefixEnd_1773370 134902398261308431913989 := by
  unfold tailWord_1773370
  simp only [CollatzResearch.WordTrace]
  refine ⟨16170029396347708082149391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43120078390260554885731709 16170029396347708082149391)
  ·
    refine ⟨24255044094521562123224087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16170029396347708082149391 24255044094521562123224087)
    ·
      refine ⟨36382566141782343184836131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24255044094521562123224087 36382566141782343184836131)
      ·
        refine ⟨54573849212673514777254197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36382566141782343184836131 54573849212673514777254197)
        ·
          refine ⟨5116298363688142010367581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54573849212673514777254197 5116298363688142010367581)
          ·
            refine ⟨1918611886383053253887843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5116298363688142010367581 1918611886383053253887843)
            ·
              refine ⟨2877917829574579880831765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1918611886383053253887843 2877917829574579880831765)
              ·
                refine ⟨134902398261308431913989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2877917829574579880831765 134902398261308431913989)
                ·
                  rfl

theorem cell21_1773370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 6].length) (baseStart_1773370 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1773370 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1773370 prefixEnd_1773370 := by exact prefixLift 1773370
  have htrace : WordTrace (prefixWord ++ tailWord_1773370) baseStart_1773370 baseEnd_1773370 := by
    simpa [prefixWord, tailWord_1773370, baseEnd_1773370] using wordTrace_append hprefix tailTrace_1773370
  have hstable : (prefixWord ++ tailWord_1773370).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773370).length < 2 ^ (prefixWord ++ tailWord_1773370).sum := by decide
  have hdescent : baseEnd_1773370 < baseStart_1773370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773384 : List Nat := [2, 1, 3, 1, 1, 5, 1, 2, 5]
def baseStart_1773384 : Nat := 118140960795 + 1773384 * 2 ^ 59
def prefixEnd_1773384 : Nat := 4983230072969 + 3 ^ 40 * 1773384 * 2
def baseEnd_1773384 : Nat := 404710389774664382508605

theorem tailTrace_1773384 : CollatzResearch.WordTrace tailWord_1773384 prefixEnd_1773384 404710389774664382508605 := by
  unfold tailWord_1773384
  simp only [CollatzResearch.WordTrace]
  refine ⟨32340314103670056359803603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43120418804893408479738137 32340314103670056359803603)
  ·
    refine ⟨48510471155505084539705405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32340314103670056359803603 48510471155505084539705405)
    ·
      refine ⟨18191426683314406702389527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48510471155505084539705405 18191426683314406702389527)
      ·
        refine ⟨27287140024971610053584291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18191426683314406702389527 27287140024971610053584291)
        ·
          refine ⟨40930710037457415080376437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27287140024971610053584291 40930710037457415080376437)
          ·
            refine ⟨3837254066011632663785291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40930710037457415080376437 3837254066011632663785291)
            ·
              refine ⟨5755881099017448995677937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3837254066011632663785291 5755881099017448995677937)
              ·
                refine ⟨4316910824263086746758453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5755881099017448995677937 4316910824263086746758453)
                ·
                  refine ⟨404710389774664382508605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4316910824263086746758453 404710389774664382508605)
                  ·
                    rfl

theorem cell21_1773384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 2, 5].length) (baseStart_1773384 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1773384 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1773384 prefixEnd_1773384 := by exact prefixLift 1773384
  have htrace : WordTrace (prefixWord ++ tailWord_1773384) baseStart_1773384 baseEnd_1773384 := by
    simpa [prefixWord, tailWord_1773384, baseEnd_1773384] using wordTrace_append hprefix tailTrace_1773384
  have hstable : (prefixWord ++ tailWord_1773384).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773384).length < 2 ^ (prefixWord ++ tailWord_1773384).sum := by decide
  have hdescent : baseEnd_1773384 < baseStart_1773384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773401 : List Nat := [1, 2, 1, 2, 2, 3, 4, 3, 3]
def baseStart_1773401 : Nat := 118140960795 + 1773401 * 2 ^ 59
def prefixEnd_1773401 : Nat := 4983230072969 + 3 ^ 40 * 1773401 * 2
def baseEnd_1773401 : Nat := 404714269406276130725237

theorem tailTrace_1773401 : CollatzResearch.WordTrace tailWord_1773401 prefixEnd_1773401 404714269406276130725237 := by
  unfold tailWord_1773401
  simp only [CollatzResearch.WordTrace]
  refine ⟨64681248248278524622976057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43120832165519016415317371 64681248248278524622976057)
  ·
    refine ⟨48510936186208893467232043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64681248248278524622976057 48510936186208893467232043)
    ·
      refine ⟨72766404279313340200848065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48510936186208893467232043 72766404279313340200848065)
      ·
        refine ⟨54574803209485005150636049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72766404279313340200848065 54574803209485005150636049)
        ·
          refine ⟨40931102407113753862977037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54574803209485005150636049 40931102407113753862977037)
          ·
            refine ⟨15349163402667657698616389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40931102407113753862977037 15349163402667657698616389)
            ·
              refine ⟨2877968138000185818490573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15349163402667657698616389 2877968138000185818490573)
              ·
                refine ⟨1079238051750069681933965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2877968138000185818490573 1079238051750069681933965)
                ·
                  refine ⟨404714269406276130725237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1079238051750069681933965 404714269406276130725237)
                  ·
                    rfl

theorem cell21_1773401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 3, 3].length) (baseStart_1773401 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1773401 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1773401 prefixEnd_1773401 := by exact prefixLift 1773401
  have htrace : WordTrace (prefixWord ++ tailWord_1773401) baseStart_1773401 baseEnd_1773401 := by
    simpa [prefixWord, tailWord_1773401, baseEnd_1773401] using wordTrace_append hprefix tailTrace_1773401
  have hstable : (prefixWord ++ tailWord_1773401).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773401).length < 2 ^ (prefixWord ++ tailWord_1773401).sum := by decide
  have hdescent : baseEnd_1773401 < baseStart_1773401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773418 : List Nat := [3, 1, 3, 4, 1, 1, 2, 1, 5]
def baseStart_1773418 : Nat := 118140960795 + 1773418 * 2 ^ 59
def prefixEnd_1773418 : Nat := 4983230072969 + 3 ^ 40 * 1773418 * 2
def baseEnd_1773418 : Nat := 404718149037887878941869

theorem tailTrace_1773418 : CollatzResearch.WordTrace tailWord_1773418 prefixEnd_1773418 404718149037887878941869 := by
  unfold tailWord_1773418
  simp only [CollatzResearch.WordTrace]
  refine ⟨16170467072304234131586227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43121245526144624350896605 16170467072304234131586227)
  ·
    refine ⟨24255700608456351197379341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16170467072304234131586227 24255700608456351197379341)
    ·
      refine ⟨9095887728171131699017253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24255700608456351197379341 9095887728171131699017253)
      ·
        refine ⟨1705478949032087193565735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9095887728171131699017253 1705478949032087193565735)
        ·
          refine ⟨2558218423548130790348603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1705478949032087193565735 2558218423548130790348603)
          ·
            refine ⟨3837327635322196185522905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2558218423548130790348603 3837327635322196185522905)
            ·
              refine ⟨2877995726491647139142179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3837327635322196185522905 2877995726491647139142179)
              ·
                refine ⟨4316993589737470708713269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2877995726491647139142179 4316993589737470708713269)
                ·
                  refine ⟨404718149037887878941869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4316993589737470708713269 404718149037887878941869)
                  ·
                    rfl

theorem cell21_1773418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 1, 5].length) (baseStart_1773418 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1773418 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1773418 prefixEnd_1773418 := by exact prefixLift 1773418
  have htrace : WordTrace (prefixWord ++ tailWord_1773418) baseStart_1773418 baseEnd_1773418 := by
    simpa [prefixWord, tailWord_1773418, baseEnd_1773418] using wordTrace_append hprefix tailTrace_1773418
  have hstable : (prefixWord ++ tailWord_1773418).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773418).length < 2 ^ (prefixWord ++ tailWord_1773418).sum := by decide
  have hdescent : baseEnd_1773418 < baseStart_1773418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773429 : List Nat := [1, 3, 4, 1, 1, 1, 2, 8]
def baseStart_1773429 : Nat := 118140960795 + 1773429 * 2 ^ 59
def prefixEnd_1773429 : Nat := 4983230072969 + 3 ^ 40 * 1773429 * 2
def baseEnd_1773429 : Nat := 134906886462584768086171

theorem tailTrace_1773429 : CollatzResearch.WordTrace tailWord_1773429 prefixEnd_1773429 134906886462584768086171 := by
  unfold tailWord_1773429
  simp only [CollatzResearch.WordTrace]
  refine ⟨64682269492177085404995341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43121512994784723603330227 64682269492177085404995341)
  ·
    refine ⟨24255851059566407026873253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64682269492177085404995341 24255851059566407026873253)
    ·
      refine ⟨4547972073668701317538735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24255851059566407026873253 4547972073668701317538735)
      ·
        refine ⟨6821958110503051976308103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4547972073668701317538735 6821958110503051976308103)
        ·
          refine ⟨10232937165754577964462155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6821958110503051976308103 10232937165754577964462155)
          ·
            refine ⟨15349405748631866946693233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10232937165754577964462155 15349405748631866946693233)
            ·
              refine ⟨11512054311473900210019925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15349405748631866946693233 11512054311473900210019925)
              ·
                refine ⟨134906886462584768086171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11512054311473900210019925 134906886462584768086171)
                ·
                  rfl

theorem cell21_1773429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 8].length) (baseStart_1773429 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1773429 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1773429 prefixEnd_1773429 := by exact prefixLift 1773429
  have htrace : WordTrace (prefixWord ++ tailWord_1773429) baseStart_1773429 baseEnd_1773429 := by
    simpa [prefixWord, tailWord_1773429, baseEnd_1773429] using wordTrace_append hprefix tailTrace_1773429
  have hstable : (prefixWord ++ tailWord_1773429).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773429).length < 2 ^ (prefixWord ++ tailWord_1773429).sum := by decide
  have hdescent : baseEnd_1773429 < baseStart_1773429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773522 : List Nat := [3, 2, 2, 3, 3, 8]
def baseStart_1773522 : Nat := 118140960795 + 1773522 * 2 ^ 59
def prefixEnd_1773522 : Nat := 4983230072969 + 3 ^ 40 * 1773522 * 2
def baseEnd_1773522 : Nat := 14990440120548400341049

theorem tailTrace_1773522 : CollatzResearch.WordTrace tailWord_1773522 prefixEnd_1773522 14990440120548400341049 := by
  unfold tailWord_1773522
  simp only [CollatzResearch.WordTrace]
  refine ⟨16171415370210040572032705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43123774320560108192087213 16171415370210040572032705)
  ·
    refine ⟨12128561527657530429024529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16171415370210040572032705 12128561527657530429024529)
    ·
      refine ⟨9096421145743147821768397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12128561527657530429024529 9096421145743147821768397)
      ·
        refine ⟨3411157929653680433163149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9096421145743147821768397 3411157929653680433163149)
        ·
          refine ⟨1279184223620130162436181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3411157929653680433163149 1279184223620130162436181)
          ·
            refine ⟨14990440120548400341049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1279184223620130162436181 14990440120548400341049)
            ·
              rfl

theorem cell21_1773522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 8].length) (baseStart_1773522 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1773522 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1773522 prefixEnd_1773522 := by exact prefixLift 1773522
  have htrace : WordTrace (prefixWord ++ tailWord_1773522) baseStart_1773522 baseEnd_1773522 := by
    simpa [prefixWord, tailWord_1773522, baseEnd_1773522] using wordTrace_append hprefix tailTrace_1773522
  have hstable : (prefixWord ++ tailWord_1773522).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773522).length < 2 ^ (prefixWord ++ tailWord_1773522).sum := by decide
  have hdescent : baseEnd_1773522 < baseStart_1773522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773646 : List Nat := [4, 1, 1, 1, 1, 5, 3, 2, 3]
def baseStart_1773646 : Nat := 118140960795 + 1773646 * 2 ^ 59
def prefixEnd_1773646 : Nat := 4983230072969 + 3 ^ 40 * 1773646 * 2
def baseEnd_1773646 : Nat := 404770181744210149141403

theorem tailTrace_1773646 : CollatzResearch.WordTrace tailWord_1773646 prefixEnd_1773646 404770181744210149141403 := by
  unfold tailWord_1773646
  simp only [CollatzResearch.WordTrace]
  refine ⟨8086273016548866433205599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43126789421593954310429861 8086273016548866433205599)
  ·
    refine ⟨12129409524823299649808399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8086273016548866433205599 12129409524823299649808399)
    ·
      refine ⟨18194114287234949474712599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12129409524823299649808399 18194114287234949474712599)
      ·
        refine ⟨27291171430852424212068899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18194114287234949474712599 27291171430852424212068899)
        ·
          refine ⟨40936757146278636318103349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27291171430852424212068899 40936757146278636318103349)
          ·
            refine ⟨3837820982463622154822189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40936757146278636318103349 3837820982463622154822189)
            ·
              refine ⟨1439182868423858308058321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3837820982463622154822189 1439182868423858308058321)
              ·
                refine ⟨1079387151317893731043741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1439182868423858308058321 1079387151317893731043741)
                ·
                  refine ⟨404770181744210149141403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1079387151317893731043741 404770181744210149141403)
                  ·
                    rfl

theorem cell21_1773646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 3, 2, 3].length) (baseStart_1773646 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1773646 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1773646 prefixEnd_1773646 := by exact prefixLift 1773646
  have htrace : WordTrace (prefixWord ++ tailWord_1773646) baseStart_1773646 baseEnd_1773646 := by
    simpa [prefixWord, tailWord_1773646, baseEnd_1773646] using wordTrace_append hprefix tailTrace_1773646
  have hstable : (prefixWord ++ tailWord_1773646).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773646).length < 2 ^ (prefixWord ++ tailWord_1773646).sum := by decide
  have hdescent : baseEnd_1773646 < baseStart_1773646 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773660 : List Nat := [2, 2, 4, 1, 1, 2, 4, 1, 4]
def baseStart_1773660 : Nat := 118140960795 + 1773660 * 2 ^ 59
def prefixEnd_1773660 : Nat := 4983230072969 + 3 ^ 40 * 1773660 * 2
def baseEnd_1773660 : Nat := 404773376734949235908041

theorem tailTrace_1773660 : CollatzResearch.WordTrace tailWord_1773660 prefixEnd_1773660 404773376734949235908041 := by
  unfold tailWord_1773660
  simp only [CollatzResearch.WordTrace]
  refine ⟨32345347377170105928327217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43127129836226807904436289 32345347377170105928327217)
  ·
    refine ⟨24259010532877579446245413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32345347377170105928327217 24259010532877579446245413)
    ·
      refine ⟨4548564474914546146171015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24259010532877579446245413 4548564474914546146171015)
      ·
        refine ⟨6822846712371819219256523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4548564474914546146171015 6822846712371819219256523)
        ·
          refine ⟨10234270068557728828884785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6822846712371819219256523 10234270068557728828884785)
          ·
            refine ⟨7675702551418296621663589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10234270068557728828884785 7675702551418296621663589)
            ·
              refine ⟨1439194228390930616561923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7675702551418296621663589 1439194228390930616561923)
              ·
                refine ⟨2158791342586395924842885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1439194228390930616561923 2158791342586395924842885)
                ·
                  refine ⟨404773376734949235908041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2158791342586395924842885 404773376734949235908041)
                  ·
                    rfl

theorem cell21_1773660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 4, 1, 4].length) (baseStart_1773660 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1773660 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1773660 prefixEnd_1773660 := by exact prefixLift 1773660
  have htrace : WordTrace (prefixWord ++ tailWord_1773660) baseStart_1773660 baseEnd_1773660 := by
    simpa [prefixWord, tailWord_1773660, baseEnd_1773660] using wordTrace_append hprefix tailTrace_1773660
  have hstable : (prefixWord ++ tailWord_1773660).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773660).length < 2 ^ (prefixWord ++ tailWord_1773660).sum := by decide
  have hdescent : baseEnd_1773660 < baseStart_1773660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773671 : List Nat := [1, 1, 5, 1, 1, 2, 2, 1, 7]
def baseStart_1773671 : Nat := 118140960795 + 1773671 * 2 ^ 59
def prefixEnd_1773671 : Nat := 4983230072969 + 3 ^ 40 * 1773671 * 2
def baseEnd_1773671 : Nat := 404775887084815661224685

theorem tailTrace_1773671 : CollatzResearch.WordTrace tailWord_1773671 prefixEnd_1773671 404775887084815661224685 := by
  unfold tailWord_1773671
  simp only [CollatzResearch.WordTrace]
  refine ⟨64691095957300360735304867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43127397304866907156869911 64691095957300360735304867)
  ·
    refine ⟨97036643935950541102957301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64691095957300360735304867 97036643935950541102957301)
    ·
      refine ⟨9097185368995363228402247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 97036643935950541102957301 9097185368995363228402247)
      ·
        refine ⟨13645778053493044842603371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9097185368995363228402247 13645778053493044842603371)
        ·
          refine ⟨20468667080239567263905057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13645778053493044842603371 20468667080239567263905057)
          ·
            refine ⟨15351500310179675447928793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20468667080239567263905057 15351500310179675447928793)
            ·
              refine ⟨11513625232634756585946595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15351500310179675447928793 11513625232634756585946595)
              ·
                refine ⟨17270437848952134878919893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11513625232634756585946595 17270437848952134878919893)
                ·
                  refine ⟨404775887084815661224685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17270437848952134878919893 404775887084815661224685)
                  ·
                    rfl

theorem cell21_1773671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 7].length) (baseStart_1773671 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1773671 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1773671 prefixEnd_1773671 := by exact prefixLift 1773671
  have htrace : WordTrace (prefixWord ++ tailWord_1773671) baseStart_1773671 baseEnd_1773671 := by
    simpa [prefixWord, tailWord_1773671, baseEnd_1773671] using wordTrace_append hprefix tailTrace_1773671
  have hstable : (prefixWord ++ tailWord_1773671).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773671).length < 2 ^ (prefixWord ++ tailWord_1773671).sum := by decide
  have hdescent : baseEnd_1773671 < baseStart_1773671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773688 : List Nat := [2, 1, 2, 1, 1, 1, 3, 7, 3]
def baseStart_1773688 : Nat := 118140960795 + 1773688 * 2 ^ 59
def prefixEnd_1773688 : Nat := 4983230072969 + 3 ^ 40 * 1773688 * 2
def baseEnd_1773688 : Nat := 404779766716427409441317

theorem tailTrace_1773688 : CollatzResearch.WordTrace tailWord_1773688 prefixEnd_1773688 404779766716427409441317 := by
  unfold tailWord_1773688
  simp only [CollatzResearch.WordTrace]
  refine ⟨32345857999119386319336859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43127810665492515092449145 32345857999119386319336859)
  ·
    refine ⟨48518786998679079479005289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32345857999119386319336859 48518786998679079479005289)
    ·
      refine ⟨36389090249009309609253967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48518786998679079479005289 36389090249009309609253967)
      ·
        refine ⟨54583635373513964413880951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36389090249009309609253967 54583635373513964413880951)
        ·
          refine ⟨81875453060270946620821427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54583635373513964413880951 81875453060270946620821427)
          ·
            refine ⟨122813179590406419931232141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81875453060270946620821427 122813179590406419931232141)
            ·
              refine ⟨46054942346402407474212053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122813179590406419931232141 46054942346402407474212053)
              ·
                refine ⟨1079412711243806425176845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 46054942346402407474212053 1079412711243806425176845)
                ·
                  refine ⟨404779766716427409441317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1079412711243806425176845 404779766716427409441317)
                  ·
                    rfl

theorem cell21_1773688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 7, 3].length) (baseStart_1773688 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1773688 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1773688 prefixEnd_1773688 := by exact prefixLift 1773688
  have htrace : WordTrace (prefixWord ++ tailWord_1773688) baseStart_1773688 baseEnd_1773688 := by
    simpa [prefixWord, tailWord_1773688, baseEnd_1773688] using wordTrace_append hprefix tailTrace_1773688
  have hstable : (prefixWord ++ tailWord_1773688).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773688).length < 2 ^ (prefixWord ++ tailWord_1773688).sum := by decide
  have hdescent : baseEnd_1773688 < baseStart_1773688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773733 : List Nat := [1, 3, 1, 2, 1, 3, 5, 5]
def baseStart_1773733 : Nat := 118140960795 + 1773733 * 2 ^ 59
def prefixEnd_1773733 : Nat := 4983230072969 + 3 ^ 40 * 1773733 * 2
def baseEnd_1773733 : Nat := 134930012109839110397075

theorem tailTrace_1773733 : CollatzResearch.WordTrace tailWord_1773733 prefixEnd_1773733 134930012109839110397075 := by
  unfold tailWord_1773733
  simp only [CollatzResearch.WordTrace]
  refine ⟨64693357283075745324061853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43128904855383830216041235 64693357283075745324061853)
  ·
    refine ⟨24260008981153404496523195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64693357283075745324061853 24260008981153404496523195)
    ·
      refine ⟨36390013471730106744784793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24260008981153404496523195 36390013471730106744784793)
      ·
        refine ⟨27292510103797580058588595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36390013471730106744784793 27292510103797580058588595)
        ·
          refine ⟨40938765155696370087882893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27292510103797580058588595 40938765155696370087882893)
          ·
            refine ⟨15352036933386138782956085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40938765155696370087882893 15352036933386138782956085)
            ·
              refine ⟨1439253462504950510902133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15352036933386138782956085 1439253462504950510902133)
              ·
                refine ⟨134930012109839110397075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1439253462504950510902133 134930012109839110397075)
                ·
                  rfl

theorem cell21_1773733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 5, 5].length) (baseStart_1773733 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1773733 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1773733 prefixEnd_1773733 := by exact prefixLift 1773733
  have htrace : WordTrace (prefixWord ++ tailWord_1773733) baseStart_1773733 baseEnd_1773733 := by
    simpa [prefixWord, tailWord_1773733, baseEnd_1773733] using wordTrace_append hprefix tailTrace_1773733
  have hstable : (prefixWord ++ tailWord_1773733).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773733).length < 2 ^ (prefixWord ++ tailWord_1773733).sum := by decide
  have hdescent : baseEnd_1773733 < baseStart_1773733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773764 : List Nat := [2, 3, 3, 1, 2, 1, 1, 3, 5]
def baseStart_1773764 : Nat := 118140960795 + 1773764 * 2 ^ 59
def prefixEnd_1773764 : Nat := 4983230072969 + 3 ^ 40 * 1773764 * 2
def baseEnd_1773764 : Nat := 404797110951868166174495

theorem tailTrace_1773764 : CollatzResearch.WordTrace tailWord_1773764 prefixEnd_1773764 404797110951868166174495 := by
  unfold tailWord_1773764
  simp only [CollatzResearch.WordTrace]
  refine ⟨32347243972981718809220173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43129658630642291745626897 32347243972981718809220173)
  ·
    refine ⟨12130216489868144553457565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32347243972981718809220173 12130216489868144553457565)
    ·
      refine ⟨4548831183700554207546587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12130216489868144553457565 4548831183700554207546587)
      ·
        refine ⟨6823246775550831311319881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4548831183700554207546587 6823246775550831311319881)
        ·
          refine ⟨5117435081663123483489911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6823246775550831311319881 5117435081663123483489911)
          ·
            refine ⟨7676152622494685225234867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5117435081663123483489911 7676152622494685225234867)
            ·
              refine ⟨11514228933742027837852301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7676152622494685225234867 11514228933742027837852301)
              ·
                refine ⟨4317835850153260439194613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11514228933742027837852301 4317835850153260439194613)
                ·
                  refine ⟨404797110951868166174495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4317835850153260439194613 404797110951868166174495)
                  ·
                    rfl

theorem cell21_1773764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 3, 5].length) (baseStart_1773764 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1773764 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1773764 prefixEnd_1773764 := by exact prefixLift 1773764
  have htrace : WordTrace (prefixWord ++ tailWord_1773764) baseStart_1773764 baseEnd_1773764 := by
    simpa [prefixWord, tailWord_1773764, baseEnd_1773764] using wordTrace_append hprefix tailTrace_1773764
  have hstable : (prefixWord ++ tailWord_1773764).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773764).length < 2 ^ (prefixWord ++ tailWord_1773764).sum := by decide
  have hdescent : baseEnd_1773764 < baseStart_1773764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773792 : List Nat := [2, 1, 1, 3, 1, 3, 3, 7]
def baseStart_1773792 : Nat := 118140960795 + 1773792 * 2 ^ 59
def prefixEnd_1773792 : Nat := 4983230072969 + 3 ^ 40 * 1773792 * 2
def baseEnd_1773792 : Nat := 134934500311115446569257

theorem tailTrace_1773792 : CollatzResearch.WordTrace tailWord_1773792 prefixEnd_1773792 134934500311115446569257 := by
  unfold tailWord_1773792
  simp only [CollatzResearch.WordTrace]
  refine ⟨32347754594930999200229815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43130339459907998933639753 32347754594930999200229815)
  ·
    refine ⟨48521631892396498800344723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32347754594930999200229815 48521631892396498800344723)
    ·
      refine ⟨72782447838594748200517085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48521631892396498800344723 72782447838594748200517085)
      ·
        refine ⟨27293417939473030575193907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72782447838594748200517085 27293417939473030575193907)
        ·
          refine ⟨40940126909209545862790861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27293417939473030575193907 40940126909209545862790861)
          ·
            refine ⟨15352547590953579698546573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40940126909209545862790861 15352547590953579698546573)
            ·
              refine ⟨5757205346607592386954965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15352547590953579698546573 5757205346607592386954965)
              ·
                refine ⟨134934500311115446569257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5757205346607592386954965 134934500311115446569257)
                ·
                  rfl

theorem cell21_1773792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 7].length) (baseStart_1773792 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1773792 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1773792 prefixEnd_1773792 := by exact prefixLift 1773792
  have htrace : WordTrace (prefixWord ++ tailWord_1773792) baseStart_1773792 baseEnd_1773792 := by
    simpa [prefixWord, tailWord_1773792, baseEnd_1773792] using wordTrace_append hprefix tailTrace_1773792
  have hstable : (prefixWord ++ tailWord_1773792).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773792).length < 2 ^ (prefixWord ++ tailWord_1773792).sum := by decide
  have hdescent : baseEnd_1773792 < baseStart_1773792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773826 : List Nat := [3, 4, 1, 1, 2, 2, 2, 6]
def baseStart_1773826 : Nat := 118140960795 + 1773826 * 2 ^ 59
def prefixEnd_1773826 : Nat := 4983230072969 + 3 ^ 40 * 1773826 * 2
def baseEnd_1773826 : Nat := 134937086732189945380345

theorem tailTrace_1773826 : CollatzResearch.WordTrace tailWord_1773826 prefixEnd_1773826 134937086732189945380345 := by
  unfold tailWord_1773826
  simp only [CollatzResearch.WordTrace]
  refine ⟨16174187317934705551799333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43131166181159214804798221 16174187317934705551799333)
  ·
    refine ⟨3032660122112757290962375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16174187317934705551799333 3032660122112757290962375)
    ·
      refine ⟨4548990183169135936443563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3032660122112757290962375 4548990183169135936443563)
      ·
        refine ⟨6823485274753703904665345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4548990183169135936443563 6823485274753703904665345)
        ·
          refine ⟨5117613956065277928499009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6823485274753703904665345 5117613956065277928499009)
          ·
            refine ⟨3838210467048958446374257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5117613956065277928499009 3838210467048958446374257)
            ·
              refine ⟨2878657850286718834780693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3838210467048958446374257 2878657850286718834780693)
              ·
                refine ⟨134937086732189945380345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2878657850286718834780693 134937086732189945380345)
                ·
                  rfl

theorem cell21_1773826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 6].length) (baseStart_1773826 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1773826 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1773826 prefixEnd_1773826 := by exact prefixLift 1773826
  have htrace : WordTrace (prefixWord ++ tailWord_1773826) baseStart_1773826 baseEnd_1773826 := by
    simpa [prefixWord, tailWord_1773826, baseEnd_1773826] using wordTrace_append hprefix tailTrace_1773826
  have hstable : (prefixWord ++ tailWord_1773826).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773826).length < 2 ^ (prefixWord ++ tailWord_1773826).sum := by decide
  have hdescent : baseEnd_1773826 < baseStart_1773826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773913 : List Nat := [1, 2, 1, 2, 2, 2, 1, 4, 6]
def baseStart_1773913 : Nat := 118140960795 + 1773913 * 2 ^ 59
def prefixEnd_1773913 : Nat := 4983230072969 + 3 ^ 40 * 1773913 * 2
def baseEnd_1773913 : Nat := 404831114781877018190857

theorem tailTrace_1773913 : CollatzResearch.WordTrace tailWord_1773913 prefixEnd_1773913 404831114781877018190857 := by
  unfold tailWord_1773913
  simp only [CollatzResearch.WordTrace]
  refine ⟨64699922422423636065614393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43133281614949090710409595 64699922422423636065614393)
  ·
    refine ⟨48524941816817727049210795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64699922422423636065614393 48524941816817727049210795)
    ·
      refine ⟨72787412725226590573816193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48524941816817727049210795 72787412725226590573816193)
      ·
        refine ⟨54590559543919942930362145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72787412725226590573816193 54590559543919942930362145)
        ·
          refine ⟨40942919657939957197771609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54590559543919942930362145 40942919657939957197771609)
          ·
            refine ⟨30707189743454967898328707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40942919657939957197771609 30707189743454967898328707)
            ·
              refine ⟨46060784615182451847493061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30707189743454967898328707 46060784615182451847493061)
              ·
                refine ⟨8636397115346709721404949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46060784615182451847493061 8636397115346709721404949)
                ·
                  refine ⟨404831114781877018190857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8636397115346709721404949 404831114781877018190857)
                  ·
                    rfl

theorem cell21_1773913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 4, 6].length) (baseStart_1773913 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1773913 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1773913 prefixEnd_1773913 := by exact prefixLift 1773913
  have htrace : WordTrace (prefixWord ++ tailWord_1773913) baseStart_1773913 baseEnd_1773913 := by
    simpa [prefixWord, tailWord_1773913, baseEnd_1773913] using wordTrace_append hprefix tailTrace_1773913
  have hstable : (prefixWord ++ tailWord_1773913).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773913).length < 2 ^ (prefixWord ++ tailWord_1773913).sum := by decide
  have hdescent : baseEnd_1773913 < baseStart_1773913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773947 : List Nat := [1, 1, 1, 1, 1, 8, 3, 1, 4]
def baseStart_1773947 : Nat := 118140960795 + 1773947 * 2 ^ 59
def prefixEnd_1773947 : Nat := 4983230072969 + 3 ^ 40 * 1773947 * 2
def baseEnd_1773947 : Nat := 404838874045100514624121

theorem tailTrace_1773947 : CollatzResearch.WordTrace tailWord_1773947 prefixEnd_1773947 404838874045100514624121 := by
  unfold tailWord_1773947
  simp only [CollatzResearch.WordTrace]
  refine ⟨64701162504300459872352095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43134108336200306581568063 64701162504300459872352095)
  ·
    refine ⟨97051743756450689808528143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64701162504300459872352095 97051743756450689808528143)
    ·
      refine ⟨145577615634676034712792215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97051743756450689808528143 145577615634676034712792215)
      ·
        refine ⟨218366423452014052069188323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145577615634676034712792215 218366423452014052069188323)
        ·
          refine ⟨327549635178021078103782485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218366423452014052069188323 327549635178021078103782485)
          ·
            refine ⟨3838472287242434509028701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 327549635178021078103782485 3838472287242434509028701)
            ·
              refine ⟨1439427107715912940885763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3838472287242434509028701 1439427107715912940885763)
              ·
                refine ⟨2159140661573869411328645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1439427107715912940885763 2159140661573869411328645)
                ·
                  refine ⟨404838874045100514624121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2159140661573869411328645 404838874045100514624121)
                  ·
                    rfl

theorem cell21_1773947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 3, 1, 4].length) (baseStart_1773947 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1773947 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1773947 prefixEnd_1773947 := by exact prefixLift 1773947
  have htrace : WordTrace (prefixWord ++ tailWord_1773947) baseStart_1773947 baseEnd_1773947 := by
    simpa [prefixWord, tailWord_1773947, baseEnd_1773947] using wordTrace_append hprefix tailTrace_1773947
  have hstable : (prefixWord ++ tailWord_1773947).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773947).length < 2 ^ (prefixWord ++ tailWord_1773947).sum := by decide
  have hdescent : baseEnd_1773947 < baseStart_1773947 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773961 : List Nat := [1, 2, 1, 1, 6, 1, 4, 5]
def baseStart_1773961 : Nat := 118140960795 + 1773961 * 2 ^ 59
def prefixEnd_1773961 : Nat := 4983230072969 + 3 ^ 40 * 1773961 * 2
def baseEnd_1773961 : Nat := 134947356345279867130253

theorem tailTrace_1773961 : CollatzResearch.WordTrace tailWord_1773961 prefixEnd_1773961 134947356345279867130253 := by
  unfold tailWord_1773961
  simp only [CollatzResearch.WordTrace]
  refine ⟨64701673126249740263361737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43134448750833160175574491 64701673126249740263361737)
  ·
    refine ⟨48526254844687305197521303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64701673126249740263361737 48526254844687305197521303)
    ·
      refine ⟨72789382267030957796281955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48526254844687305197521303 72789382267030957796281955)
      ·
        refine ⟨109184073400546436694422933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72789382267030957796281955 109184073400546436694422933)
        ·
          refine ⟨5118003440650614220051075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 109184073400546436694422933 5118003440650614220051075)
          ·
            refine ⟨7677005160975921330076613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5118003440650614220051075 7677005160975921330076613)
            ·
              refine ⟨1439438467682985249389365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7677005160975921330076613 1439438467682985249389365)
              ·
                refine ⟨134947356345279867130253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1439438467682985249389365 134947356345279867130253)
                ·
                  rfl

theorem cell21_1773961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 4, 5].length) (baseStart_1773961 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1773961 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1773961 prefixEnd_1773961 := by exact prefixLift 1773961
  have htrace : WordTrace (prefixWord ++ tailWord_1773961) baseStart_1773961 baseEnd_1773961 := by
    simpa [prefixWord, tailWord_1773961, baseEnd_1773961] using wordTrace_append hprefix tailTrace_1773961
  have hstable : (prefixWord ++ tailWord_1773961).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773961).length < 2 ^ (prefixWord ++ tailWord_1773961).sum := by decide
  have hdescent : baseEnd_1773961 < baseStart_1773961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773989 : List Nat := [1, 3, 1, 2, 1, 1, 3, 3, 6]
def baseStart_1773989 : Nat := 118140960795 + 1773989 * 2 ^ 59
def prefixEnd_1773989 : Nat := 4983230072969 + 3 ^ 40 * 1773989 * 2
def baseEnd_1773989 : Nat := 404848459017317774924035

theorem tailTrace_1773989 : CollatzResearch.WordTrace tailWord_1773989 prefixEnd_1773989 404848459017317774924035 := by
  unfold tailWord_1773989
  simp only [CollatzResearch.WordTrace]
  refine ⟨64702694370148301045381021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43135129580098867363587347 64702694370148301045381021)
  ·
    refine ⟨24263510388805612892017883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64702694370148301045381021 24263510388805612892017883)
    ·
      refine ⟨36395265583208419338026825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24263510388805612892017883 36395265583208419338026825)
      ·
        refine ⟨27296449187406314503520119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36395265583208419338026825 27296449187406314503520119)
        ·
          refine ⟨40944673781109471755280179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27296449187406314503520119 40944673781109471755280179)
          ·
            refine ⟨61417010671664207632920269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40944673781109471755280179 61417010671664207632920269)
            ·
              refine ⟨23031379001874077862345101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61417010671664207632920269 23031379001874077862345101)
              ·
                refine ⟨8636767125702779198379413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23031379001874077862345101 8636767125702779198379413)
                ·
                  refine ⟨404848459017317774924035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8636767125702779198379413 404848459017317774924035)
                  ·
                    rfl

theorem cell21_1773989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 3, 6].length) (baseStart_1773989 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1773989 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1773989 prefixEnd_1773989 := by exact prefixLift 1773989
  have htrace : WordTrace (prefixWord ++ tailWord_1773989) baseStart_1773989 baseEnd_1773989 := by
    simpa [prefixWord, tailWord_1773989, baseEnd_1773989] using wordTrace_append hprefix tailTrace_1773989
  have hstable : (prefixWord ++ tailWord_1773989).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773989).length < 2 ^ (prefixWord ++ tailWord_1773989).sum := by decide
  have hdescent : baseEnd_1773989 < baseStart_1773989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774144 : List Nat := [2, 1, 1, 2, 2, 2, 5, 3, 3]
def baseStart_1774144 : Nat := 118140960795 + 1774144 * 2 ^ 59
def prefixEnd_1774144 : Nat := 4983230072969 + 3 ^ 40 * 1774144 * 2
def baseEnd_1774144 : Nat := 404883832129071949840385

theorem tailTrace_1774144 : CollatzResearch.WordTrace tailWord_1774144 prefixEnd_1774144 404883832129071949840385 := by
  unfold tailWord_1774144
  simp only [CollatzResearch.WordTrace]
  refine ⟨32354173842293381258636743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43138898456391175011515657 32354173842293381258636743)
  ·
    refine ⟨48531260763440071887955115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32354173842293381258636743 48531260763440071887955115)
    ·
      refine ⟨72796891145160107831932673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48531260763440071887955115 72796891145160107831932673)
      ·
        refine ⟨54597668358870080873949505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72796891145160107831932673 54597668358870080873949505)
        ·
          refine ⟨40948251269152560655462129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54597668358870080873949505 40948251269152560655462129)
          ·
            refine ⟨30711188451864420491596597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40948251269152560655462129 30711188451864420491596597)
            ·
              refine ⟨2879173917362289421087181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30711188451864420491596597 2879173917362289421087181)
              ·
                refine ⟨1079690219010858532907693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2879173917362289421087181 1079690219010858532907693)
                ·
                  refine ⟨404883832129071949840385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1079690219010858532907693 404883832129071949840385)
                  ·
                    rfl

theorem cell21_1774144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 3, 3].length) (baseStart_1774144 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1774144 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1774144 prefixEnd_1774144 := by exact prefixLift 1774144
  have htrace : WordTrace (prefixWord ++ tailWord_1774144) baseStart_1774144 baseEnd_1774144 := by
    simpa [prefixWord, tailWord_1774144, baseEnd_1774144] using wordTrace_append hprefix tailTrace_1774144
  have hstable : (prefixWord ++ tailWord_1774144).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774144).length < 2 ^ (prefixWord ++ tailWord_1774144).sum := by decide
  have hdescent : baseEnd_1774144 < baseStart_1774144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774155 : List Nat := [1, 1, 1, 1, 3, 1, 13]
def baseStart_1774155 : Nat := 118140960795 + 1774155 * 2 ^ 59
def prefixEnd_1774155 : Nat := 4983230072969 + 3 ^ 40 * 1774155 * 2
def baseEnd_1774155 : Nat := 44987371386548708350781

theorem tailTrace_1774155 : CollatzResearch.WordTrace tailWord_1774155 prefixEnd_1774155 44987371386548708350781 := by
  unfold tailWord_1774155
  simp only [CollatzResearch.WordTrace]
  refine ⟨64708748887546911395923919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43139165925031274263949279 64708748887546911395923919)
  ·
    refine ⟨97063123331320367093885879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64708748887546911395923919 97063123331320367093885879)
    ·
      refine ⟨145594684996980550640828819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97063123331320367093885879 145594684996980550640828819)
      ·
        refine ⟨218392027495470825961243229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145594684996980550640828819 218392027495470825961243229)
        ·
          refine ⟨81897010310801559735466211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 218392027495470825961243229 81897010310801559735466211)
          ·
            refine ⟨122845515466202339603199317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81897010310801559735466211 122845515466202339603199317)
            ·
              refine ⟨44987371386548708350781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 122845515466202339603199317 44987371386548708350781)
              ·
                rfl

theorem cell21_1774155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 13].length) (baseStart_1774155 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1774155 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1774155 prefixEnd_1774155 := by exact prefixLift 1774155
  have htrace : WordTrace (prefixWord ++ tailWord_1774155) baseStart_1774155 baseEnd_1774155 := by
    simpa [prefixWord, tailWord_1774155, baseEnd_1774155] using wordTrace_append hprefix tailTrace_1774155
  have hstable : (prefixWord ++ tailWord_1774155).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774155).length < 2 ^ (prefixWord ++ tailWord_1774155).sum := by decide
  have hdescent : baseEnd_1774155 < baseStart_1774155 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774161 : List Nat := [1, 2, 2, 1, 3, 4, 3, 2, 3]
def baseStart_1774161 : Nat := 118140960795 + 1774161 * 2 ^ 59
def prefixEnd_1774161 : Nat := 4983230072969 + 3 ^ 40 * 1774161 * 2
def baseEnd_1774161 : Nat := 404887711760683698057017

theorem tailTrace_1774161 : CollatzResearch.WordTrace tailWord_1774161 prefixEnd_1774161 404887711760683698057017 := by
  unfold tailWord_1774161
  simp only [CollatzResearch.WordTrace]
  refine ⟨64708967725525174420642337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43139311817016782947094891 64708967725525174420642337)
  ·
    refine ⟨48531725794143880815481753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64708967725525174420642337 48531725794143880815481753)
    ·
      refine ⟨36398794345607910611611315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48531725794143880815481753 36398794345607910611611315)
      ·
        refine ⟨54598191518411865917416973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36398794345607910611611315 54598191518411865917416973)
        ·
          refine ⟨20474321819404449719031365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54598191518411865917416973 20474321819404449719031365)
          ·
            refine ⟨3838935341138334322318381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20474321819404449719031365 3838935341138334322318381)
            ·
              refine ⟨1439600752926875370869393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3838935341138334322318381 1439600752926875370869393)
              ·
                refine ⟨1079700564695156528152045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1439600752926875370869393 1079700564695156528152045)
                ·
                  refine ⟨404887711760683698057017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1079700564695156528152045 404887711760683698057017)
                  ·
                    rfl

theorem cell21_1774161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 3, 2, 3].length) (baseStart_1774161 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1774161 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1774161 prefixEnd_1774161 := by exact prefixLift 1774161
  have htrace : WordTrace (prefixWord ++ tailWord_1774161) baseStart_1774161 baseEnd_1774161 := by
    simpa [prefixWord, tailWord_1774161, baseEnd_1774161] using wordTrace_append hprefix tailTrace_1774161
  have hstable : (prefixWord ++ tailWord_1774161).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774161).length < 2 ^ (prefixWord ++ tailWord_1774161).sum := by decide
  have hdescent : baseEnd_1774161 < baseStart_1774161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774254 : List Nat := [4, 1, 4, 1, 1, 2, 2, 3, 3]
def baseStart_1774254 : Nat := 118140960795 + 1774254 * 2 ^ 59
def prefixEnd_1774254 : Nat := 4983230072969 + 3 ^ 40 * 1774254 * 2
def baseEnd_1774254 : Nat := 404908935627736203006827

theorem tailTrace_1774254 : CollatzResearch.WordTrace tailWord_1774254 prefixEnd_1774254 404908935627736203006827 := by
  unfold tailWord_1774254
  simp only [CollatzResearch.WordTrace]
  refine ⟨8089044964273531412972227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43141573142792167535851877 8089044964273531412972227)
  ·
    refine ⟨12133567446410297119458341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8089044964273531412972227 12133567446410297119458341)
    ·
      refine ⟨2275043896201930709898439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12133567446410297119458341 2275043896201930709898439)
      ·
        refine ⟨3412565844302896064847659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2275043896201930709898439 3412565844302896064847659)
        ·
          refine ⟨5118848766454344097271489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3412565844302896064847659 5118848766454344097271489)
          ·
            refine ⟨3839136574840758072953617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5118848766454344097271489 3839136574840758072953617)
            ·
              refine ⟨2879352431130568554715213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3839136574840758072953617 2879352431130568554715213)
              ·
                refine ⟨1079757161673963208018205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2879352431130568554715213 1079757161673963208018205)
                ·
                  refine ⟨404908935627736203006827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1079757161673963208018205 404908935627736203006827)
                  ·
                    rfl

theorem cell21_1774254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 3, 3].length) (baseStart_1774254 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1774254 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1774254 prefixEnd_1774254 := by exact prefixLift 1774254
  have htrace : WordTrace (prefixWord ++ tailWord_1774254) baseStart_1774254 baseEnd_1774254 := by
    simpa [prefixWord, tailWord_1774254, baseEnd_1774254] using wordTrace_append hprefix tailTrace_1774254
  have hstable : (prefixWord ++ tailWord_1774254).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774254).length < 2 ^ (prefixWord ++ tailWord_1774254).sum := by decide
  have hdescent : baseEnd_1774254 < baseStart_1774254 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774285 : List Nat := [1, 6, 2, 1, 2, 1, 3, 1, 4]
def baseStart_1774285 : Nat := 118140960795 + 1774285 * 2 ^ 59
def prefixEnd_1774285 : Nat := 4983230072969 + 3 ^ 40 * 1774285 * 2
def baseEnd_1774285 : Nat := 404916010250087037990097

theorem tailTrace_1774285 : CollatzResearch.WordTrace tailWord_1774285 prefixEnd_1774285 404916010250087037990097 := by
  unfold tailWord_1774285
  simp only [CollatzResearch.WordTrace]
  refine ⟨64713490377075943598156309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43142326918050629065437539 64713490377075943598156309)
  ·
    refine ⟨3033444861425434856163577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 64713490377075943598156309 3033444861425434856163577)
    ·
      refine ⟨2275083646069076142122683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3033444861425434856163577 2275083646069076142122683)
      ·
        refine ⟨3412625469103614213184025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2275083646069076142122683 3412625469103614213184025)
        ·
          refine ⟨2559469101827710659888019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3412625469103614213184025 2559469101827710659888019)
          ·
            refine ⟨3839203652741565989832029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2559469101827710659888019 3839203652741565989832029)
            ·
              refine ⟨1439701369778087246187011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3839203652741565989832029 1439701369778087246187011)
              ·
                refine ⟨2159552054667130869280517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1439701369778087246187011 2159552054667130869280517)
                ·
                  refine ⟨404916010250087037990097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2159552054667130869280517 404916010250087037990097)
                  ·
                    rfl

theorem cell21_1774285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_1774285 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1774285 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1774285 prefixEnd_1774285 := by exact prefixLift 1774285
  have htrace : WordTrace (prefixWord ++ tailWord_1774285) baseStart_1774285 baseEnd_1774285 := by
    simpa [prefixWord, tailWord_1774285, baseEnd_1774285] using wordTrace_append hprefix tailTrace_1774285
  have hstable : (prefixWord ++ tailWord_1774285).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774285).length < 2 ^ (prefixWord ++ tailWord_1774285).sum := by decide
  have hdescent : baseEnd_1774285 < baseStart_1774285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774386 : List Nat := [3, 2, 1, 1, 3, 1, 4, 2, 4]
def baseStart_1774386 : Nat := 118140960795 + 1774386 * 2 ^ 59
def prefixEnd_1774386 : Nat := 4983230072969 + 3 ^ 40 * 1774386 * 2
def baseEnd_1774386 : Nat := 404939059826133306806557

theorem tailTrace_1774386 : CollatzResearch.WordTrace tailWord_1774386 prefixEnd_1774386 404939059826133306806557 := by
  unfold tailWord_1774386
  simp only [CollatzResearch.WordTrace]
  refine ⟨16179293537427509461895753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43144782766473358565055341 16179293537427509461895753)
  ·
    refine ⟨12134470153070632096421815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16179293537427509461895753 12134470153070632096421815)
    ·
      refine ⟨18201705229605948144632723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12134470153070632096421815 18201705229605948144632723)
      ·
        refine ⟨27302557844408922216949085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18201705229605948144632723 27302557844408922216949085)
        ·
          refine ⟨10238459191653345831355907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27302557844408922216949085 10238459191653345831355907)
          ·
            refine ⟨15357688787480018747033861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10238459191653345831355907 15357688787480018747033861)
            ·
              refine ⟨2879566647652503515068849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15357688787480018747033861 2879566647652503515068849)
              ·
                refine ⟨2159674985739377636301637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2879566647652503515068849 2159674985739377636301637)
                ·
                  refine ⟨404939059826133306806557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2159674985739377636301637 404939059826133306806557)
                  ·
                    rfl

theorem cell21_1774386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 2, 4].length) (baseStart_1774386 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1774386 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1774386 prefixEnd_1774386 := by exact prefixLift 1774386
  have htrace : WordTrace (prefixWord ++ tailWord_1774386) baseStart_1774386 baseEnd_1774386 := by
    simpa [prefixWord, tailWord_1774386, baseEnd_1774386] using wordTrace_append hprefix tailTrace_1774386
  have hstable : (prefixWord ++ tailWord_1774386).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774386).length < 2 ^ (prefixWord ++ tailWord_1774386).sum := by decide
  have hdescent : baseEnd_1774386 < baseStart_1774386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774389 : List Nat := [1, 3, 3, 1, 3, 1, 4, 2, 3]
def baseStart_1774389 : Nat := 118140960795 + 1774389 * 2 ^ 59
def prefixEnd_1774389 : Nat := 4983230072969 + 3 ^ 40 * 1774389 * 2
def baseEnd_1774389 : Nat := 404939744467005968256551

theorem tailTrace_1774389 : CollatzResearch.WordTrace tailWord_1774389 prefixEnd_1774389 404939744467005968256551 := by
  unfold tailWord_1774389
  simp only [CollatzResearch.WordTrace]
  refine ⟨64717283568699169359942221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43144855712466112906628147 64717283568699169359942221)
  ·
    refine ⟨24268981338262188509978333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64717283568699169359942221 24268981338262188509978333)
    ·
      refine ⟨9100868001848320691241875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24268981338262188509978333 9100868001848320691241875)
      ·
        refine ⟨13651302002772481036862813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9100868001848320691241875 13651302002772481036862813)
        ·
          refine ⟨5119238251039680388823555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13651302002772481036862813 5119238251039680388823555)
          ·
            refine ⟨7678857376559520583235333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5119238251039680388823555 7678857376559520583235333)
            ·
              refine ⟨1439785758104910109356625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7678857376559520583235333 1439785758104910109356625)
              ·
                refine ⟨1079839318578682582017469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1439785758104910109356625 1079839318578682582017469)
                ·
                  refine ⟨404939744467005968256551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1079839318578682582017469 404939744467005968256551)
                  ·
                    rfl

theorem cell21_1774389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 4, 2, 3].length) (baseStart_1774389 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1774389 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1774389 prefixEnd_1774389 := by exact prefixLift 1774389
  have htrace : WordTrace (prefixWord ++ tailWord_1774389) baseStart_1774389 baseEnd_1774389 := by
    simpa [prefixWord, tailWord_1774389, baseEnd_1774389] using wordTrace_append hprefix tailTrace_1774389
  have hstable : (prefixWord ++ tailWord_1774389).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774389).length < 2 ^ (prefixWord ++ tailWord_1774389).sum := by decide
  have hdescent : baseEnd_1774389 < baseStart_1774389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774417 : List Nat := [1, 2, 2, 1, 6, 1, 3, 5]
def baseStart_1774417 : Nat := 118140960795 + 1774417 * 2 ^ 59
def prefixEnd_1774417 : Nat := 4983230072969 + 3 ^ 40 * 1774417 * 2
def baseEnd_1774417 : Nat := 134982044816161380596609

theorem tailTrace_1774417 : CollatzResearch.WordTrace tailWord_1774417 prefixEnd_1774417 134982044816161380596609 := by
  unfold tailWord_1774417
  simp only [CollatzResearch.WordTrace]
  refine ⟨64718304812597730141961505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43145536541731820094641003 64718304812597730141961505)
  ·
    refine ⟨48538728609448297606471129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64718304812597730141961505 48538728609448297606471129)
    ·
      refine ⟨36404046457086223204853347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48538728609448297606471129 36404046457086223204853347)
      ·
        refine ⟨54606069685629334807280021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36404046457086223204853347 54606069685629334807280021)
        ·
          refine ⟨2559659516513875069091251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 54606069685629334807280021 2559659516513875069091251)
          ·
            refine ⟨3839489274770812603636877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2559659516513875069091251 3839489274770812603636877)
            ·
              refine ⟨1439808478039054726363829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3839489274770812603636877 1439808478039054726363829)
              ·
                refine ⟨134982044816161380596609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1439808478039054726363829 134982044816161380596609)
                ·
                  rfl

theorem cell21_1774417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 3, 5].length) (baseStart_1774417 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1774417 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1774417 prefixEnd_1774417 := by exact prefixLift 1774417
  have htrace : WordTrace (prefixWord ++ tailWord_1774417) baseStart_1774417 baseEnd_1774417 := by
    simpa [prefixWord, tailWord_1774417, baseEnd_1774417] using wordTrace_append hprefix tailTrace_1774417
  have hstable : (prefixWord ++ tailWord_1774417).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774417).length < 2 ^ (prefixWord ++ tailWord_1774417).sum := by decide
  have hdescent : baseEnd_1774417 < baseStart_1774417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774476 : List Nat := [2, 2, 1, 2, 1, 2, 6, 5]
def baseStart_1774476 : Nat := 118140960795 + 1774476 * 2 ^ 59
def prefixEnd_1774476 : Nat := 4983230072969 + 3 ^ 40 * 1774476 * 2
def baseEnd_1774476 : Nat := 134986533017437716768791

theorem tailTrace_1774476 : CollatzResearch.WordTrace tailWord_1774476 prefixEnd_1774476 134986533017437716768791 := by
  unfold tailWord_1774476
  simp only [CollatzResearch.WordTrace]
  refine ⟨32360228359691991609179641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43146971146255988812239521 32360228359691991609179641)
  ·
    refine ⟨24270171269768993706884731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32360228359691991609179641 24270171269768993706884731)
    ·
      refine ⟨36405256904653490560327097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24270171269768993706884731 36405256904653490560327097)
      ·
        refine ⟨27303942678490117920245323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36405256904653490560327097 27303942678490117920245323)
        ·
          refine ⟨40955914017735176880367985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27303942678490117920245323 40955914017735176880367985)
          ·
            refine ⟨30716935513301382660275989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40955914017735176880367985 30716935513301382660275989)
            ·
              refine ⟨1439856352186002312200437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 30716935513301382660275989 1439856352186002312200437)
              ·
                refine ⟨134986533017437716768791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1439856352186002312200437 134986533017437716768791)
                ·
                  rfl

theorem cell21_1774476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 6, 5].length) (baseStart_1774476 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1774476 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1774476 prefixEnd_1774476 := by exact prefixLift 1774476
  have htrace : WordTrace (prefixWord ++ tailWord_1774476) baseStart_1774476 baseEnd_1774476 := by
    simpa [prefixWord, tailWord_1774476, baseEnd_1774476] using wordTrace_append hprefix tailTrace_1774476
  have hstable : (prefixWord ++ tailWord_1774476).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774476).length < 2 ^ (prefixWord ++ tailWord_1774476).sum := by decide
  have hdescent : baseEnd_1774476 < baseStart_1774476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774482 : List Nat := [3, 2, 3, 2, 2, 2, 1, 3, 3]
def baseStart_1774482 : Nat := 118140960795 + 1774482 * 2 ^ 59
def prefixEnd_1774482 : Nat := 4983230072969 + 3 ^ 40 * 1774482 * 2
def baseEnd_1774482 : Nat := 404960968334058473206361

theorem tailTrace_1774482 : CollatzResearch.WordTrace tailWord_1774482 prefixEnd_1774482 404960968334058473206361 := by
  unfold tailWord_1774482
  simp only [CollatzResearch.WordTrace]
  refine ⟨16180168889340561560769425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43147117038241497495385133 16180168889340561560769425)
  ·
    refine ⟨12135126667005421170577069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16180168889340561560769425 12135126667005421170577069)
    ·
      refine ⟨4550672500127032938966401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12135126667005421170577069 4550672500127032938966401)
      ·
        refine ⟨3413004375095274704224801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4550672500127032938966401 3413004375095274704224801)
        ·
          refine ⟨2559753281321456028168601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3413004375095274704224801 2559753281321456028168601)
          ·
            refine ⟨1919814960991092021126451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2559753281321456028168601 1919814960991092021126451)
            ·
              refine ⟨2879722441486638031689677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1919814960991092021126451 2879722441486638031689677)
              ·
                refine ⟨1079895915557489261883629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2879722441486638031689677 1079895915557489261883629)
                ·
                  refine ⟨404960968334058473206361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1079895915557489261883629 404960968334058473206361)
                  ·
                    rfl

theorem cell21_1774482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 3, 3].length) (baseStart_1774482 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1774482 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1774482 prefixEnd_1774482 := by exact prefixLift 1774482
  have htrace : WordTrace (prefixWord ++ tailWord_1774482) baseStart_1774482 baseEnd_1774482 := by
    simpa [prefixWord, tailWord_1774482, baseEnd_1774482] using wordTrace_append hprefix tailTrace_1774482
  have hstable : (prefixWord ++ tailWord_1774482).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774482).length < 2 ^ (prefixWord ++ tailWord_1774482).sum := by decide
  have hdescent : baseEnd_1774482 < baseStart_1774482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774535 : List Nat := [1, 1, 4, 1, 1, 2, 4, 7]
def baseStart_1774535 : Nat := 118140960795 + 1774535 * 2 ^ 59
def prefixEnd_1774535 : Nat := 4983230072969 + 3 ^ 40 * 1774535 * 2
def baseEnd_1774535 : Nat := 134991021218714052940973

theorem tailTrace_1774535 : CollatzResearch.WordTrace tailWord_1774535 prefixEnd_1774535 134991021218714052940973 := by
  unfold tailWord_1774535
  simp only [CollatzResearch.WordTrace]
  refine ⟨64722608626170236294757059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43148405750780157529838039 64722608626170236294757059)
  ·
    refine ⟨97083912939255354442135589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64722608626170236294757059 97083912939255354442135589)
    ·
      refine ⟨18203233676110378957900423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97083912939255354442135589 18203233676110378957900423)
      ·
        refine ⟨27304850514165568436850635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18203233676110378957900423 27304850514165568436850635)
        ·
          refine ⟨40957275771248352655275953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27304850514165568436850635 40957275771248352655275953)
          ·
            refine ⟨30717956828436264491456965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40957275771248352655275953 30717956828436264491456965)
            ·
              refine ⟨5759616905331799592148181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30717956828436264491456965 5759616905331799592148181)
              ·
                refine ⟨134991021218714052940973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5759616905331799592148181 134991021218714052940973)
                ·
                  rfl

theorem cell21_1774535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 7].length) (baseStart_1774535 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1774535 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1774535 prefixEnd_1774535 := by exact prefixLift 1774535
  have htrace : WordTrace (prefixWord ++ tailWord_1774535) baseStart_1774535 baseEnd_1774535 := by
    simpa [prefixWord, tailWord_1774535, baseEnd_1774535] using wordTrace_append hprefix tailTrace_1774535
  have hstable : (prefixWord ++ tailWord_1774535).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774535).length < 2 ^ (prefixWord ++ tailWord_1774535).sum := by decide
  have hdescent : baseEnd_1774535 < baseStart_1774535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774600 : List Nat := [2, 1, 3, 2, 1, 4, 2, 3, 3]
def baseStart_1774600 : Nat := 118140960795 + 1774600 * 2 ^ 59
def prefixEnd_1774600 : Nat := 4983230072969 + 3 ^ 40 * 1774600 * 2
def baseEnd_1774600 : Nat := 404987897541716490239453

theorem tailTrace_1774600 : CollatzResearch.WordTrace tailWord_1774600 prefixEnd_1774600 404987897541716490239453 := by
  unfold tailWord_1774600
  simp only [CollatzResearch.WordTrace]
  refine ⟨32362489685467376197936627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43149986247289834930582169 32362489685467376197936627)
  ·
    refine ⟨48543734528201064296904941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32362489685467376197936627 48543734528201064296904941)
    ·
      refine ⟨18203900448075399111339353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48543734528201064296904941 18203900448075399111339353)
      ·
        refine ⟨13652925336056549333504515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18203900448075399111339353 13652925336056549333504515)
        ·
          refine ⟨20479388004084824000256773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13652925336056549333504515 20479388004084824000256773)
          ·
            refine ⟨3839885250765904500048145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20479388004084824000256773 3839885250765904500048145)
            ·
              refine ⟨2879913938074428375036109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3839885250765904500048145 2879913938074428375036109)
              ·
                refine ⟨1079967726777910640638541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2879913938074428375036109 1079967726777910640638541)
                ·
                  refine ⟨404987897541716490239453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1079967726777910640638541 404987897541716490239453)
                  ·
                    rfl

theorem cell21_1774600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 3, 3].length) (baseStart_1774600 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1774600 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1774600 prefixEnd_1774600 := by exact prefixLift 1774600
  have htrace : WordTrace (prefixWord ++ tailWord_1774600) baseStart_1774600 baseEnd_1774600 := by
    simpa [prefixWord, tailWord_1774600, baseEnd_1774600] using wordTrace_append hprefix tailTrace_1774600
  have hstable : (prefixWord ++ tailWord_1774600).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774600).length < 2 ^ (prefixWord ++ tailWord_1774600).sum := by decide
  have hdescent : baseEnd_1774600 < baseStart_1774600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774642 : List Nat := [3, 2, 1, 1, 2, 2, 1, 4, 5]
def baseStart_1774642 : Nat := 118140960795 + 1774642 * 2 ^ 59
def prefixEnd_1774642 : Nat := 4983230072969 + 3 ^ 40 * 1774642 * 2
def baseEnd_1774642 : Nat := 404997482513933750539367

theorem tailTrace_1774642 : CollatzResearch.WordTrace tailWord_1774642 prefixEnd_1774642 404997482513933750539367 := by
  unfold tailWord_1774642
  simp only [CollatzResearch.WordTrace]
  refine ⟨16181627809195648392225545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43151007491188395712601453 16181627809195648392225545)
  ·
    refine ⟨12136220856896736294169159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16181627809195648392225545 12136220856896736294169159)
    ·
      refine ⟨18204331285345104441253739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12136220856896736294169159 18204331285345104441253739)
      ·
        refine ⟨27306496928017656661880609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18204331285345104441253739 27306496928017656661880609)
        ·
          refine ⟨20479872696013242496410457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27306496928017656661880609 20479872696013242496410457)
          ·
            refine ⟨15359904522009931872307843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20479872696013242496410457 15359904522009931872307843)
            ·
              refine ⟨23039856783014897808461765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15359904522009931872307843 23039856783014897808461765)
              ·
                refine ⟨4319973146815293339086581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23039856783014897808461765 4319973146815293339086581)
                ·
                  refine ⟨404997482513933750539367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4319973146815293339086581 404997482513933750539367)
                  ·
                    rfl

theorem cell21_1774642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 4, 5].length) (baseStart_1774642 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1774642 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1774642 prefixEnd_1774642 := by exact prefixLift 1774642
  have htrace : WordTrace (prefixWord ++ tailWord_1774642) baseStart_1774642 baseEnd_1774642 := by
    simpa [prefixWord, tailWord_1774642, baseEnd_1774642] using wordTrace_append hprefix tailTrace_1774642
  have hstable : (prefixWord ++ tailWord_1774642).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774642).length < 2 ^ (prefixWord ++ tailWord_1774642).sum := by decide
  have hdescent : baseEnd_1774642 < baseStart_1774642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774656 : List Nat := [2, 1, 1, 2, 2, 3, 1, 1, 8]
def baseStart_1774656 : Nat := 118140960795 + 1774656 * 2 ^ 59
def prefixEnd_1774656 : Nat := 4983230072969 + 3 ^ 40 * 1774656 * 2
def baseEnd_1774656 : Nat := 405000677504672837306005

theorem tailTrace_1774656 : CollatzResearch.WordTrace tailWord_1774656 prefixEnd_1774656 405000677504672837306005 := by
  unfold tailWord_1774656
  simp only [CollatzResearch.WordTrace]
  refine ⟨32363510929365936979955911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43151347905821249306607881 32363510929365936979955911)
  ·
    refine ⟨48545266394048905469933867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32363510929365936979955911 48545266394048905469933867)
    ·
      refine ⟨72817899591073358204900801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48545266394048905469933867 72817899591073358204900801)
      ·
        refine ⟨54613424693305018653675601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72817899591073358204900801 54613424693305018653675601)
        ·
          refine ⟨40960068519978763990256701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54613424693305018653675601 40960068519978763990256701)
          ·
            refine ⟨15360025694992036496346263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40960068519978763990256701 15360025694992036496346263)
            ·
              refine ⟨23040038542488054744519395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15360025694992036496346263 23040038542488054744519395)
              ·
                refine ⟨34560057813732082116779093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23040038542488054744519395 34560057813732082116779093)
                ·
                  refine ⟨405000677504672837306005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34560057813732082116779093 405000677504672837306005)
                  ·
                    rfl

theorem cell21_1774656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 8].length) (baseStart_1774656 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1774656 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1774656 prefixEnd_1774656 := by exact prefixLift 1774656
  have htrace : WordTrace (prefixWord ++ tailWord_1774656) baseStart_1774656 baseEnd_1774656 := by
    simpa [prefixWord, tailWord_1774656, baseEnd_1774656] using wordTrace_append hprefix tailTrace_1774656
  have hstable : (prefixWord ++ tailWord_1774656).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774656).length < 2 ^ (prefixWord ++ tailWord_1774656).sum := by decide
  have hdescent : baseEnd_1774656 < baseStart_1774656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774687 : List Nat := [1, 1, 2, 3, 1, 1, 6, 6]
def baseStart_1774687 : Nat := 118140960795 + 1774687 * 2 ^ 59
def prefixEnd_1774687 : Nat := 4983230072969 + 3 ^ 40 * 1774687 * 2
def baseEnd_1774687 : Nat := 135002584042341224096425

theorem tailTrace_1774687 : CollatzResearch.WordTrace tailWord_1774687 prefixEnd_1774687 135002584042341224096425 := by
  unfold tailWord_1774687
  simp only [CollatzResearch.WordTrace]
  refine ⟨64728152521619566254290315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43152101681079710836193543 64728152521619566254290315)
  ·
    refine ⟨97092228782429349381435473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64728152521619566254290315 97092228782429349381435473)
    ·
      refine ⟨72819171586822012036076605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97092228782429349381435473 72819171586822012036076605)
      ·
        refine ⟨27307189345058254513528727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72819171586822012036076605 27307189345058254513528727)
        ·
          refine ⟨40960784017587381770293091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27307189345058254513528727 40960784017587381770293091)
          ·
            refine ⟨61441176026381072655439637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40960784017587381770293091 61441176026381072655439637)
            ·
              refine ⟨2880055126236612780723733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 61441176026381072655439637 2880055126236612780723733)
              ·
                refine ⟨135002584042341224096425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2880055126236612780723733 135002584042341224096425)
                ·
                  rfl

theorem cell21_1774687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 6].length) (baseStart_1774687 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1774687 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1774687 prefixEnd_1774687 := by exact prefixLift 1774687
  have htrace : WordTrace (prefixWord ++ tailWord_1774687) baseStart_1774687 baseEnd_1774687 := by
    simpa [prefixWord, tailWord_1774687, baseEnd_1774687] using wordTrace_append hprefix tailTrace_1774687
  have hstable : (prefixWord ++ tailWord_1774687).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774687).length < 2 ^ (prefixWord ++ tailWord_1774687).sum := by decide
  have hdescent : baseEnd_1774687 < baseStart_1774687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774732 : List Nat := [2, 2, 1, 2, 1, 1, 1, 5, 6]
def baseStart_1774732 : Nat := 118140960795 + 1774732 * 2 ^ 59
def prefixEnd_1774732 : Nat := 4983230072969 + 3 ^ 40 * 1774732 * 2
def baseEnd_1774732 : Nat := 405018021740113594039183

theorem tailTrace_1774732 : CollatzResearch.WordTrace tailWord_1774732 prefixEnd_1774732 405018021740113594039183 := by
  unfold tailWord_1774732
  simp only [CollatzResearch.WordTrace]
  refine ⟨32364896903228269469839225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43153195870971025959785633 32364896903228269469839225)
  ·
    refine ⟨24273672677421202102379419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32364896903228269469839225 24273672677421202102379419)
    ·
      refine ⟨36410509016131803153569129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24273672677421202102379419 36410509016131803153569129)
      ·
        refine ⟨27307881762098852365176847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36410509016131803153569129 27307881762098852365176847)
        ·
          refine ⟨40961822643148278547765271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27307881762098852365176847 40961822643148278547765271)
          ·
            refine ⟨61442733964722417821647907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40961822643148278547765271 61442733964722417821647907)
            ·
              refine ⟨92164100947083626732471861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61442733964722417821647907 92164100947083626732471861)
              ·
                refine ⟨8640384463789090006169237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 92164100947083626732471861 8640384463789090006169237)
                ·
                  refine ⟨405018021740113594039183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8640384463789090006169237 405018021740113594039183)
                  ·
                    rfl

theorem cell21_1774732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 6].length) (baseStart_1774732 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1774732 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1774732 prefixEnd_1774732 := by exact prefixLift 1774732
  have htrace : WordTrace (prefixWord ++ tailWord_1774732) baseStart_1774732 baseEnd_1774732 := by
    simpa [prefixWord, tailWord_1774732, baseEnd_1774732] using wordTrace_append hprefix tailTrace_1774732
  have hstable : (prefixWord ++ tailWord_1774732).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774732).length < 2 ^ (prefixWord ++ tailWord_1774732).sum := by decide
  have hdescent : baseEnd_1774732 < baseStart_1774732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774749 : List Nat := [1, 4, 2, 1, 1, 2, 1, 5, 4]
def baseStart_1774749 : Nat := 118140960795 + 1774749 * 2 ^ 59
def prefixEnd_1774749 : Nat := 4983230072969 + 3 ^ 40 * 1774749 * 2
def baseEnd_1774749 : Nat := 405021901371725342255815

theorem tailTrace_1774749 : CollatzResearch.WordTrace tailWord_1774749 prefixEnd_1774749 405021901371725342255815 := by
  unfold tailWord_1774749
  simp only [CollatzResearch.WordTrace]
  refine ⟨64730413847394950843047301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43153609231596633895364867 64730413847394950843047301)
  ·
    refine ⟨12136952596386553283071369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64730413847394950843047301 12136952596386553283071369)
    ·
      refine ⟨9102714447289914962303527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12136952596386553283071369 9102714447289914962303527)
      ·
        refine ⟨13654071670934872443455291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9102714447289914962303527 13654071670934872443455291)
        ·
          refine ⟨20481107506402308665182937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13654071670934872443455291 20481107506402308665182937)
          ·
            refine ⟨15360830629801731498887203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20481107506402308665182937 15360830629801731498887203)
            ·
              refine ⟨23041245944702597248330805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15360830629801731498887203 23041245944702597248330805)
              ·
                refine ⟨2160116807315868492031013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23041245944702597248330805 2160116807315868492031013)
                ·
                  refine ⟨405021901371725342255815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2160116807315868492031013 405021901371725342255815)
                  ·
                    rfl

theorem cell21_1774749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 5, 4].length) (baseStart_1774749 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1774749 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1774749 prefixEnd_1774749 := by exact prefixLift 1774749
  have htrace : WordTrace (prefixWord ++ tailWord_1774749) baseStart_1774749 baseEnd_1774749 := by
    simpa [prefixWord, tailWord_1774749, baseEnd_1774749] using wordTrace_append hprefix tailTrace_1774749
  have hstable : (prefixWord ++ tailWord_1774749).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774749).length < 2 ^ (prefixWord ++ tailWord_1774749).sum := by decide
  have hdescent : baseEnd_1774749 < baseStart_1774749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774794 : List Nat := [3, 1, 2, 1, 3, 2, 1, 3, 5]
def baseStart_1774794 : Nat := 118140960795 + 1774794 * 2 ^ 59
def prefixEnd_1774794 : Nat := 4983230072969 + 3 ^ 40 * 1774794 * 2
def baseEnd_1774794 : Nat := 405032170984815264005723

theorem tailTrace_1774794 : CollatzResearch.WordTrace tailWord_1774794 prefixEnd_1774794 405032170984815264005723 := by
  unfold tailWord_1774794
  simp only [CollatzResearch.WordTrace]
  refine ⟨16183013783057980882108859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43154703421487949018956957 16183013783057980882108859)
  ·
    refine ⟨24274520674586971323163289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16183013783057980882108859 24274520674586971323163289)
    ·
      refine ⟨18205890505940228492372467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24274520674586971323163289 18205890505940228492372467)
      ·
        refine ⟨27308835758910342738558701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18205890505940228492372467 27308835758910342738558701)
        ·
          refine ⟨10240813409591378526959513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27308835758910342738558701 10240813409591378526959513)
          ·
            refine ⟨7680610057193533895219635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10240813409591378526959513 7680610057193533895219635)
            ·
              refine ⟨11520915085790300842829453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7680610057193533895219635 11520915085790300842829453)
              ·
                refine ⟨4320343157171362816061045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11520915085790300842829453 4320343157171362816061045)
                ·
                  refine ⟨405032170984815264005723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4320343157171362816061045 405032170984815264005723)
                  ·
                    rfl

theorem cell21_1774794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 3, 5].length) (baseStart_1774794 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1774794 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1774794 prefixEnd_1774794 := by exact prefixLift 1774794
  have htrace : WordTrace (prefixWord ++ tailWord_1774794) baseStart_1774794 baseEnd_1774794 := by
    simpa [prefixWord, tailWord_1774794, baseEnd_1774794] using wordTrace_append hprefix tailTrace_1774794
  have hstable : (prefixWord ++ tailWord_1774794).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774794).length < 2 ^ (prefixWord ++ tailWord_1774794).sum := by decide
  have hdescent : baseEnd_1774794 < baseStart_1774794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774828 : List Nat := [2, 2, 1, 1, 2, 6, 1, 3, 3]
def baseStart_1774828 : Nat := 118140960795 + 1774828 * 2 ^ 59
def prefixEnd_1774828 : Nat := 4983230072969 + 3 ^ 40 * 1774828 * 2
def baseEnd_1774828 : Nat := 405039930248038760438987

theorem tailTrace_1774828 : CollatzResearch.WordTrace tailWord_1774828 prefixEnd_1774828 405039930248038760438987 := by
  unfold tailWord_1774828
  simp only [CollatzResearch.WordTrace]
  refine ⟨32366647607054373667586569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43155530142739164890115425 32366647607054373667586569)
  ·
    refine ⟨24274985705290780250689927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32366647607054373667586569 24274985705290780250689927)
    ·
      refine ⟨36412478557936170376034891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24274985705290780250689927 36412478557936170376034891)
      ·
        refine ⟨54618717836904255564052337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36412478557936170376034891 54618717836904255564052337)
        ·
          refine ⟨40964038377678191673039253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54618717836904255564052337 40964038377678191673039253)
          ·
            refine ⟨1920189298953665234673715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 40964038377678191673039253 1920189298953665234673715)
            ·
              refine ⟨2880283948430497852010573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1920189298953665234673715 2880283948430497852010573)
              ·
                refine ⟨1080106480661436694503965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2880283948430497852010573 1080106480661436694503965)
                ·
                  refine ⟨405039930248038760438987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1080106480661436694503965 405039930248038760438987)
                  ·
                    rfl

theorem cell21_1774828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 3, 3].length) (baseStart_1774828 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1774828 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1774828 prefixEnd_1774828 := by exact prefixLift 1774828
  have htrace : WordTrace (prefixWord ++ tailWord_1774828) baseStart_1774828 baseEnd_1774828 := by
    simpa [prefixWord, tailWord_1774828, baseEnd_1774828] using wordTrace_append hprefix tailTrace_1774828
  have hstable : (prefixWord ++ tailWord_1774828).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774828).length < 2 ^ (prefixWord ++ tailWord_1774828).sum := by decide
  have hdescent : baseEnd_1774828 < baseStart_1774828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774856 : List Nat := [2, 1, 3, 2, 4, 1, 2, 6]
def baseStart_1774856 : Nat := 118140960795 + 1774856 * 2 ^ 59
def prefixEnd_1774856 : Nat := 4983230072969 + 3 ^ 40 * 1774856 * 2
def baseEnd_1774856 : Nat := 135015440076505644657421

theorem tailTrace_1774856 : CollatzResearch.WordTrace tailWord_1774856 prefixEnd_1774856 135015440076505644657421 := by
  unfold tailWord_1774856
  simp only [CollatzResearch.WordTrace]
  refine ⟨32367158229003654058596211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43156210972004872078128281 32367158229003654058596211)
  ·
    refine ⟨48550737343505481087894317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32367158229003654058596211 48550737343505481087894317)
    ·
      refine ⟨18206526503814555407960369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48550737343505481087894317 18206526503814555407960369)
      ·
        refine ⟨13654894877860916555970277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18206526503814555407960369 13654894877860916555970277)
        ·
          refine ⟨2560292789598921854244427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13654894877860916555970277 2560292789598921854244427)
          ·
            refine ⟨3840439184398382781366641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2560292789598921854244427 3840439184398382781366641)
            ·
              refine ⟨2880329388298787086024981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3840439184398382781366641 2880329388298787086024981)
              ·
                refine ⟨135015440076505644657421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2880329388298787086024981 135015440076505644657421)
                ·
                  rfl

theorem cell21_1774856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 6].length) (baseStart_1774856 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1774856 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1774856 prefixEnd_1774856 := by exact prefixLift 1774856
  have htrace : WordTrace (prefixWord ++ tailWord_1774856) baseStart_1774856 baseEnd_1774856 := by
    simpa [prefixWord, tailWord_1774856, baseEnd_1774856] using wordTrace_append hprefix tailTrace_1774856
  have hstable : (prefixWord ++ tailWord_1774856).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774856).length < 2 ^ (prefixWord ++ tailWord_1774856).sum := by decide
  have hdescent : baseEnd_1774856 < baseStart_1774856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774901 : List Nat := [1, 3, 3, 1, 2, 2, 1, 4, 4]
def baseStart_1774901 : Nat := 118140960795 + 1774901 * 2 ^ 59
def prefixEnd_1774901 : Nat := 4983230072969 + 3 ^ 40 * 1774901 * 2
def baseEnd_1774901 : Nat := 405056589842606855722171

theorem tailTrace_1774901 : CollatzResearch.WordTrace tailWord_1774901 prefixEnd_1774901 405056589842606855722171 := by
  unfold tailWord_1774901
  simp only [CollatzResearch.WordTrace]
  refine ⟨64735957742844280802580557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43157305161896187201720371 64735957742844280802580557)
  ·
    refine ⟨24275984153566605300967709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64735957742844280802580557 24275984153566605300967709)
    ·
      refine ⟨9103494057587476987862891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24275984153566605300967709 9103494057587476987862891)
      ·
        refine ⟨13655241086381215481794337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9103494057587476987862891 13655241086381215481794337)
        ·
          refine ⟨10241430814785911611345753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13655241086381215481794337 10241430814785911611345753)
          ·
            refine ⟨7681073111089433708509315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10241430814785911611345753 7681073111089433708509315)
            ·
              refine ⟨11521609666634150562763973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7681073111089433708509315 11521609666634150562763973)
              ·
                refine ⟨2160301812493903230518245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11521609666634150562763973 2160301812493903230518245)
                ·
                  refine ⟨405056589842606855722171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2160301812493903230518245 405056589842606855722171)
                  ·
                    rfl

theorem cell21_1774901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 4, 4].length) (baseStart_1774901 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1774901 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1774901 prefixEnd_1774901 := by exact prefixLift 1774901
  have htrace : WordTrace (prefixWord ++ tailWord_1774901) baseStart_1774901 baseEnd_1774901 := by
    simpa [prefixWord, tailWord_1774901, baseEnd_1774901] using wordTrace_append hprefix tailTrace_1774901
  have hstable : (prefixWord ++ tailWord_1774901).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774901).length < 2 ^ (prefixWord ++ tailWord_1774901).sum := by decide
  have hdescent : baseEnd_1774901 < baseStart_1774901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774932 : List Nat := [2, 4, 1, 1, 2, 1, 5, 5]
def baseStart_1774932 : Nat := 118140960795 + 1774932 * 2 ^ 59
def prefixEnd_1774932 : Nat := 4983230072969 + 3 ^ 40 * 1774932 * 2
def baseEnd_1774932 : Nat := 135021221488319230235147

theorem tailTrace_1774932 : CollatzResearch.WordTrace tailWord_1774932 prefixEnd_1774932 135021221488319230235147 := by
  unfold tailWord_1774932
  simp only [CollatzResearch.WordTrace]
  refine ⟨32368544202865986548479525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43158058937154648731306033 32368544202865986548479525)
  ·
    refine ⟨6069102038037372477839911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32368544202865986548479525 6069102038037372477839911)
    ·
      refine ⟨9103653057056058716759867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6069102038037372477839911 9103653057056058716759867)
      ·
        refine ⟨13655479585584088075139801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9103653057056058716759867 13655479585584088075139801)
        ·
          refine ⟨10241609689188066056354851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13655479585584088075139801 10241609689188066056354851)
          ·
            refine ⟨15362414533782099084532277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10241609689188066056354851 15362414533782099084532277)
            ·
              refine ⟨1440226362542071789174901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15362414533782099084532277 1440226362542071789174901)
              ·
                refine ⟨135021221488319230235147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1440226362542071789174901 135021221488319230235147)
                ·
                  rfl

theorem cell21_1774932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 5, 5].length) (baseStart_1774932 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1774932 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1774932 prefixEnd_1774932 := by exact prefixLift 1774932
  have htrace : WordTrace (prefixWord ++ tailWord_1774932) baseStart_1774932 baseEnd_1774932 := by
    simpa [prefixWord, tailWord_1774932, baseEnd_1774932] using wordTrace_append hprefix tailTrace_1774932
  have hstable : (prefixWord ++ tailWord_1774932).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774932).length < 2 ^ (prefixWord ++ tailWord_1774932).sum := by decide
  have hdescent : baseEnd_1774932 < baseStart_1774932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774946 : List Nat := [3, 3, 2, 1, 1, 1, 1, 2, 7]
def baseStart_1774946 : Nat := 118140960795 + 1774946 * 2 ^ 59
def prefixEnd_1774946 : Nat := 4983230072969 + 3 ^ 40 * 1774946 * 2
def baseEnd_1774946 : Nat := 405066859455696777472079

theorem tailTrace_1774946 : CollatzResearch.WordTrace tailWord_1774946 prefixEnd_1774946 405066859455696777472079 := by
  unfold tailWord_1774946
  simp only [CollatzResearch.WordTrace]
  refine ⟨16184399756920313371992173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43158399351787502325312461 16184399756920313371992173)
  ·
    refine ⟨6069149908845117514497065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16184399756920313371992173 6069149908845117514497065)
    ·
      refine ⟨4551862431633838135872799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6069149908845117514497065 4551862431633838135872799)
      ·
        refine ⟨6827793647450757203809199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4551862431633838135872799 6827793647450757203809199)
        ·
          refine ⟨10241690471176135805713799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6827793647450757203809199 10241690471176135805713799)
          ·
            refine ⟨15362535706764203708570699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10241690471176135805713799 15362535706764203708570699)
            ·
              refine ⟨23043803560146305562856049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15362535706764203708570699 23043803560146305562856049)
              ·
                refine ⟨17282852670109729172142037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23043803560146305562856049 17282852670109729172142037)
                ·
                  refine ⟨405066859455696777472079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17282852670109729172142037 405066859455696777472079)
                  ·
                    rfl

theorem cell21_1774946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_1774946 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1774946 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1774946 prefixEnd_1774946 := by exact prefixLift 1774946
  have htrace : WordTrace (prefixWord ++ tailWord_1774946) baseStart_1774946 baseEnd_1774946 := by
    simpa [prefixWord, tailWord_1774946, baseEnd_1774946] using wordTrace_append hprefix tailTrace_1774946
  have hstable : (prefixWord ++ tailWord_1774946).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774946).length < 2 ^ (prefixWord ++ tailWord_1774946).sum := by decide
  have hdescent : baseEnd_1774946 < baseStart_1774946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774960 : List Nat := [2, 1, 1, 1, 4, 2, 3, 1, 6]
def baseStart_1774960 : Nat := 118140960795 + 1774960 * 2 ^ 59
def prefixEnd_1774960 : Nat := 4983230072969 + 3 ^ 40 * 1774960 * 2
def baseEnd_1774960 : Nat := 405070054446435864238717

theorem tailTrace_1774960 : CollatzResearch.WordTrace tailWord_1774960 prefixEnd_1774960 405070054446435864238717 := by
  unfold tailWord_1774960
  simp only [CollatzResearch.WordTrace]
  refine ⟨32369054824815266939489167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43158739766420355919318889 32369054824815266939489167)
  ·
    refine ⟨48553582237222900409233751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32369054824815266939489167 48553582237222900409233751)
    ·
      refine ⟨72830373355834350613850627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48553582237222900409233751 72830373355834350613850627)
      ·
        refine ⟨109245560033751525920775941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72830373355834350613850627 109245560033751525920775941)
        ·
          refine ⟨20483542506328411110145489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109245560033751525920775941 20483542506328411110145489)
          ·
            refine ⟨15362656879746308332609117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20483542506328411110145489 15362656879746308332609117)
            ·
              refine ⟨5760996329904865624728419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15362656879746308332609117 5760996329904865624728419)
              ·
                refine ⟨8641494494857298437092629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5760996329904865624728419 8641494494857298437092629)
                ·
                  refine ⟨405070054446435864238717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8641494494857298437092629 405070054446435864238717)
                  ·
                    rfl

theorem cell21_1774960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 1, 6].length) (baseStart_1774960 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1774960 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1774960 prefixEnd_1774960 := by exact prefixLift 1774960
  have htrace : WordTrace (prefixWord ++ tailWord_1774960) baseStart_1774960 baseEnd_1774960 := by
    simpa [prefixWord, tailWord_1774960, baseEnd_1774960] using wordTrace_append hprefix tailTrace_1774960
  have hstable : (prefixWord ++ tailWord_1774960).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774960).length < 2 ^ (prefixWord ++ tailWord_1774960).sum := by decide
  have hdescent : baseEnd_1774960 < baseStart_1774960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1775146 : List Nat := [3, 1, 4, 1, 1, 1, 5, 1, 4]
def baseStart_1775146 : Nat := 118140960795 + 1775146 * 2 ^ 59
def prefixEnd_1775146 : Nat := 4983230072969 + 3 ^ 40 * 1775146 * 2
def baseEnd_1775146 : Nat := 405112502180540874138337

theorem tailTrace_1775146 : CollatzResearch.WordTrace tailWord_1775146 prefixEnd_1775146 405112502180540874138337 := by
  unfold tailWord_1775146
  simp only [CollatzResearch.WordTrace]
  refine ⟨16186223406739171911312323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43163262417971125096832861 16186223406739171911312323)
  ·
    refine ⟨24279335110108757866968485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16186223406739171911312323 24279335110108757866968485)
    ·
      refine ⟨4552375333145392100056591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24279335110108757866968485 4552375333145392100056591)
      ·
        refine ⟨6828562999718088150084887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4552375333145392100056591 6828562999718088150084887)
        ·
          refine ⟨10242844499577132225127331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6828562999718088150084887 10242844499577132225127331)
          ·
            refine ⟨15364266749365698337690997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10242844499577132225127331 15364266749365698337690997)
            ·
              refine ⟨1440400007753034219158531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15364266749365698337690997 1440400007753034219158531)
              ·
                refine ⟨2160600011629551328737797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1440400007753034219158531 2160600011629551328737797)
                ·
                  refine ⟨405112502180540874138337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2160600011629551328737797 405112502180540874138337)
                  ·
                    rfl

theorem cell21_1775146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 5, 1, 4].length) (baseStart_1775146 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1775146 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1775146 prefixEnd_1775146 := by exact prefixLift 1775146
  have htrace : WordTrace (prefixWord ++ tailWord_1775146) baseStart_1775146 baseEnd_1775146 := by
    simpa [prefixWord, tailWord_1775146, baseEnd_1775146] using wordTrace_append hprefix tailTrace_1775146
  have hstable : (prefixWord ++ tailWord_1775146).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1775146).length < 2 ^ (prefixWord ++ tailWord_1775146).sum := by decide
  have hdescent : baseEnd_1775146 < baseStart_1775146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1775146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1775160 : List Nat := [2, 1, 2, 1, 4, 4, 2, 5]
def baseStart_1775160 : Nat := 118140960795 + 1775160 * 2 ^ 59
def prefixEnd_1775160 : Nat := 4983230072969 + 3 ^ 40 * 1775160 * 2
def baseEnd_1775160 : Nat := 135038565723759986968325

theorem tailTrace_1775160 : CollatzResearch.WordTrace tailWord_1775160 prefixEnd_1775160 135038565723759986968325 := by
  unfold tailWord_1775160
  simp only [CollatzResearch.WordTrace]
  refine ⟨32372702124452984018129467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43163602832603978690839289 32372702124452984018129467)
  ·
    refine ⟨48559053186679476027194201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32372702124452984018129467 48559053186679476027194201)
    ·
      refine ⟨36419289890009607020395651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48559053186679476027194201 36419289890009607020395651)
      ·
        refine ⟨54628934835014410530593477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36419289890009607020395651 54628934835014410530593477)
        ·
          refine ⟨10242925281565201974486277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54628934835014410530593477 10242925281565201974486277)
          ·
            refine ⟨1920548490293475370216177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10242925281565201974486277 1920548490293475370216177)
            ·
              refine ⟨1440411367720106527662133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1920548490293475370216177 1440411367720106527662133)
              ·
                refine ⟨135038565723759986968325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1440411367720106527662133 135038565723759986968325)
                ·
                  rfl

theorem cell21_1775160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 2, 5].length) (baseStart_1775160 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1775160 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1775160 prefixEnd_1775160 := by exact prefixLift 1775160
  have htrace : WordTrace (prefixWord ++ tailWord_1775160) baseStart_1775160 baseEnd_1775160 := by
    simpa [prefixWord, tailWord_1775160, baseEnd_1775160] using wordTrace_append hprefix tailTrace_1775160
  have hstable : (prefixWord ++ tailWord_1775160).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1775160).length < 2 ^ (prefixWord ++ tailWord_1775160).sum := by decide
  have hdescent : baseEnd_1775160 < baseStart_1775160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1775160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1775188 : List Nat := [2, 4, 1, 1, 1, 2, 1, 3, 6]
def baseStart_1775188 : Nat := 118140960795 + 1775188 * 2 ^ 59
def prefixEnd_1775188 : Nat := 4983230072969 + 3 ^ 40 * 1775188 * 2
def baseEnd_1775188 : Nat := 405122087152758134438251

theorem tailTrace_1775188 : CollatzResearch.WordTrace tailWord_1775188 prefixEnd_1775188 405122087152758134438251 := by
  unfold tailWord_1775188
  simp only [CollatzResearch.WordTrace]
  refine ⟨32373212746402264409139109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43164283661869685878852145 32373212746402264409139109)
  ·
    refine ⟨6069977389950424576713583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32373212746402264409139109 6069977389950424576713583)
    ·
      refine ⟨9104966084925636865070375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6069977389950424576713583 9104966084925636865070375)
      ·
        refine ⟨13657449127388455297605563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9104966084925636865070375 13657449127388455297605563)
        ·
          refine ⟨20486173691082682946408345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13657449127388455297605563 20486173691082682946408345)
          ·
            refine ⟨15364630268312012209806259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20486173691082682946408345 15364630268312012209806259)
            ·
              refine ⟨23046945402468018314709389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15364630268312012209806259 23046945402468018314709389)
              ·
                refine ⟨8642604525925506868016021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23046945402468018314709389 8642604525925506868016021)
                ·
                  refine ⟨405122087152758134438251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8642604525925506868016021 405122087152758134438251)
                  ·
                    rfl

theorem cell21_1775188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_1775188 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1775188 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1775188 prefixEnd_1775188 := by exact prefixLift 1775188
  have htrace : WordTrace (prefixWord ++ tailWord_1775188) baseStart_1775188 baseEnd_1775188 := by
    simpa [prefixWord, tailWord_1775188, baseEnd_1775188] using wordTrace_append hprefix tailTrace_1775188
  have hstable : (prefixWord ++ tailWord_1775188).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1775188).length < 2 ^ (prefixWord ++ tailWord_1775188).sum := by decide
  have hdescent : baseEnd_1775188 < baseStart_1775188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1775188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1775197 : List Nat := [1, 4, 4, 2, 2, 1, 2, 1, 4]
def baseStart_1775197 : Nat := 118140960795 + 1775197 * 2 ^ 59
def prefixEnd_1775197 : Nat := 4983230072969 + 3 ^ 40 * 1775197 * 2
def baseEnd_1775197 : Nat := 405124141075376118788233

theorem tailTrace_1775197 : CollatzResearch.WordTrace tailWord_1775197 prefixEnd_1775197 405124141075376118788233 := by
  unfold tailWord_1775197
  simp only [CollatzResearch.WordTrace]
  refine ⟨64746753749771923355355845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43164502499847948903570563 64746753749771923355355845)
  ·
    refine ⟨12140016328082235629129221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64746753749771923355355845 12140016328082235629129221)
    ·
      refine ⟨2276253061515419180461729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12140016328082235629129221 2276253061515419180461729)
      ·
        refine ⟨1707189796136564385346297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2276253061515419180461729 1707189796136564385346297)
        ·
          refine ⟨1280392347102423289009723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1707189796136564385346297 1280392347102423289009723)
          ·
            refine ⟨1920588520653634933514585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1280392347102423289009723 1920588520653634933514585)
            ·
              refine ⟨1440441390490226200135939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1920588520653634933514585 1440441390490226200135939)
              ·
                refine ⟨2160662085735339300203909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1440441390490226200135939 2160662085735339300203909)
                ·
                  refine ⟨405124141075376118788233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2160662085735339300203909 405124141075376118788233)
                  ·
                    rfl

theorem cell21_1775197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 2, 1, 4].length) (baseStart_1775197 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1775197 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1775197 prefixEnd_1775197 := by exact prefixLift 1775197
  have htrace : WordTrace (prefixWord ++ tailWord_1775197) baseStart_1775197 baseEnd_1775197 := by
    simpa [prefixWord, tailWord_1775197, baseEnd_1775197] using wordTrace_append hprefix tailTrace_1775197
  have hstable : (prefixWord ++ tailWord_1775197).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1775197).length < 2 ^ (prefixWord ++ tailWord_1775197).sum := by decide
  have hdescent : baseEnd_1775197 < baseStart_1775197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1775197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1775205 : List Nat := [1, 3, 1, 3, 3, 2, 1, 3, 4]
def baseStart_1775205 : Nat := 118140960795 + 1775205 * 2 ^ 59
def prefixEnd_1775205 : Nat := 4983230072969 + 3 ^ 40 * 1775205 * 2
def baseEnd_1775205 : Nat := 405125966784369882654883

theorem tailTrace_1775205 : CollatzResearch.WordTrace tailWord_1775205 prefixEnd_1775205 405125966784369882654883 := by
  unfold tailWord_1775205
  simp only [CollatzResearch.WordTrace]
  refine ⟨64747045533742940721647069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43164697022495293814431379 64747045533742940721647069)
  ·
    refine ⟨24280142075153602770617651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64747045533742940721647069 24280142075153602770617651)
    ·
      refine ⟨36420213112730404155926477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24280142075153602770617651 36420213112730404155926477)
      ·
        refine ⟨13657579917273901558472429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36420213112730404155926477 13657579917273901558472429)
        ·
          refine ⟨5121592468977713084427161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13657579917273901558472429 5121592468977713084427161)
          ·
            refine ⟨3841194351733284813320371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5121592468977713084427161 3841194351733284813320371)
            ·
              refine ⟨5761791527599927219980557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3841194351733284813320371 5761791527599927219980557)
              ·
                refine ⟨2160671822849972707492709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5761791527599927219980557 2160671822849972707492709)
                ·
                  refine ⟨405125966784369882654883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2160671822849972707492709 405125966784369882654883)
                  ·
                    rfl

theorem cell21_1775205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 3, 4].length) (baseStart_1775205 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1775205 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1775205 prefixEnd_1775205 := by exact prefixLift 1775205
  have htrace : WordTrace (prefixWord ++ tailWord_1775205) baseStart_1775205 baseEnd_1775205 := by
    simpa [prefixWord, tailWord_1775205, baseEnd_1775205] using wordTrace_append hprefix tailTrace_1775205
  have hstable : (prefixWord ++ tailWord_1775205).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1775205).length < 2 ^ (prefixWord ++ tailWord_1775205).sum := by decide
  have hdescent : baseEnd_1775205 < baseStart_1775205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1775205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1775329 : List Nat := [1, 2, 3, 1, 6, 1, 2, 5]
def baseStart_1775329 : Nat := 118140960795 + 1775329 * 2 ^ 59
def prefixEnd_1775329 : Nat := 4983230072969 + 3 ^ 40 * 1775329 * 2
def baseEnd_1775329 : Nat := 135051421757924407529321

theorem tailTrace_1775329 : CollatzResearch.WordTrace tailWord_1775329 prefixEnd_1775329 135051421757924407529321 := by
  unfold tailWord_1775329
  simp only [CollatzResearch.WordTrace]
  refine ⟨64751568185293709899161041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43167712123529139932774027 64751568185293709899161041)
  ·
    refine ⟨48563676138970282424370781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64751568185293709899161041 48563676138970282424370781)
    ·
      refine ⟨18211378552113855909139043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48563676138970282424370781 18211378552113855909139043)
      ·
        refine ⟨27317067828170783863708565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18211378552113855909139043 27317067828170783863708565)
        ·
          refine ⟨1280487554445505493611339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 27317067828170783863708565 1280487554445505493611339)
          ·
            refine ⟨1920731331668258240417009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1280487554445505493611339 1920731331668258240417009)
            ·
              refine ⟨1440548498751193680312757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1920731331668258240417009 1440548498751193680312757)
              ·
                refine ⟨135051421757924407529321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1440548498751193680312757 135051421757924407529321)
                ·
                  rfl

theorem cell21_1775329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 2, 5].length) (baseStart_1775329 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1775329 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1775329 prefixEnd_1775329 := by exact prefixLift 1775329
  have htrace : WordTrace (prefixWord ++ tailWord_1775329) baseStart_1775329 baseEnd_1775329 := by
    simpa [prefixWord, tailWord_1775329, baseEnd_1775329] using wordTrace_append hprefix tailTrace_1775329
  have hstable : (prefixWord ++ tailWord_1775329).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1775329).length < 2 ^ (prefixWord ++ tailWord_1775329).sum := by decide
  have hdescent : baseEnd_1775329 < baseStart_1775329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1775329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1775416 : List Nat := [2, 1, 2, 1, 3, 3, 1, 4, 4]
def baseStart_1775416 : Nat := 118140960795 + 1775416 * 2 ^ 59
def prefixEnd_1775416 : Nat := 4983230072969 + 3 ^ 40 * 1775416 * 2
def baseEnd_1775416 : Nat := 405174119859080404637785

theorem tailTrace_1775416 : CollatzResearch.WordTrace tailWord_1775416 prefixEnd_1775416 405174119859080404637785 := by
  unfold tailWord_1775416
  simp only [CollatzResearch.WordTrace]
  refine ⟨32377370667989261878789051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43169827557319015838385401 32377370667989261878789051)
  ·
    refine ⟨48566056001983892818183577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32377370667989261878789051 48566056001983892818183577)
    ·
      refine ⟨36424542001487919613637683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48566056001983892818183577 36424542001487919613637683)
      ·
        refine ⟨54636813002231879420456525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36424542001487919613637683 54636813002231879420456525)
        ·
          refine ⟨20488804875836954782671197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54636813002231879420456525 20488804875836954782671197)
          ·
            refine ⟨7683301828438858043501699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20488804875836954782671197 7683301828438858043501699)
            ·
              refine ⟨11524952742658287065252549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7683301828438858043501699 11524952742658287065252549)
              ·
                refine ⟨2160928639248428824734853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11524952742658287065252549 2160928639248428824734853)
                ·
                  refine ⟨405174119859080404637785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2160928639248428824734853 405174119859080404637785)
                  ·
                    rfl

theorem cell21_1775416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 4, 4].length) (baseStart_1775416 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1775416 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1775416 prefixEnd_1775416 := by exact prefixLift 1775416
  have htrace : WordTrace (prefixWord ++ tailWord_1775416) baseStart_1775416 baseEnd_1775416 := by
    simpa [prefixWord, tailWord_1775416, baseEnd_1775416] using wordTrace_append hprefix tailTrace_1775416
  have hstable : (prefixWord ++ tailWord_1775416).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1775416).length < 2 ^ (prefixWord ++ tailWord_1775416).sum := by decide
  have hdescent : baseEnd_1775416 < baseStart_1775416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1775416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1775492 : List Nat := [2, 3, 2, 1, 1, 1, 2, 5, 4]
def baseStart_1775492 : Nat := 118140960795 + 1775492 * 2 ^ 59
def prefixEnd_1775492 : Nat := 4983230072969 + 3 ^ 40 * 1775492 * 2
def baseEnd_1775492 : Nat := 405191464094521161370963

theorem tailTrace_1775492 : CollatzResearch.WordTrace tailWord_1775492 prefixEnd_1775492 405191464094521161370963 := by
  unfold tailWord_1775492
  simp only [CollatzResearch.WordTrace]
  refine ⟨32378756641851594368672365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43171675522468792491563153 32378756641851594368672365)
  ·
    refine ⟨12142033740694347888252137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32378756641851594368672365 12142033740694347888252137)
    ·
      refine ⟨9106525305520760916189103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12142033740694347888252137 9106525305520760916189103)
      ·
        refine ⟨13659787958281141374283655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9106525305520760916189103 13659787958281141374283655)
        ·
          refine ⟨20489681937421712061425483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13659787958281141374283655 20489681937421712061425483)
          ·
            refine ⟨30734522906132568092138225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20489681937421712061425483 30734522906132568092138225)
            ·
              refine ⟨23050892179599426069103669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30734522906132568092138225 23050892179599426069103669)
              ·
                refine ⟨2161021141837446193978469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23050892179599426069103669 2161021141837446193978469)
                ·
                  refine ⟨405191464094521161370963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2161021141837446193978469 405191464094521161370963)
                  ·
                    rfl

theorem cell21_1775492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 5, 4].length) (baseStart_1775492 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1775492 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1775492 prefixEnd_1775492 := by exact prefixLift 1775492
  have htrace : WordTrace (prefixWord ++ tailWord_1775492) baseStart_1775492 baseEnd_1775492 := by
    simpa [prefixWord, tailWord_1775492, baseEnd_1775492] using wordTrace_append hprefix tailTrace_1775492
  have hstable : (prefixWord ++ tailWord_1775492).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1775492).length < 2 ^ (prefixWord ++ tailWord_1775492).sum := by decide
  have hdescent : baseEnd_1775492 < baseStart_1775492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1775492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1775596 : List Nat := [2, 2, 1, 1, 2, 1, 1, 2, 9]
def baseStart_1775596 : Nat := 118140960795 + 1775596 * 2 ^ 59
def prefixEnd_1775596 : Nat := 4983230072969 + 3 ^ 40 * 1775596 * 2
def baseEnd_1775596 : Nat := 405215198311440091637417

theorem tailTrace_1775596 : CollatzResearch.WordTrace tailWord_1775596 prefixEnd_1775596 405215198311440091637417 := by
  unfold tailWord_1775596
  simp only [CollatzResearch.WordTrace]
  refine ⟨32380653237663207249565321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43174204316884276332753761 32380653237663207249565321)
  ·
    refine ⟨24285489928247405437173991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32380653237663207249565321 24285489928247405437173991)
    ·
      refine ⟨36428234892371108155760987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24285489928247405437173991 36428234892371108155760987)
      ·
        refine ⟨54642352338556662233641481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36428234892371108155760987 54642352338556662233641481)
        ·
          refine ⟨40981764253917496675231111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54642352338556662233641481 40981764253917496675231111)
          ·
            refine ⟨61472646380876245012846667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40981764253917496675231111 61472646380876245012846667)
            ·
              refine ⟨92208969571314367519270001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61472646380876245012846667 92208969571314367519270001)
              ·
                refine ⟨69156727178485775639452501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92208969571314367519270001 69156727178485775639452501)
                ·
                  refine ⟨405215198311440091637417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 69156727178485775639452501 405215198311440091637417)
                  ·
                    rfl

theorem cell21_1775596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 9].length) (baseStart_1775596 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1775596 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1775596 prefixEnd_1775596 := by exact prefixLift 1775596
  have htrace : WordTrace (prefixWord ++ tailWord_1775596) baseStart_1775596 baseEnd_1775596 := by
    simpa [prefixWord, tailWord_1775596, baseEnd_1775596] using wordTrace_append hprefix tailTrace_1775596
  have hstable : (prefixWord ++ tailWord_1775596).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1775596).length < 2 ^ (prefixWord ++ tailWord_1775596).sum := by decide
  have hdescent : baseEnd_1775596 < baseStart_1775596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1775596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1775627 : List Nat := [1, 1, 1, 1, 6, 1, 2, 2, 6]
def baseStart_1775627 : Nat := 118140960795 + 1775627 * 2 ^ 59
def prefixEnd_1775627 : Nat := 4983230072969 + 3 ^ 40 * 1775627 * 2
def baseEnd_1775627 : Nat := 405222272933790926620687

theorem tailTrace_1775627 : CollatzResearch.WordTrace tailWord_1775627 prefixEnd_1775627 405222272933790926620687 := by
  unfold tailWord_1775627
  simp only [CollatzResearch.WordTrace]
  refine ⟨64762437138214106793509135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43174958092142737862339423 64762437138214106793509135)
  ·
    refine ⟨97143655707321160190263703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64762437138214106793509135 97143655707321160190263703)
    ·
      refine ⟨145715483560981740285395555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97143655707321160190263703 145715483560981740285395555)
      ·
        refine ⟨218573225341472610428093333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145715483560981740285395555 218573225341472610428093333)
        ·
          refine ⟨10245619937881528613816875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 218573225341472610428093333 10245619937881528613816875)
          ·
            refine ⟨15368429906822292920725313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10245619937881528613816875 15368429906822292920725313)
            ·
              refine ⟨11526322430116719690543985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15368429906822292920725313 11526322430116719690543985)
              ·
                refine ⟨8644741822587539767907989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11526322430116719690543985 8644741822587539767907989)
                ·
                  refine ⟨405222272933790926620687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8644741822587539767907989 405222272933790926620687)
                  ·
                    rfl

theorem cell21_1775627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 2, 6].length) (baseStart_1775627 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1775627 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1775627 prefixEnd_1775627 := by exact prefixLift 1775627
  have htrace : WordTrace (prefixWord ++ tailWord_1775627) baseStart_1775627 baseEnd_1775627 := by
    simpa [prefixWord, tailWord_1775627, baseEnd_1775627] using wordTrace_append hprefix tailTrace_1775627
  have hstable : (prefixWord ++ tailWord_1775627).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1775627).length < 2 ^ (prefixWord ++ tailWord_1775627).sum := by decide
  have hdescent : baseEnd_1775627 < baseStart_1775627 := by decide
  rcases family_descends (prefixWord ++ tailWord_1775627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1775636 : List Nat := [2, 4, 3, 2, 2, 1, 1, 2, 4]
def baseStart_1775636 : Nat := 118140960795 + 1775636 * 2 ^ 59
def prefixEnd_1775636 : Nat := 4983230072969 + 3 ^ 40 * 1775636 * 2
def baseEnd_1775636 : Nat := 405224326856408910970669

theorem tailTrace_1775636 : CollatzResearch.WordTrace tailWord_1775636 prefixEnd_1775636 405224326856408910970669 := by
  unfold tailWord_1775636
  simp only [CollatzResearch.WordTrace]
  refine ⟨32381382697590750665293381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43175176930121000887057841 32381382697590750665293381)
  ·
    refine ⟨6071509255798265749742509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32381382697590750665293381 6071509255798265749742509)
    ·
      refine ⟨2276815970924349656153441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6071509255798265749742509 2276815970924349656153441)
      ·
        refine ⟨1707611978193262242115081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2276815970924349656153441 1707611978193262242115081)
        ·
          refine ⟨1280708983644946681586311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1707611978193262242115081 1280708983644946681586311)
          ·
            refine ⟨1921063475467420022379467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1280708983644946681586311 1921063475467420022379467)
            ·
              refine ⟨2881595213201130033569201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1921063475467420022379467 2881595213201130033569201)
              ·
                refine ⟨2161196409900847525176901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2881595213201130033569201 2161196409900847525176901)
                ·
                  refine ⟨405224326856408910970669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2161196409900847525176901 405224326856408910970669)
                  ·
                    rfl

theorem cell21_1775636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 2, 4].length) (baseStart_1775636 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1775636 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1775636 prefixEnd_1775636 := by exact prefixLift 1775636
  have htrace : WordTrace (prefixWord ++ tailWord_1775636) baseStart_1775636 baseEnd_1775636 := by
    simpa [prefixWord, tailWord_1775636, baseEnd_1775636] using wordTrace_append hprefix tailTrace_1775636
  have hstable : (prefixWord ++ tailWord_1775636).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1775636).length < 2 ^ (prefixWord ++ tailWord_1775636).sum := by decide
  have hdescent : baseEnd_1775636 < baseStart_1775636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1775636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1775644 : List Nat := [2, 2, 3, 1, 3, 2, 1, 1, 6]
def baseStart_1775644 : Nat := 118140960795 + 1775644 * 2 ^ 59
def prefixEnd_1775644 : Nat := 4983230072969 + 3 ^ 40 * 1775644 * 2
def baseEnd_1775644 : Nat := 405226152565402674837319

theorem tailTrace_1775644 : CollatzResearch.WordTrace tailWord_1775644 prefixEnd_1775644 405226152565402674837319 := by
  unfold tailWord_1775644
  simp only [CollatzResearch.WordTrace]
  refine ⟨32381528589576259348438993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43175371452768345797918657 32381528589576259348438993)
  ·
    refine ⟨24286146442182194511329245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32381528589576259348438993 24286146442182194511329245)
    ·
      refine ⟨9107304915818322941748467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24286146442182194511329245 9107304915818322941748467)
      ·
        refine ⟨13660957373727484412622701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9107304915818322941748467 13660957373727484412622701)
        ·
          refine ⟨5122859015147806654733513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13660957373727484412622701 5122859015147806654733513)
          ·
            refine ⟨3842144261360854991050135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5122859015147806654733513 3842144261360854991050135)
            ·
              refine ⟨5763216392041282486575203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3842144261360854991050135 5763216392041282486575203)
              ·
                refine ⟨8644824588061923729862805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5763216392041282486575203 8644824588061923729862805)
                ·
                  refine ⟨405226152565402674837319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8644824588061923729862805 405226152565402674837319)
                  ·
                    rfl

theorem cell21_1775644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 1, 6].length) (baseStart_1775644 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1775644 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1775644 prefixEnd_1775644 := by exact prefixLift 1775644
  have htrace : WordTrace (prefixWord ++ tailWord_1775644) baseStart_1775644 baseEnd_1775644 := by
    simpa [prefixWord, tailWord_1775644, baseEnd_1775644] using wordTrace_append hprefix tailTrace_1775644
  have hstable : (prefixWord ++ tailWord_1775644).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1775644).length < 2 ^ (prefixWord ++ tailWord_1775644).sum := by decide
  have hdescent : baseEnd_1775644 < baseStart_1775644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1775644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1775703 : List Nat := [1, 1, 3, 2, 2, 1, 4, 1, 6]
def baseStart_1775703 : Nat := 118140960795 + 1775703 * 2 ^ 59
def prefixEnd_1775703 : Nat := 4983230072969 + 3 ^ 40 * 1775703 * 2
def baseEnd_1775703 : Nat := 405239617169231683353865

theorem tailTrace_1775703 : CollatzResearch.WordTrace tailWord_1775703 prefixEnd_1775703 405239617169231683353865 := by
  unfold tailWord_1775703
  simp only [CollatzResearch.WordTrace]
  refine ⟨64765209085938771773275763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43176806057292514515517175 64765209085938771773275763)
  ·
    refine ⟨97147813628908157659913645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64765209085938771773275763 97147813628908157659913645)
    ·
      refine ⟨36430430110840559122467617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97147813628908157659913645 36430430110840559122467617)
      ·
        refine ⟨27322822583130419341850713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36430430110840559122467617 27322822583130419341850713)
        ·
          refine ⟨20492116937347814506388035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27322822583130419341850713 20492116937347814506388035)
          ·
            refine ⟨30738175406021721759582053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20492116937347814506388035 30738175406021721759582053)
            ·
              refine ⟨5763407888629072829921635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30738175406021721759582053 5763407888629072829921635)
              ·
                refine ⟨8645111832943609244882453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5763407888629072829921635 8645111832943609244882453)
                ·
                  refine ⟨405239617169231683353865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8645111832943609244882453 405239617169231683353865)
                  ·
                    rfl

theorem cell21_1775703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 1, 6].length) (baseStart_1775703 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1775703 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1775703 prefixEnd_1775703 := by exact prefixLift 1775703
  have htrace : WordTrace (prefixWord ++ tailWord_1775703) baseStart_1775703 baseEnd_1775703 := by
    simpa [prefixWord, tailWord_1775703, baseEnd_1775703] using wordTrace_append hprefix tailTrace_1775703
  have hstable : (prefixWord ++ tailWord_1775703).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1775703).length < 2 ^ (prefixWord ++ tailWord_1775703).sum := by decide
  have hdescent : baseEnd_1775703 < baseStart_1775703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1775703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1775768 : List Nat := [2, 1, 2, 4, 4, 1, 1, 6]
def baseStart_1775768 : Nat := 118140960795 + 1775768 * 2 ^ 59
def prefixEnd_1775768 : Nat := 4983230072969 + 3 ^ 40 * 1775768 * 2
def baseEnd_1775768 : Nat := 135084817018268671590133

theorem tailTrace_1775768 : CollatzResearch.WordTrace tailWord_1775768 prefixEnd_1775768 135084817018268671590133 := by
  unfold tailWord_1775768
  simp only [CollatzResearch.WordTrace]
  refine ⟨32383789915351643937195979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43178386553802191916261305 32383789915351643937195979)
  ·
    refine ⟨48575684873027465905793969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32383789915351643937195979 48575684873027465905793969)
    ·
      refine ⟨36431763654770599429345477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48575684873027465905793969 36431763654770599429345477)
      ·
        refine ⟨6830955685269487393002277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36431763654770599429345477 6830955685269487393002277)
        ·
          refine ⟨1280804190988028886187927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6830955685269487393002277 1280804190988028886187927)
          ·
            refine ⟨1921206286482043329281891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1280804190988028886187927 1921206286482043329281891)
            ·
              refine ⟨2881809429723064993922837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1921206286482043329281891 2881809429723064993922837)
              ·
                refine ⟨135084817018268671590133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2881809429723064993922837 135084817018268671590133)
                ·
                  rfl

theorem cell21_1775768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 6].length) (baseStart_1775768 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1775768 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1775768 prefixEnd_1775768 := by exact prefixLift 1775768
  have htrace : WordTrace (prefixWord ++ tailWord_1775768) baseStart_1775768 baseEnd_1775768 := by
    simpa [prefixWord, tailWord_1775768, baseEnd_1775768] using wordTrace_append hprefix tailTrace_1775768
  have hstable : (prefixWord ++ tailWord_1775768).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1775768).length < 2 ^ (prefixWord ++ tailWord_1775768).sum := by decide
  have hdescent : baseEnd_1775768 < baseStart_1775768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1775768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1775855 : List Nat := [1, 1, 2, 1, 6, 1, 1, 2, 6]
def baseStart_1775855 : Nat := 118140960795 + 1775855 * 2 ^ 59
def prefixEnd_1775855 : Nat := 4983230072969 + 3 ^ 40 * 1775855 * 2
def baseEnd_1775855 : Nat := 405274305640113196820221

theorem tailTrace_1775855 : CollatzResearch.WordTrace tailWord_1775855 prefixEnd_1775855 405274305640113196820221 := by
  unfold tailWord_1775855
  simp only [CollatzResearch.WordTrace]
  refine ⟨64770752981388101732809019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43180501987592067821872679 64770752981388101732809019)
  ·
    refine ⟨97156129472082152599213529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64770752981388101732809019 97156129472082152599213529)
    ·
      refine ⟨72867097104061614449410147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97156129472082152599213529 72867097104061614449410147)
      ·
        refine ⟨109300645656092421674115221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72867097104061614449410147 109300645656092421674115221)
        ·
          refine ⟨5123467765129332265974151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 109300645656092421674115221 5123467765129332265974151)
          ·
            refine ⟨7685201647693998398961227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5123467765129332265974151 7685201647693998398961227)
            ·
              refine ⟨11527802471540997598441841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7685201647693998398961227 11527802471540997598441841)
              ·
                refine ⟨8645851853655748198831381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11527802471540997598441841 8645851853655748198831381)
                ·
                  refine ⟨405274305640113196820221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8645851853655748198831381 405274305640113196820221)
                  ·
                    rfl

theorem cell21_1775855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 2, 6].length) (baseStart_1775855 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1775855 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1775855 prefixEnd_1775855 := by exact prefixLift 1775855
  have htrace : WordTrace (prefixWord ++ tailWord_1775855) baseStart_1775855 baseEnd_1775855 := by
    simpa [prefixWord, tailWord_1775855, baseEnd_1775855] using wordTrace_append hprefix tailTrace_1775855
  have hstable : (prefixWord ++ tailWord_1775855).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1775855).length < 2 ^ (prefixWord ++ tailWord_1775855).sum := by decide
  have hdescent : baseEnd_1775855 < baseStart_1775855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1775855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1775886 : List Nat := [4, 1, 1, 2, 1, 2, 4, 6]
def baseStart_1775886 : Nat := 118140960795 + 1775886 * 2 ^ 59
def prefixEnd_1775886 : Nat := 4983230072969 + 3 ^ 40 * 1775886 * 2
def baseEnd_1775886 : Nat := 135093793420821343934497

theorem tailTrace_1775886 : CollatzResearch.WordTrace tailWord_1775886 prefixEnd_1775886 135093793420821343934497 := by
  unfold tailWord_1775886
  simp only [CollatzResearch.WordTrace]
  refine ⟨8096485455534474253398439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43181255762850529351458341 8096485455534474253398439)
  ·
    refine ⟨12144728183301711380097659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8096485455534474253398439 12144728183301711380097659)
    ·
      refine ⟨18217092274952567070146489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12144728183301711380097659 18217092274952567070146489)
      ·
        refine ⟨13662819206214425302609867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18217092274952567070146489 13662819206214425302609867)
        ·
          refine ⟨20494228809321637953914801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13662819206214425302609867 20494228809321637953914801)
          ·
            refine ⟨15370671606991228465436101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20494228809321637953914801 15370671606991228465436101)
            ·
              refine ⟨2882000926310855337269269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15370671606991228465436101 2882000926310855337269269)
              ·
                refine ⟨135093793420821343934497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2882000926310855337269269 135093793420821343934497)
                ·
                  rfl

theorem cell21_1775886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 6].length) (baseStart_1775886 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1775886 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1775886 prefixEnd_1775886 := by exact prefixLift 1775886
  have htrace : WordTrace (prefixWord ++ tailWord_1775886) baseStart_1775886 baseEnd_1775886 := by
    simpa [prefixWord, tailWord_1775886, baseEnd_1775886] using wordTrace_append hprefix tailTrace_1775886
  have hstable : (prefixWord ++ tailWord_1775886).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1775886).length < 2 ^ (prefixWord ++ tailWord_1775886).sum := by decide
  have hdescent : baseEnd_1775886 < baseStart_1775886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1775886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1775889 : List Nat := [1, 2, 2, 1, 1, 7, 2, 1, 4]
def baseStart_1775889 : Nat := 118140960795 + 1775889 * 2 ^ 59
def prefixEnd_1775889 : Nat := 4983230072969 + 3 ^ 40 * 1775889 * 2
def baseEnd_1775889 : Nat := 405282064903336693253485

theorem tailTrace_1775889 : CollatzResearch.WordTrace tailWord_1775889 prefixEnd_1775889 405282064903336693253485 := by
  unfold tailWord_1775889
  simp only [CollatzResearch.WordTrace]
  refine ⟨64771993063264925539546721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43181328708843283693031147 64771993063264925539546721)
  ·
    refine ⟨48578994797448694154660041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64771993063264925539546721 48578994797448694154660041)
    ·
      refine ⟨36434246098086520615995031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48578994797448694154660041 36434246098086520615995031)
      ·
        refine ⟨54651369147129780923992547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36434246098086520615995031 54651369147129780923992547)
        ·
          refine ⟨81977053720694671385988821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54651369147129780923992547 81977053720694671385988821)
          ·
            refine ⟨1921337196578781360609113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 81977053720694671385988821 1921337196578781360609113)
            ·
              refine ⟨1441002897434086020456835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1921337196578781360609113 1441002897434086020456835)
              ·
                refine ⟨2161504346151129030685253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1441002897434086020456835 2161504346151129030685253)
                ·
                  refine ⟨405282064903336693253485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2161504346151129030685253 405282064903336693253485)
                  ·
                    rfl

theorem cell21_1775889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 2, 1, 4].length) (baseStart_1775889 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1775889 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1775889 prefixEnd_1775889 := by exact prefixLift 1775889
  have htrace : WordTrace (prefixWord ++ tailWord_1775889) baseStart_1775889 baseEnd_1775889 := by
    simpa [prefixWord, tailWord_1775889, baseEnd_1775889] using wordTrace_append hprefix tailTrace_1775889
  have hstable : (prefixWord ++ tailWord_1775889).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1775889).length < 2 ^ (prefixWord ++ tailWord_1775889).sum := by decide
  have hdescent : baseEnd_1775889 < baseStart_1775889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1775889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1775900 : List Nat := [2, 2, 3, 1, 1, 1, 1, 3, 7]
def baseStart_1775900 : Nat := 118140960795 + 1775900 * 2 ^ 59
def prefixEnd_1775900 : Nat := 4983230072969 + 3 ^ 40 * 1775900 * 2
def baseEnd_1775900 : Nat := 405284575253203118570129

theorem tailTrace_1775900 : CollatzResearch.WordTrace tailWord_1775900 prefixEnd_1775900 405284575253203118570129 := by
  unfold tailWord_1775900
  simp only [CollatzResearch.WordTrace]
  refine ⟨32386197133112537209098577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43181596177483382945464769 32386197133112537209098577)
  ·
    refine ⟨24289647849834402906823933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32386197133112537209098577 24289647849834402906823933)
    ·
      refine ⟨9108617943687901090058975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24289647849834402906823933 9108617943687901090058975)
      ·
        refine ⟨13662926915531851635088463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9108617943687901090058975 13662926915531851635088463)
        ·
          refine ⟨20494390373297777452632695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13662926915531851635088463 20494390373297777452632695)
          ·
            refine ⟨30741585559946666178949043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20494390373297777452632695 30741585559946666178949043)
            ·
              refine ⟨46112378339919999268423565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30741585559946666178949043 46112378339919999268423565)
              ·
                refine ⟨17292141877469999725658837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46112378339919999268423565 17292141877469999725658837)
                ·
                  refine ⟨405284575253203118570129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17292141877469999725658837 405284575253203118570129)
                  ·
                    rfl

theorem cell21_1775900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 7].length) (baseStart_1775900 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1775900 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1775900 prefixEnd_1775900 := by exact prefixLift 1775900
  have htrace : WordTrace (prefixWord ++ tailWord_1775900) baseStart_1775900 baseEnd_1775900 := by
    simpa [prefixWord, tailWord_1775900, baseEnd_1775900] using wordTrace_append hprefix tailTrace_1775900
  have hstable : (prefixWord ++ tailWord_1775900).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1775900).length < 2 ^ (prefixWord ++ tailWord_1775900).sum := by decide
  have hdescent : baseEnd_1775900 < baseStart_1775900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1775900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776187 : List Nat := [1, 1, 1, 1, 1, 2, 1, 2, 11]
def baseStart_1776187 : Nat := 118140960795 + 1776187 * 2 ^ 59
def prefixEnd_1776187 : Nat := 4983230072969 + 3 ^ 40 * 1776187 * 2
def baseEnd_1776187 : Nat := 405350072563354397286209

theorem tailTrace_1776187 : CollatzResearch.WordTrace tailWord_1776187 prefixEnd_1776187 405350072563354397286209 := by
  unfold tailWord_1776187
  simp only [CollatzResearch.WordTrace]
  refine ⟨64782862016185322433894815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43188574677456881622596543 64782862016185322433894815)
  ·
    refine ⟨97174293024277983650842223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64782862016185322433894815 97174293024277983650842223)
    ·
      refine ⟨145761439536416975476263335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97174293024277983650842223 145761439536416975476263335)
      ·
        refine ⟨218642159304625463214395003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145761439536416975476263335 218642159304625463214395003)
        ·
          refine ⟨327963238956938194821592505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218642159304625463214395003 327963238956938194821592505)
          ·
            refine ⟨245972429217703646116194379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 327963238956938194821592505 245972429217703646116194379)
            ·
              refine ⟨368958643826555469174291569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245972429217703646116194379 368958643826555469174291569)
              ·
                refine ⟨276718982869916601880718677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 368958643826555469174291569 276718982869916601880718677)
                ·
                  refine ⟨405350072563354397286209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 276718982869916601880718677 405350072563354397286209)
                  ·
                    rfl

theorem cell21_1776187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 11].length) (baseStart_1776187 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1776187 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1776187 prefixEnd_1776187 := by exact prefixLift 1776187
  have htrace : WordTrace (prefixWord ++ tailWord_1776187) baseStart_1776187 baseEnd_1776187 := by
    simpa [prefixWord, tailWord_1776187, baseEnd_1776187] using wordTrace_append hprefix tailTrace_1776187
  have hstable : (prefixWord ++ tailWord_1776187).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776187).length < 2 ^ (prefixWord ++ tailWord_1776187).sum := by decide
  have hdescent : baseEnd_1776187 < baseStart_1776187 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776249 : List Nat := [1, 2, 1, 3, 3, 2, 2, 7]
def baseStart_1776249 : Nat := 118140960795 + 1776249 * 2 ^ 59
def prefixEnd_1776249 : Nat := 4983230072969 + 3 ^ 40 * 1776249 * 2
def baseEnd_1776249 : Nat := 135121407269352022417583

theorem tailTrace_1776249 : CollatzResearch.WordTrace tailWord_1776249 prefixEnd_1776249 135121407269352022417583 := by
  unfold tailWord_1776249
  simp only [CollatzResearch.WordTrace]
  refine ⟨64785123341960707022651801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43190082227973804681767867 64785123341960707022651801)
  ·
    refine ⟨48588842506470530266988851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64785123341960707022651801 48588842506470530266988851)
    ·
      refine ⟨72883263759705795400483277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48588842506470530266988851 72883263759705795400483277)
      ·
        refine ⟨27331223909889673275181229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72883263759705795400483277 27331223909889673275181229)
        ·
          refine ⟨10249208966208627478192961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27331223909889673275181229 10249208966208627478192961)
          ·
            refine ⟨7686906724656470608644721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10249208966208627478192961 7686906724656470608644721)
            ·
              refine ⟨5765180043492352956483541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7686906724656470608644721 5765180043492352956483541)
              ·
                refine ⟨135121407269352022417583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5765180043492352956483541 135121407269352022417583)
                ·
                  rfl

theorem cell21_1776249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 7].length) (baseStart_1776249 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1776249 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1776249 prefixEnd_1776249 := by exact prefixLift 1776249
  have htrace : WordTrace (prefixWord ++ tailWord_1776249) baseStart_1776249 baseEnd_1776249 := by
    simpa [prefixWord, tailWord_1776249, baseEnd_1776249] using wordTrace_append hprefix tailTrace_1776249
  have hstable : (prefixWord ++ tailWord_1776249).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776249).length < 2 ^ (prefixWord ++ tailWord_1776249).sum := by decide
  have hdescent : baseEnd_1776249 < baseStart_1776249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776266 : List Nat := [3, 1, 2, 3, 4, 8]
def baseStart_1776266 : Nat := 118140960795 + 1776266 * 2 ^ 59
def prefixEnd_1776266 : Nat := 4983230072969 + 3 ^ 40 * 1776266 * 2
def baseEnd_1776266 : Nat := 15013633386654363535903

theorem tailTrace_1776266 : CollatzResearch.WordTrace tailWord_1776266 prefixEnd_1776266 15013633386654363535903 := by
  unfold tailWord_1776266
  simp only [CollatzResearch.WordTrace]
  refine ⟨16196435845724779731505163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43190495588599412617347101 16196435845724779731505163)
  ·
    refine ⟨24294653768587169597257745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16196435845724779731505163 24294653768587169597257745)
    ·
      refine ⟨18220990326440377197943309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24294653768587169597257745 18220990326440377197943309)
      ·
        refine ⟨6832871372415141449228741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18220990326440377197943309 6832871372415141449228741)
        ·
          refine ⟨1281163382327839021730389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6832871372415141449228741 1281163382327839021730389)
          ·
            refine ⟨15013633386654363535903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1281163382327839021730389 15013633386654363535903)
            ·
              rfl

theorem cell21_1776266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 8].length) (baseStart_1776266 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1776266 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1776266 prefixEnd_1776266 := by exact prefixLift 1776266
  have htrace : WordTrace (prefixWord ++ tailWord_1776266) baseStart_1776266 baseEnd_1776266 := by
    simpa [prefixWord, tailWord_1776266, baseEnd_1776266] using wordTrace_append hprefix tailTrace_1776266
  have hstable : (prefixWord ++ tailWord_1776266).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776266).length < 2 ^ (prefixWord ++ tailWord_1776266).sum := by decide
  have hdescent : baseEnd_1776266 < baseStart_1776266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776280 : List Nat := [2, 1, 2, 4, 1, 1, 2, 3, 5]
def baseStart_1776280 : Nat := 118140960795 + 1776280 * 2 ^ 59
def prefixEnd_1776280 : Nat := 4983230072969 + 3 ^ 40 * 1776280 * 2
def baseEnd_1776280 : Nat := 405371296430406902236019

theorem tailTrace_1776280 : CollatzResearch.WordTrace tailWord_1776280 prefixEnd_1776280 405371296430406902236019 := by
  unfold tailWord_1776280
  simp only [CollatzResearch.WordTrace]
  refine ⟨32393127002424199658515147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43190836003232266211353529 32393127002424199658515147)
  ·
    refine ⟨48589690503636299487772721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32393127002424199658515147 48589690503636299487772721)
    ·
      refine ⟨36442267877727224615829541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48589690503636299487772721 36442267877727224615829541)
      ·
        refine ⟨6832925227073854615468039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36442267877727224615829541 6832925227073854615468039)
        ·
          refine ⟨10249387840610781923202059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6832925227073854615468039 10249387840610781923202059)
          ·
            refine ⟨15374081760916172884803089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10249387840610781923202059 15374081760916172884803089)
            ·
              refine ⟨11530561320687129663602317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15374081760916172884803089 11530561320687129663602317)
              ·
                refine ⟨4323960495257673623850869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11530561320687129663602317 4323960495257673623850869)
                ·
                  refine ⟨405371296430406902236019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4323960495257673623850869 405371296430406902236019)
                  ·
                    rfl

theorem cell21_1776280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 3, 5].length) (baseStart_1776280 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1776280 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1776280 prefixEnd_1776280 := by exact prefixLift 1776280
  have htrace : WordTrace (prefixWord ++ tailWord_1776280) baseStart_1776280 baseEnd_1776280 := by
    simpa [prefixWord, tailWord_1776280, baseEnd_1776280] using wordTrace_append hprefix tailTrace_1776280
  have hstable : (prefixWord ++ tailWord_1776280).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776280).length < 2 ^ (prefixWord ++ tailWord_1776280).sum := by decide
  have hdescent : baseEnd_1776280 < baseStart_1776280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776328 : List Nat := [2, 1, 3, 1, 2, 5, 1, 2, 4]
def baseStart_1776328 : Nat := 118140960795 + 1776328 * 2 ^ 59
def prefixEnd_1776328 : Nat := 4983230072969 + 3 ^ 40 * 1776328 * 2
def baseEnd_1776328 : Nat := 405382250684369485435921

theorem tailTrace_1776328 : CollatzResearch.WordTrace tailWord_1776328 prefixEnd_1776328 405382250684369485435921 := by
  unfold tailWord_1776328
  simp only [CollatzResearch.WordTrace]
  refine ⟨32394002354337251757388819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43192003139116335676518425 32394002354337251757388819)
  ·
    refine ⟨48591003531505877636083229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32394002354337251757388819 48591003531505877636083229)
    ·
      refine ⟨18221626324314704113531211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48591003531505877636083229 18221626324314704113531211)
      ·
        refine ⟨27332439486472056170296817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18221626324314704113531211 27332439486472056170296817)
        ·
          refine ⟨20499329614854042127722613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27332439486472056170296817 20499329614854042127722613)
          ·
            refine ⟨1921812151392566449473995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20499329614854042127722613 1921812151392566449473995)
            ·
              refine ⟨2882718227088849674210993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1921812151392566449473995 2882718227088849674210993)
              ·
                refine ⟨2162038670316637255658245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2882718227088849674210993 2162038670316637255658245)
                ·
                  refine ⟨405382250684369485435921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2162038670316637255658245 405382250684369485435921)
                  ·
                    rfl

theorem cell21_1776328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 2, 4].length) (baseStart_1776328 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1776328 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1776328 prefixEnd_1776328 := by exact prefixLift 1776328
  have htrace : WordTrace (prefixWord ++ tailWord_1776328) baseStart_1776328 baseEnd_1776328 := by
    simpa [prefixWord, tailWord_1776328, baseEnd_1776328] using wordTrace_append hprefix tailTrace_1776328
  have hstable : (prefixWord ++ tailWord_1776328).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776328).length < 2 ^ (prefixWord ++ tailWord_1776328).sum := by decide
  have hdescent : baseEnd_1776328 < baseStart_1776328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776356 : List Nat := [2, 3, 1, 1, 1, 4, 2, 2, 5]
def baseStart_1776356 : Nat := 118140960795 + 1776356 * 2 ^ 59
def prefixEnd_1776356 : Nat := 4983230072969 + 3 ^ 40 * 1776356 * 2
def baseEnd_1776356 : Nat := 405388640665847658969197

theorem tailTrace_1776356 : CollatzResearch.WordTrace tailWord_1776356 prefixEnd_1776356 405388640665847658969197 := by
  unfold tailWord_1776356
  simp only [CollatzResearch.WordTrace]
  refine ⟨32394512976286532148398461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43192683968382042864531281 32394512976286532148398461)
  ·
    refine ⟨12147942366107449555649423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32394512976286532148398461 12147942366107449555649423)
    ·
      refine ⟨18221913549161174333474135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12147942366107449555649423 18221913549161174333474135)
      ·
        refine ⟨27332870323741761500211203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18221913549161174333474135 27332870323741761500211203)
        ·
          refine ⟨40999305485612642250316805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27332870323741761500211203 40999305485612642250316805)
          ·
            refine ⟨7687369778552370421934401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40999305485612642250316805 7687369778552370421934401)
            ·
              refine ⟨5765527333914277816450801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7687369778552370421934401 5765527333914277816450801)
              ·
                refine ⟨4324145500435708362338101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5765527333914277816450801 4324145500435708362338101)
                ·
                  refine ⟨405388640665847658969197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4324145500435708362338101 405388640665847658969197)
                  ·
                    rfl

theorem cell21_1776356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 2, 5].length) (baseStart_1776356 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1776356 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1776356 prefixEnd_1776356 := by exact prefixLift 1776356
  have htrace : WordTrace (prefixWord ++ tailWord_1776356) baseStart_1776356 baseEnd_1776356 := by
    simpa [prefixWord, tailWord_1776356, baseEnd_1776356] using wordTrace_append hprefix tailTrace_1776356
  have hstable : (prefixWord ++ tailWord_1776356).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776356).length < 2 ^ (prefixWord ++ tailWord_1776356).sum := by decide
  have hdescent : baseEnd_1776356 < baseStart_1776356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776452 : List Nat := [2, 3, 4, 2, 1, 2, 1, 6]
def baseStart_1776452 : Nat := 118140960795 + 1776452 * 2 ^ 59
def prefixEnd_1776452 : Nat := 4983230072969 + 3 ^ 40 * 1776452 * 2
def baseEnd_1776452 : Nat := 135136849724590941789667

theorem tailTrace_1776452 : CollatzResearch.WordTrace tailWord_1776452 prefixEnd_1776452 135136849724590941789667 := by
  unfold tailWord_1776452
  simp only [CollatzResearch.WordTrace]
  refine ⟨32396263680112636346145805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43195018240150181794861073 32396263680112636346145805)
  ·
    refine ⟨12148598880042238629804677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32396263680112636346145805 12148598880042238629804677)
    ·
      refine ⟨2277862290007919743088377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12148598880042238629804677 2277862290007919743088377)
      ·
        refine ⟨1708396717505939807316283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2277862290007919743088377 1708396717505939807316283)
        ·
          refine ⟨2562595076258909710974425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1708396717505939807316283 2562595076258909710974425)
          ·
            refine ⟨1921946307194182283230819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2562595076258909710974425 1921946307194182283230819)
            ·
              refine ⟨2882919460791273424846229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1921946307194182283230819 2882919460791273424846229)
              ·
                refine ⟨135136849724590941789667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2882919460791273424846229 135136849724590941789667)
                ·
                  rfl

theorem cell21_1776452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 6].length) (baseStart_1776452 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1776452 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1776452 prefixEnd_1776452 := by exact prefixLift 1776452
  have htrace : WordTrace (prefixWord ++ tailWord_1776452) baseStart_1776452 baseEnd_1776452 := by
    simpa [prefixWord, tailWord_1776452, baseEnd_1776452] using wordTrace_append hprefix tailTrace_1776452
  have hstable : (prefixWord ++ tailWord_1776452).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776452).length < 2 ^ (prefixWord ++ tailWord_1776452).sum := by decide
  have hdescent : baseEnd_1776452 < baseStart_1776452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776494 : List Nat := [4, 1, 2, 3, 2, 1, 8]
def baseStart_1776494 : Nat := 118140960795 + 1776494 * 2 ^ 59
def prefixEnd_1776494 : Nat := 4983230072969 + 3 ^ 40 * 1776494 * 2
def baseEnd_1776494 : Nat := 45046681571776676185435

theorem tailTrace_1776494 : CollatzResearch.WordTrace tailWord_1776494 prefixEnd_1776494 45046681571776676185435 := by
  unfold tailWord_1776494
  simp only [CollatzResearch.WordTrace]
  refine ⟨8099257403259139233165067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43196039484048742576880357 8099257403259139233165067)
  ·
    refine ⟨12148886104888708849747601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8099257403259139233165067 12148886104888708849747601)
    ·
      refine ⟨9111664578666531637310701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12148886104888708849747601 9111664578666531637310701)
      ·
        refine ⟨3416874216999949363991513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9111664578666531637310701 3416874216999949363991513)
        ·
          refine ⟨2562655662749962022993635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3416874216999949363991513 2562655662749962022993635)
          ·
            refine ⟨3843983494124943034490453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2562655662749962022993635 3843983494124943034490453)
            ·
              refine ⟨45046681571776676185435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3843983494124943034490453 45046681571776676185435)
              ·
                rfl

theorem cell21_1776494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 8].length) (baseStart_1776494 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1776494 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1776494 prefixEnd_1776494 := by exact prefixLift 1776494
  have htrace : WordTrace (prefixWord ++ tailWord_1776494) baseStart_1776494 baseEnd_1776494 := by
    simpa [prefixWord, tailWord_1776494, baseEnd_1776494] using wordTrace_append hprefix tailTrace_1776494
  have hstable : (prefixWord ++ tailWord_1776494).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776494).length < 2 ^ (prefixWord ++ tailWord_1776494).sum := by decide
  have hdescent : baseEnd_1776494 < baseStart_1776494 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776573 : List Nat := [1, 4, 1, 2, 4, 2, 2, 1, 4]
def baseStart_1776573 : Nat := 118140960795 + 1776573 * 2 ^ 59
def prefixEnd_1776573 : Nat := 4983230072969 + 3 ^ 40 * 1776573 * 2
def baseEnd_1776573 : Nat := 405438163022303503852087

theorem tailTrace_1776573 : CollatzResearch.WordTrace tailWord_1776573 prefixEnd_1776573 405438163022303503852087 := by
  unfold tailWord_1776573
  simp only [CollatzResearch.WordTrace]
  refine ⟨64796940592786910357446373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43197960395191273571630915 64796940592786910357446373)
  ·
    refine ⟨12149426361147545692021195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64796940592786910357446373 12149426361147545692021195)
    ·
      refine ⟨18224139541721318538031793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12149426361147545692021195 18224139541721318538031793)
      ·
        refine ⟨13668104656290988903523845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18224139541721318538031793 13668104656290988903523845)
        ·
          refine ⟨2562769623054560419410721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13668104656290988903523845 2562769623054560419410721)
          ·
            refine ⟨1922077217290920314558041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2562769623054560419410721 1922077217290920314558041)
            ·
              refine ⟨1441557912968190235918531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1922077217290920314558041 1441557912968190235918531)
              ·
                refine ⟨2162336869452285353877797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1441557912968190235918531 2162336869452285353877797)
                ·
                  refine ⟨405438163022303503852087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2162336869452285353877797 405438163022303503852087)
                  ·
                    rfl

theorem cell21_1776573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 2, 1, 4].length) (baseStart_1776573 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1776573 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1776573 prefixEnd_1776573 := by exact prefixLift 1776573
  have htrace : WordTrace (prefixWord ++ tailWord_1776573) baseStart_1776573 baseEnd_1776573 := by
    simpa [prefixWord, tailWord_1776573, baseEnd_1776573] using wordTrace_append hprefix tailTrace_1776573
  have hstable : (prefixWord ++ tailWord_1776573).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776573).length < 2 ^ (prefixWord ++ tailWord_1776573).sum := by decide
  have hdescent : baseEnd_1776573 < baseStart_1776573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776615 : List Nat := [1, 1, 5, 2, 2, 1, 1, 4, 4]
def baseStart_1776615 : Nat := 118140960795 + 1776615 * 2 ^ 59
def prefixEnd_1776615 : Nat := 4983230072969 + 3 ^ 40 * 1776615 * 2
def baseEnd_1776615 : Nat := 405447747994520764152001

theorem tailTrace_1776615 : CollatzResearch.WordTrace tailWord_1776615 prefixEnd_1776615 405447747994520764152001 := by
  unfold tailWord_1776615
  simp only [CollatzResearch.WordTrace]
  refine ⟨64798472458634751530475299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43198981639089834353650199 64798472458634751530475299)
  ·
    refine ⟨97197708687952127295712949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64798472458634751530475299 97197708687952127295712949)
    ·
      refine ⟨9112285189495511933973089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 97197708687952127295712949 9112285189495511933973089)
      ·
        refine ⟨6834213892121633950479817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9112285189495511933973089 6834213892121633950479817)
        ·
          refine ⟨5125660419091225462859863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6834213892121633950479817 5125660419091225462859863)
          ·
            refine ⟨7688490628636838194289795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5125660419091225462859863 7688490628636838194289795)
            ·
              refine ⟨11532735942955257291434693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7688490628636838194289795 11532735942955257291434693)
              ·
                refine ⟨2162387989304110742144005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11532735942955257291434693 2162387989304110742144005)
                ·
                  refine ⟨405447747994520764152001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2162387989304110742144005 405447747994520764152001)
                  ·
                    rfl

theorem cell21_1776615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 4, 4].length) (baseStart_1776615 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1776615 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1776615 prefixEnd_1776615 := by exact prefixLift 1776615
  have htrace : WordTrace (prefixWord ++ tailWord_1776615) baseStart_1776615 baseEnd_1776615 := by
    simpa [prefixWord, tailWord_1776615, baseEnd_1776615] using wordTrace_append hprefix tailTrace_1776615
  have hstable : (prefixWord ++ tailWord_1776615).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776615).length < 2 ^ (prefixWord ++ tailWord_1776615).sum := by decide
  have hdescent : baseEnd_1776615 < baseStart_1776615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776618 : List Nat := [3, 1, 3, 1, 2, 2, 4, 2, 3]
def baseStart_1776618 : Nat := 118140960795 + 1776618 * 2 ^ 59
def prefixEnd_1776618 : Nat := 4983230072969 + 3 ^ 40 * 1776618 * 2
def baseEnd_1776618 : Nat := 405448432635393425601995

theorem tailTrace_1776618 : CollatzResearch.WordTrace tailWord_1776618 prefixEnd_1776618 405448432635393425601995 := by
  unfold tailWord_1776618
  simp only [CollatzResearch.WordTrace]
  refine ⟨16199645469405970760708627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43199054585082588695223005 16199645469405970760708627)
  ·
    refine ⟨24299468204108956141062941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16199645469405970760708627 24299468204108956141062941)
    ·
      refine ⟨9112300576540858552898603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24299468204108956141062941 9112300576540858552898603)
      ·
        refine ⟨13668450864811287829347905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9112300576540858552898603 13668450864811287829347905)
        ·
          refine ⟨10251338148608465872010929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13668450864811287829347905 10251338148608465872010929)
          ·
            refine ⟨7688503611456349404008197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10251338148608465872010929 7688503611456349404008197)
            ·
              refine ⟨1441594427148065513251537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7688503611456349404008197 1441594427148065513251537)
              ·
                refine ⟨1081195820361049134938653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1441594427148065513251537 1081195820361049134938653)
                ·
                  refine ⟨405448432635393425601995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1081195820361049134938653 405448432635393425601995)
                  ·
                    rfl

theorem cell21_1776618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 4, 2, 3].length) (baseStart_1776618 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1776618 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1776618 prefixEnd_1776618 := by exact prefixLift 1776618
  have htrace : WordTrace (prefixWord ++ tailWord_1776618) baseStart_1776618 baseEnd_1776618 := by
    simpa [prefixWord, tailWord_1776618, baseEnd_1776618] using wordTrace_append hprefix tailTrace_1776618
  have hstable : (prefixWord ++ tailWord_1776618).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776618).length < 2 ^ (prefixWord ++ tailWord_1776618).sum := by decide
  have hdescent : baseEnd_1776618 < baseStart_1776618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776688 : List Nat := [2, 1, 1, 1, 2, 4, 2, 8]
def baseStart_1776688 : Nat := 118140960795 + 1776688 * 2 ^ 59
def prefixEnd_1776688 : Nat := 4983230072969 + 3 ^ 40 * 1776688 * 2
def baseEnd_1776688 : Nat := 135154802529696286478395

theorem tailTrace_1776688 : CollatzResearch.WordTrace tailWord_1776688 prefixEnd_1776688 135154802529696286478395 := by
  unfold tailWord_1776688
  simp only [CollatzResearch.WordTrace]
  refine ⟨32400567493685142498941359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43200756658246856665255145 32400567493685142498941359)
  ·
    refine ⟨48600851240527713748412039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32400567493685142498941359 48600851240527713748412039)
    ·
      refine ⟨72901276860791570622618059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48600851240527713748412039 72901276860791570622618059)
      ·
        refine ⟨109351915291187355933927089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72901276860791570622618059 109351915291187355933927089)
        ·
          refine ⟨82013936468390516950445317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109351915291187355933927089 82013936468390516950445317)
          ·
            refine ⟨15377613087823221928208497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82013936468390516950445317 15377613087823221928208497)
            ·
              refine ⟨11533209815867416446156373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15377613087823221928208497 11533209815867416446156373)
              ·
                refine ⟨135154802529696286478395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11533209815867416446156373 135154802529696286478395)
                ·
                  rfl

theorem cell21_1776688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 8].length) (baseStart_1776688 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1776688 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1776688 prefixEnd_1776688 := by exact prefixLift 1776688
  have htrace : WordTrace (prefixWord ++ tailWord_1776688) baseStart_1776688 baseEnd_1776688 := by
    simpa [prefixWord, tailWord_1776688, baseEnd_1776688] using wordTrace_append hprefix tailTrace_1776688
  have hstable : (prefixWord ++ tailWord_1776688).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776688).length < 2 ^ (prefixWord ++ tailWord_1776688).sum := by decide
  have hdescent : baseEnd_1776688 < baseStart_1776688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776764 : List Nat := [2, 2, 2, 1, 1, 3, 1, 9]
def baseStart_1776764 : Nat := 118140960795 + 1776764 * 2 ^ 59
def prefixEnd_1776764 : Nat := 4983230072969 + 3 ^ 40 * 1776764 * 2
def baseEnd_1776764 : Nat := 135160583941509872056121

theorem tailTrace_1776764 : CollatzResearch.WordTrace tailWord_1776764 prefixEnd_1776764 135160583941509872056121 := by
  unfold tailWord_1776764
  simp only [CollatzResearch.WordTrace]
  refine ⟨32401953467547474988824673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43202604623396633318432897 32401953467547474988824673)
  ·
    refine ⟨24301465100660606241618505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32401953467547474988824673 24301465100660606241618505)
    ·
      refine ⟨18226098825495454681213879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24301465100660606241618505 18226098825495454681213879)
      ·
        refine ⟨27339148238243182021820819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18226098825495454681213879 27339148238243182021820819)
        ·
          refine ⟨41008722357364773032731229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27339148238243182021820819 41008722357364773032731229)
          ·
            refine ⟨15378270884011789887274211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41008722357364773032731229 15378270884011789887274211)
            ·
              refine ⟨23067406326017684830911317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15378270884011789887274211 23067406326017684830911317)
              ·
                refine ⟨135160583941509872056121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23067406326017684830911317 135160583941509872056121)
                ·
                  rfl

theorem cell21_1776764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 9].length) (baseStart_1776764 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1776764 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1776764 prefixEnd_1776764 := by exact prefixLift 1776764
  have htrace : WordTrace (prefixWord ++ tailWord_1776764) baseStart_1776764 baseEnd_1776764 := by
    simpa [prefixWord, tailWord_1776764, baseEnd_1776764] using wordTrace_append hprefix tailTrace_1776764
  have hstable : (prefixWord ++ tailWord_1776764).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776764).length < 2 ^ (prefixWord ++ tailWord_1776764).sum := by decide
  have hdescent : baseEnd_1776764 < baseStart_1776764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776798 : List Nat := [4, 3, 1, 1, 2, 1, 3, 6]
def baseStart_1776798 : Nat := 118140960795 + 1776798 * 2 ^ 59
def prefixEnd_1776798 : Nat := 4983230072969 + 3 ^ 40 * 1776798 * 2
def baseEnd_1776798 : Nat := 135163170362584370867209

theorem tailTrace_1776798 : CollatzResearch.WordTrace tailWord_1776798 prefixEnd_1776798 135163170362584370867209 := by
  unfold tailWord_1776798
  simp only [CollatzResearch.WordTrace]
  refine ⟨8100643377121471723048381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43203431344647849189591365 8100643377121471723048381)
  ·
    refine ⟨3037741266420551896143143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8100643377121471723048381 3037741266420551896143143)
    ·
      refine ⟨4556611899630827844214715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3037741266420551896143143 4556611899630827844214715)
      ·
        refine ⟨6834917849446241766322073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4556611899630827844214715 6834917849446241766322073)
        ·
          refine ⟨5126188387084681324741555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6834917849446241766322073 5126188387084681324741555)
          ·
            refine ⟨7689282580627021987112333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5126188387084681324741555 7689282580627021987112333)
            ·
              refine ⟨2883480967735133245167125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7689282580627021987112333 2883480967735133245167125)
              ·
                refine ⟨135163170362584370867209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2883480967735133245167125 135163170362584370867209)
                ·
                  rfl

theorem cell21_1776798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 6].length) (baseStart_1776798 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1776798 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1776798 prefixEnd_1776798 := by exact prefixLift 1776798
  have htrace : WordTrace (prefixWord ++ tailWord_1776798) baseStart_1776798 baseEnd_1776798 := by
    simpa [prefixWord, tailWord_1776798, baseEnd_1776798] using wordTrace_append hprefix tailTrace_1776798
  have hstable : (prefixWord ++ tailWord_1776798).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776798).length < 2 ^ (prefixWord ++ tailWord_1776798).sum := by decide
  have hdescent : baseEnd_1776798 < baseStart_1776798 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776874 : List Nat := [3, 1, 3, 1, 1, 5, 2, 5]
def baseStart_1776874 : Nat := 118140960795 + 1776874 * 2 ^ 59
def prefixEnd_1776874 : Nat := 4983230072969 + 3 ^ 40 * 1776874 * 2
def baseEnd_1776874 : Nat := 135168951774397956444935

theorem tailTrace_1776874 : CollatzResearch.WordTrace tailWord_1776874 prefixEnd_1776874 135168951774397956444935 := by
  unfold tailWord_1776874
  simp only [CollatzResearch.WordTrace]
  refine ⟨16201979741174109691038419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43205279309797625842769117 16201979741174109691038419)
  ·
    refine ⟨24302969611761164536557629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16201979741174109691038419 24302969611761164536557629)
    ·
      refine ⟨9113613604410436701209111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24302969611761164536557629 9113613604410436701209111)
      ·
        refine ⟨13670420406615655051813667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9113613604410436701209111 13670420406615655051813667)
        ·
          refine ⟨20505630609923482577720501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13670420406615655051813667 20505630609923482577720501)
          ·
            refine ⟨1922402869680326491661297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20505630609923482577720501 1922402869680326491661297)
            ·
              refine ⟨1441802152260244868745973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1922402869680326491661297 1441802152260244868745973)
              ·
                refine ⟨135168951774397956444935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1441802152260244868745973 135168951774397956444935)
                ·
                  rfl

theorem cell21_1776874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 2, 5].length) (baseStart_1776874 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1776874 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1776874 prefixEnd_1776874 := by exact prefixLift 1776874
  have htrace : WordTrace (prefixWord ++ tailWord_1776874) baseStart_1776874 baseEnd_1776874 := by
    simpa [prefixWord, tailWord_1776874, baseEnd_1776874] using wordTrace_append hprefix tailTrace_1776874
  have hstable : (prefixWord ++ tailWord_1776874).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776874).length < 2 ^ (prefixWord ++ tailWord_1776874).sum := by decide
  have hdescent : baseEnd_1776874 < baseStart_1776874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776905 : List Nat := [1, 2, 1, 1, 3, 3, 5, 2, 3]
def baseStart_1776905 : Nat := 118140960795 + 1776905 * 2 ^ 59
def prefixEnd_1776905 : Nat := 4983230072969 + 3 ^ 40 * 1776905 * 2
def baseEnd_1776905 : Nat := 405513929945544704318075

theorem tailTrace_1776905 : CollatzResearch.WordTrace tailWord_1776905 prefixEnd_1776905 405513929945544704318075 := by
  unfold tailWord_1776905
  simp only [CollatzResearch.WordTrace]
  refine ⟨64809049627584131058532169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43206033085056087372354779 64809049627584131058532169)
  ·
    refine ⟨48606787220688098293899127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64809049627584131058532169 48606787220688098293899127)
    ·
      refine ⟨72910180831032147440848691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48606787220688098293899127 72910180831032147440848691)
      ·
        refine ⟨109365271246548221161273037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72910180831032147440848691 109365271246548221161273037)
        ·
          refine ⟨41011976717455582935477389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109365271246548221161273037 41011976717455582935477389)
          ·
            refine ⟨15379491269045843600804021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41011976717455582935477389 15379491269045843600804021)
            ·
              refine ⟨1441827306473047837575377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15379491269045843600804021 1441827306473047837575377)
              ·
                refine ⟨1081370479854785878181533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1441827306473047837575377 1081370479854785878181533)
                ·
                  refine ⟨405513929945544704318075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1081370479854785878181533 405513929945544704318075)
                  ·
                    rfl

theorem cell21_1776905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 5, 2, 3].length) (baseStart_1776905 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1776905 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1776905 prefixEnd_1776905 := by exact prefixLift 1776905
  have htrace : WordTrace (prefixWord ++ tailWord_1776905) baseStart_1776905 baseEnd_1776905 := by
    simpa [prefixWord, tailWord_1776905, baseEnd_1776905] using wordTrace_append hprefix tailTrace_1776905
  have hstable : (prefixWord ++ tailWord_1776905).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776905).length < 2 ^ (prefixWord ++ tailWord_1776905).sum := by decide
  have hdescent : baseEnd_1776905 < baseStart_1776905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776950 : List Nat := [5, 1, 2, 3, 1, 9]
def baseStart_1776950 : Nat := 118140960795 + 1776950 * 2 ^ 59
def prefixEnd_1776950 : Nat := 4983230072969 + 3 ^ 40 * 1776950 * 2
def baseEnd_1776950 : Nat := 15019414798467949113629

theorem tailTrace_1776950 : CollatzResearch.WordTrace tailWord_1776950 prefixEnd_1776950 15019414798467949113629 := by
  unfold tailWord_1776950
  simp only [CollatzResearch.WordTrace]
  refine ⟨4050668182026318983995019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43207127274947402495946869 4050668182026318983995019)
  ·
    refine ⟨6076002273039478475992529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4050668182026318983995019 6076002273039478475992529)
    ·
      refine ⟨4557001704779608856994397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6076002273039478475992529 4557001704779608856994397)
      ·
        refine ⟨1708875639292353321372899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4557001704779608856994397 1708875639292353321372899)
        ·
          refine ⟨2563313458938529982059349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1708875639292353321372899 2563313458938529982059349)
          ·
            refine ⟨15019414798467949113629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2563313458938529982059349 15019414798467949113629)
            ·
              rfl

theorem cell21_1776950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 9].length) (baseStart_1776950 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1776950 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1776950 prefixEnd_1776950 := by exact prefixLift 1776950
  have htrace : WordTrace (prefixWord ++ tailWord_1776950) baseStart_1776950 baseEnd_1776950 := by
    simpa [prefixWord, tailWord_1776950, baseEnd_1776950] using wordTrace_append hprefix tailTrace_1776950
  have hstable : (prefixWord ++ tailWord_1776950).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776950).length < 2 ^ (prefixWord ++ tailWord_1776950).sum := by decide
  have hdescent : baseEnd_1776950 < baseStart_1776950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777144 : List Nat := [2, 1, 2, 1, 1, 5, 3, 6]
def baseStart_1777144 : Nat := 118140960795 + 1777144 * 2 ^ 59
def prefixEnd_1777144 : Nat := 4983230072969 + 3 ^ 40 * 1777144 * 2
def baseEnd_1777144 : Nat := 135189491000577799944751

theorem tailTrace_1777144 : CollatzResearch.WordTrace tailWord_1777144 prefixEnd_1777144 135189491000577799944751 := by
  unfold tailWord_1777144
  simp only [CollatzResearch.WordTrace]
  refine ⟨32408883336859137438241243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43211844449145516584321657 32408883336859137438241243)
  ·
    refine ⟨48613325005288706157361865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32408883336859137438241243 48613325005288706157361865)
    ·
      refine ⟨36459993753966529618021399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48613325005288706157361865 36459993753966529618021399)
      ·
        refine ⟨54689990630949794427032099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36459993753966529618021399 54689990630949794427032099)
        ·
          refine ⟨82034985946424691640548149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54689990630949794427032099 82034985946424691640548149)
          ·
            refine ⟨7690779932477314841301389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 82034985946424691640548149 7690779932477314841301389)
            ·
              refine ⟨2884042474678993065488021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7690779932477314841301389 2884042474678993065488021)
              ·
                refine ⟨135189491000577799944751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2884042474678993065488021 135189491000577799944751)
                ·
                  rfl

theorem cell21_1777144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 6].length) (baseStart_1777144 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1777144 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1777144 prefixEnd_1777144 := by exact prefixLift 1777144
  have htrace : WordTrace (prefixWord ++ tailWord_1777144) baseStart_1777144 baseEnd_1777144 := by
    simpa [prefixWord, tailWord_1777144, baseEnd_1777144] using wordTrace_append hprefix tailTrace_1777144
  have hstable : (prefixWord ++ tailWord_1777144).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777144).length < 2 ^ (prefixWord ++ tailWord_1777144).sum := by decide
  have hdescent : baseEnd_1777144 < baseStart_1777144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777251 : List Nat := [1, 1, 1, 5, 1, 3, 3, 1, 5]
def baseStart_1777251 : Nat := 118140960795 + 1777251 * 2 ^ 59
def prefixEnd_1777251 : Nat := 4983230072969 + 3 ^ 40 * 1777251 * 2
def baseEnd_1777251 : Nat := 405592891859524991550701

theorem tailTrace_1777251 : CollatzResearch.WordTrace tailWord_1777251 prefixEnd_1777251 405592891859524991550701 := by
  unfold tailWord_1777251
  simp only [CollatzResearch.WordTrace]
  refine ⟨64821669284330632150627607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43214446189553754767085071 64821669284330632150627607)
  ·
    refine ⟨97232503926495948225941411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64821669284330632150627607 97232503926495948225941411)
    ·
      refine ⟨145848755889743922338912117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97232503926495948225941411 145848755889743922338912117)
      ·
        refine ⟨13673320864663492719273011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 145848755889743922338912117 13673320864663492719273011)
        ·
          refine ⟨20509981296995239078909517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13673320864663492719273011 20509981296995239078909517)
          ·
            refine ⟨7691242986373214654591069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20509981296995239078909517 7691242986373214654591069)
            ·
              refine ⟨2884216119889955495471651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7691242986373214654591069 2884216119889955495471651)
              ·
                refine ⟨4326324179834933243207477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2884216119889955495471651 4326324179834933243207477)
                ·
                  refine ⟨405592891859524991550701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4326324179834933243207477 405592891859524991550701)
                  ·
                    rfl

theorem cell21_1777251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 1, 5].length) (baseStart_1777251 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1777251 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1777251 prefixEnd_1777251 := by exact prefixLift 1777251
  have htrace : WordTrace (prefixWord ++ tailWord_1777251) baseStart_1777251 baseEnd_1777251 := by
    simpa [prefixWord, tailWord_1777251, baseEnd_1777251] using wordTrace_append hprefix tailTrace_1777251
  have hstable : (prefixWord ++ tailWord_1777251).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777251).length < 2 ^ (prefixWord ++ tailWord_1777251).sum := by decide
  have hdescent : baseEnd_1777251 < baseStart_1777251 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777313 : List Nat := [1, 2, 3, 3, 2, 3, 1, 6]
def baseStart_1777313 : Nat := 118140960795 + 1777313 * 2 ^ 59
def prefixEnd_1777313 : Nat := 4983230072969 + 3 ^ 40 * 1777313 * 2
def baseEnd_1777313 : Nat := 135202347034742220505747

theorem tailTrace_1777313 : CollatzResearch.WordTrace tailWord_1777313 prefixEnd_1777313 135202347034742220505747 := by
  unfold tailWord_1777313
  simp only [CollatzResearch.WordTrace]
  refine ⟨64823930610106016739384593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43215953740070677826256395 64823930610106016739384593)
  ·
    refine ⟨48617947957579512554538445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64823930610106016739384593 48617947957579512554538445)
    ·
      refine ⟨18231730484092317207951917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48617947957579512554538445 18231730484092317207951917)
      ·
        refine ⟨6836898931534618952981969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18231730484092317207951917 6836898931534618952981969)
        ·
          refine ⟨5127674198650964214736477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6836898931534618952981969 5127674198650964214736477)
          ·
            refine ⟨1922877824494111580526179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5127674198650964214736477 1922877824494111580526179)
            ·
              refine ⟨2884316736741167370789269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1922877824494111580526179 2884316736741167370789269)
              ·
                refine ⟨135202347034742220505747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2884316736741167370789269 135202347034742220505747)
                ·
                  rfl

theorem cell21_1777313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 6].length) (baseStart_1777313 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1777313 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1777313 prefixEnd_1777313 := by exact prefixLift 1777313
  have htrace : WordTrace (prefixWord ++ tailWord_1777313) baseStart_1777313 baseEnd_1777313 := by
    simpa [prefixWord, tailWord_1777313, baseEnd_1777313] using wordTrace_append hprefix tailTrace_1777313
  have hstable : (prefixWord ++ tailWord_1777313).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777313).length < 2 ^ (prefixWord ++ tailWord_1777313).sum := by decide
  have hdescent : baseEnd_1777313 < baseStart_1777313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777341 : List Nat := [1, 4, 1, 2, 1, 2, 2, 2, 6]
def baseStart_1777341 : Nat := 118140960795 + 1777341 * 2 ^ 59
def prefixEnd_1777341 : Nat := 4983230072969 + 3 ^ 40 * 1777341 * 2
def baseEnd_1777341 : Nat := 405613431085704835050517

theorem tailTrace_1777341 : CollatzResearch.WordTrace tailWord_1777341 prefixEnd_1777341 405613431085704835050517 := by
  unfold tailWord_1777341
  simp only [CollatzResearch.WordTrace]
  refine ⟨64824951854004577521403877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43216634569336385014269251 64824951854004577521403877)
  ·
    refine ⟨12154678472625858285263227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64824951854004577521403877 12154678472625858285263227)
    ·
      refine ⟨18232017708938787427894841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12154678472625858285263227 18232017708938787427894841)
      ·
        refine ⟨13674013281704090570921131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18232017708938787427894841 13674013281704090570921131)
        ·
          refine ⟨20511019922556135856381697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13674013281704090570921131 20511019922556135856381697)
          ·
            refine ⟨15383264941917101892286273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20511019922556135856381697 15383264941917101892286273)
            ·
              refine ⟨11537448706437826419214705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15383264941917101892286273 11537448706437826419214705)
              ·
                refine ⟨8653086529828369814411029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11537448706437826419214705 8653086529828369814411029)
                ·
                  refine ⟨405613431085704835050517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8653086529828369814411029 405613431085704835050517)
                  ·
                    rfl

theorem cell21_1777341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 2, 6].length) (baseStart_1777341 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1777341 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1777341 prefixEnd_1777341 := by exact prefixLift 1777341
  have htrace : WordTrace (prefixWord ++ tailWord_1777341) baseStart_1777341 baseEnd_1777341 := by
    simpa [prefixWord, tailWord_1777341, baseEnd_1777341] using wordTrace_append hprefix tailTrace_1777341
  have hstable : (prefixWord ++ tailWord_1777341).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777341).length < 2 ^ (prefixWord ++ tailWord_1777341).sum := by decide
  have hdescent : baseEnd_1777341 < baseStart_1777341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777344 : List Nat := [2, 1, 1, 2, 4, 1, 4, 3, 3]
def baseStart_1777344 : Nat := 118140960795 + 1777344 * 2 ^ 59
def prefixEnd_1777344 : Nat := 4983230072969 + 3 ^ 40 * 1777344 * 2
def baseEnd_1777344 : Nat := 405614115726577496500511

theorem tailTrace_1777344 : CollatzResearch.WordTrace tailWord_1777344 prefixEnd_1777344 405614115726577496500511 := by
  unfold tailWord_1777344
  simp only [CollatzResearch.WordTrace]
  refine ⟨32412530636496854516881543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43216707515329139355842057 32412530636496854516881543)
  ·
    refine ⟨48618795954745281775322315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32412530636496854516881543 48618795954745281775322315)
    ·
      refine ⟨72928193932117922662983473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48618795954745281775322315 72928193932117922662983473)
      ·
        refine ⟨54696145449088441997237605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72928193932117922662983473 54696145449088441997237605)
        ·
          refine ⟨10255527271704082874482051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54696145449088441997237605 10255527271704082874482051)
          ·
            refine ⟨15383290907556124311723077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10255527271704082874482051 15383290907556124311723077)
            ·
              refine ⟨2884367045166773308448077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15383290907556124311723077 2884367045166773308448077)
              ·
                refine ⟨1081637641937539990668029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2884367045166773308448077 1081637641937539990668029)
                ·
                  refine ⟨405614115726577496500511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1081637641937539990668029 405614115726577496500511)
                  ·
                    rfl

theorem cell21_1777344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 3, 3].length) (baseStart_1777344 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1777344 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1777344 prefixEnd_1777344 := by exact prefixLift 1777344
  have htrace : WordTrace (prefixWord ++ tailWord_1777344) baseStart_1777344 baseEnd_1777344 := by
    simpa [prefixWord, tailWord_1777344, baseEnd_1777344] using wordTrace_append hprefix tailTrace_1777344
  have hstable : (prefixWord ++ tailWord_1777344).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777344).length < 2 ^ (prefixWord ++ tailWord_1777344).sum := by decide
  have hdescent : baseEnd_1777344 < baseStart_1777344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777389 : List Nat := [1, 5, 1, 2, 1, 2, 4, 5]
def baseStart_1777389 : Nat := 118140960795 + 1777389 * 2 ^ 59
def prefixEnd_1777389 : Nat := 4983230072969 + 3 ^ 40 * 1777389 * 2
def baseEnd_1777389 : Nat := 135208128446555806083473

theorem tailTrace_1777389 : CollatzResearch.WordTrace tailWord_1777389 prefixEnd_1777389 135208128446555806083473 := by
  unfold tailWord_1777389
  simp only [CollatzResearch.WordTrace]
  refine ⟨64826702557830681719151221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43217801705220454479434147 64826702557830681719151221)
  ·
    refine ⟨6077503364796626411170427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 64826702557830681719151221 6077503364796626411170427)
    ·
      refine ⟨9116255047194939616755641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6077503364796626411170427 9116255047194939616755641)
      ·
        refine ⟨6837191285396204712566731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9116255047194939616755641 6837191285396204712566731)
        ·
          refine ⟨10255786928094307068850097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6837191285396204712566731 10255786928094307068850097)
          ·
            refine ⟨7691840196070730301637573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10255786928094307068850097 7691840196070730301637573)
            ·
              refine ⟨1442220036763261931557045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7691840196070730301637573 1442220036763261931557045)
              ·
                refine ⟨135208128446555806083473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1442220036763261931557045 135208128446555806083473)
                ·
                  rfl

theorem cell21_1777389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 4, 5].length) (baseStart_1777389 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1777389 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1777389 prefixEnd_1777389 := by exact prefixLift 1777389
  have htrace : WordTrace (prefixWord ++ tailWord_1777389) baseStart_1777389 baseEnd_1777389 := by
    simpa [prefixWord, tailWord_1777389, baseEnd_1777389] using wordTrace_append hprefix tailTrace_1777389
  have hstable : (prefixWord ++ tailWord_1777389).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777389).length < 2 ^ (prefixWord ++ tailWord_1777389).sum := by decide
  have hdescent : baseEnd_1777389 < baseStart_1777389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777403 : List Nat := [1, 1, 1, 1, 1, 3, 1, 9, 3]
def baseStart_1777403 : Nat := 118140960795 + 1777403 * 2 ^ 59
def prefixEnd_1777403 : Nat := 4983230072969 + 3 ^ 40 * 1777403 * 2
def baseEnd_1777403 : Nat := 405627580330406505017057

theorem tailTrace_1777403 : CollatzResearch.WordTrace tailWord_1777403 prefixEnd_1777403 405627580330406505017057 := by
  unfold tailWord_1777403
  simp only [CollatzResearch.WordTrace]
  refine ⟨64827213179779962110160863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43218142119853308073440575 64827213179779962110160863)
  ·
    refine ⟨97240819769669943165241295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64827213179779962110160863 97240819769669943165241295)
    ·
      refine ⟨145861229654504914747861943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97240819769669943165241295 145861229654504914747861943)
      ·
        refine ⟨218791844481757372121792915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145861229654504914747861943 218791844481757372121792915)
        ·
          refine ⟨328187766722636058182689373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218791844481757372121792915 328187766722636058182689373)
          ·
            refine ⟨123070412520988521818508515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 328187766722636058182689373 123070412520988521818508515)
            ·
              refine ⟨184605618781482782727762773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123070412520988521818508515 184605618781482782727762773)
              ·
                refine ⟨1081673547547750680045485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 184605618781482782727762773 1081673547547750680045485)
                ·
                  refine ⟨405627580330406505017057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1081673547547750680045485 405627580330406505017057)
                  ·
                    rfl

theorem cell21_1777403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 9, 3].length) (baseStart_1777403 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1777403 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1777403 prefixEnd_1777403 := by exact prefixLift 1777403
  have htrace : WordTrace (prefixWord ++ tailWord_1777403) baseStart_1777403 baseEnd_1777403 := by
    simpa [prefixWord, tailWord_1777403, baseEnd_1777403] using wordTrace_append hprefix tailTrace_1777403
  have hstable : (prefixWord ++ tailWord_1777403).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777403).length < 2 ^ (prefixWord ++ tailWord_1777403).sum := by decide
  have hdescent : baseEnd_1777403 < baseStart_1777403 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777406 : List Nat := [4, 2, 2, 1, 4, 1, 7]
def baseStart_1777406 : Nat := 118140960795 + 1777406 * 2 ^ 59
def prefixEnd_1777406 : Nat := 4983230072969 + 3 ^ 40 * 1777406 * 2
def baseEnd_1777406 : Nat := 45069807219031018496339

theorem tailTrace_1777406 : CollatzResearch.WordTrace tailWord_1777406 prefixEnd_1777406 45069807219031018496339 := by
  unfold tailWord_1777406
  simp only [CollatzResearch.WordTrace]
  refine ⟨8103415324846136702815009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43218215065846062415013381 8103415324846136702815009)
  ·
    refine ⟨6077561493634602527111257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8103415324846136702815009 6077561493634602527111257)
    ·
      refine ⟨4558171120225951895333443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6077561493634602527111257 4558171120225951895333443)
      ·
        refine ⟨6837256680338927843000165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4558171120225951895333443 6837256680338927843000165)
        ·
          refine ⟨1281985627563548970562531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6837256680338927843000165 1281985627563548970562531)
          ·
            refine ⟨1922978441345323455843797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1281985627563548970562531 1922978441345323455843797)
            ·
              refine ⟨45069807219031018496339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1922978441345323455843797 45069807219031018496339)
              ·
                rfl

theorem cell21_1777406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 7].length) (baseStart_1777406 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1777406 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1777406 prefixEnd_1777406 := by exact prefixLift 1777406
  have htrace : WordTrace (prefixWord ++ tailWord_1777406) baseStart_1777406 baseEnd_1777406 := by
    simpa [prefixWord, tailWord_1777406, baseEnd_1777406] using wordTrace_append hprefix tailTrace_1777406
  have hstable : (prefixWord ++ tailWord_1777406).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777406).length < 2 ^ (prefixWord ++ tailWord_1777406).sum := by decide
  have hdescent : baseEnd_1777406 < baseStart_1777406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777417 : List Nat := [1, 2, 1, 1, 3, 2, 1, 6, 4]
def baseStart_1777417 : Nat := 118140960795 + 1777417 * 2 ^ 59
def prefixEnd_1777417 : Nat := 4983230072969 + 3 ^ 40 * 1777417 * 2
def baseEnd_1777417 : Nat := 405630775321145591783695

theorem tailTrace_1777417 : CollatzResearch.WordTrace tailWord_1777417 prefixEnd_1777417 405630775321145591783695 := by
  unfold tailWord_1777417
  simp only [CollatzResearch.WordTrace]
  refine ⟨64827723801729242501170505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43218482534486161667447003 64827723801729242501170505)
  ·
    refine ⟨48620792851296931875877879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64827723801729242501170505 48620792851296931875877879)
    ·
      refine ⟨72931189276945397813816819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48620792851296931875877879 72931189276945397813816819)
      ·
        refine ⟨109396783915418096720725229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72931189276945397813816819 109396783915418096720725229)
        ·
          refine ⟨41023793968281786270271961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109396783915418096720725229 41023793968281786270271961)
          ·
            refine ⟨30767845476211339702703971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41023793968281786270271961 30767845476211339702703971)
            ·
              refine ⟨46151768214317009554055957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30767845476211339702703971 46151768214317009554055957)
              ·
                refine ⟨2163364135046109822846373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 46151768214317009554055957 2163364135046109822846373)
                ·
                  refine ⟨405630775321145591783695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2163364135046109822846373 405630775321145591783695)
                  ·
                    rfl

theorem cell21_1777417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 6, 4].length) (baseStart_1777417 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1777417 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1777417 prefixEnd_1777417 := by exact prefixLift 1777417
  have htrace : WordTrace (prefixWord ++ tailWord_1777417) baseStart_1777417 baseEnd_1777417 := by
    simpa [prefixWord, tailWord_1777417, baseEnd_1777417] using wordTrace_append hprefix tailTrace_1777417
  have hstable : (prefixWord ++ tailWord_1777417).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777417).length < 2 ^ (prefixWord ++ tailWord_1777417).sum := by decide
  have hdescent : baseEnd_1777417 < baseStart_1777417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777434 : List Nat := [3, 1, 1, 3, 2, 3, 1, 3, 4]
def baseStart_1777434 : Nat := 118140960795 + 1777434 * 2 ^ 59
def prefixEnd_1777434 : Nat := 4983230072969 + 3 ^ 40 * 1777434 * 2
def baseEnd_1777434 : Nat := 405634654952757340000327

theorem tailTrace_1777434 : CollatzResearch.WordTrace tailWord_1777434 prefixEnd_1777434 405634654952757340000327 := by
  unfold tailWord_1777434
  simp only [CollatzResearch.WordTrace]
  refine ⟨16207085960666913601134839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43218895895111769603026237 16207085960666913601134839)
  ·
    refine ⟨24310628941000370401702259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16207085960666913601134839 24310628941000370401702259)
    ·
      refine ⟨36465943411500555602553389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24310628941000370401702259 36465943411500555602553389)
      ·
        refine ⟨13674728779312708350957521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36465943411500555602553389 13674728779312708350957521)
        ·
          refine ⟨10256046584484531263218141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13674728779312708350957521 10256046584484531263218141)
          ·
            refine ⟨3846017469181699223706803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10256046584484531263218141 3846017469181699223706803)
            ·
              refine ⟨5769026203772548835560205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3846017469181699223706803 5769026203772548835560205)
              ·
                refine ⟨2163384826414705813335077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5769026203772548835560205 2163384826414705813335077)
                ·
                  refine ⟨405634654952757340000327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2163384826414705813335077 405634654952757340000327)
                  ·
                    rfl

theorem cell21_1777434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 3, 4].length) (baseStart_1777434 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1777434 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1777434 prefixEnd_1777434 := by exact prefixLift 1777434
  have htrace : WordTrace (prefixWord ++ tailWord_1777434) baseStart_1777434 baseEnd_1777434 := by
    simpa [prefixWord, tailWord_1777434, baseEnd_1777434] using wordTrace_append hprefix tailTrace_1777434
  have hstable : (prefixWord ++ tailWord_1777434).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777434).length < 2 ^ (prefixWord ++ tailWord_1777434).sum := by decide
  have hdescent : baseEnd_1777434 < baseStart_1777434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777448 : List Nat := [2, 1, 5, 1, 1, 2, 2, 7]
def baseStart_1777448 : Nat := 118140960795 + 1777448 * 2 ^ 59
def prefixEnd_1777448 : Nat := 4983230072969 + 3 ^ 40 * 1777448 * 2
def baseEnd_1777448 : Nat := 135212616647832142255655

theorem tailTrace_1777448 : CollatzResearch.WordTrace tailWord_1777448 prefixEnd_1777448 135212616647832142255655 := by
  unfold tailWord_1777448
  simp only [CollatzResearch.WordTrace]
  refine ⟨32414427232308467397774499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43219236309744623197032665 32414427232308467397774499)
  ·
    refine ⟨48621640848462701096661749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32414427232308467397774499 48621640848462701096661749)
    ·
      refine ⟨4558278829543378227812039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48621640848462701096661749 4558278829543378227812039)
      ·
        refine ⟨6837418244315067341718059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4558278829543378227812039 6837418244315067341718059)
        ·
          refine ⟨10256127366472601012577089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6837418244315067341718059 10256127366472601012577089)
          ·
            refine ⟨7692095524854450759432817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10256127366472601012577089 7692095524854450759432817)
            ·
              refine ⟨5769071643640838069574613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7692095524854450759432817 5769071643640838069574613)
              ·
                refine ⟨135212616647832142255655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5769071643640838069574613 135212616647832142255655)
                ·
                  rfl

theorem cell21_1777448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 7].length) (baseStart_1777448 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1777448 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1777448 prefixEnd_1777448 := by exact prefixLift 1777448
  have htrace : WordTrace (prefixWord ++ tailWord_1777448) baseStart_1777448 baseEnd_1777448 := by
    simpa [prefixWord, tailWord_1777448, baseEnd_1777448] using wordTrace_append hprefix tailTrace_1777448
  have hstable : (prefixWord ++ tailWord_1777448).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777448).length < 2 ^ (prefixWord ++ tailWord_1777448).sum := by decide
  have hdescent : baseEnd_1777448 < baseStart_1777448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777465 : List Nat := [1, 2, 1, 7, 2, 8]
def baseStart_1777465 : Nat := 118140960795 + 1777465 * 2 ^ 59
def prefixEnd_1777465 : Nat := 4983230072969 + 3 ^ 40 * 1777465 * 2
def baseEnd_1777465 : Nat := 15023767762041043517911

theorem tailTrace_1777465 : CollatzResearch.WordTrace tailWord_1777465 prefixEnd_1777465 15023767762041043517911 := by
  unfold tailWord_1777465
  simp only [CollatzResearch.WordTrace]
  refine ⟨64829474505555346698917849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43219649670370231132611899 64829474505555346698917849)
  ·
    refine ⟨48622105879166510024188387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64829474505555346698917849 48622105879166510024188387)
    ·
      refine ⟨72933158818749765036282581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48622105879166510024188387 72933158818749765036282581)
      ·
        refine ⟨1709370909814447618037873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 72933158818749765036282581 1709370909814447618037873)
        ·
          refine ⟨1282028182360835713528405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1709370909814447618037873 1282028182360835713528405)
          ·
            refine ⟨15023767762041043517911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1282028182360835713528405 15023767762041043517911)
            ·
              rfl

theorem cell21_1777465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 8].length) (baseStart_1777465 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1777465 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1777465 prefixEnd_1777465 := by exact prefixLift 1777465
  have htrace : WordTrace (prefixWord ++ tailWord_1777465) baseStart_1777465 baseEnd_1777465 := by
    simpa [prefixWord, tailWord_1777465, baseEnd_1777465] using wordTrace_append hprefix tailTrace_1777465
  have hstable : (prefixWord ++ tailWord_1777465).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777465).length < 2 ^ (prefixWord ++ tailWord_1777465).sum := by decide
  have hdescent : baseEnd_1777465 < baseStart_1777465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777552 : List Nat := [2, 1, 1, 1, 1, 1, 2, 4, 8]
def baseStart_1777552 : Nat := 118140960795 + 1777552 * 2 ^ 59
def prefixEnd_1777552 : Nat := 4983230072969 + 3 ^ 40 * 1777552 * 2
def baseEnd_1777552 : Nat := 405661584160415357033419

theorem tailTrace_1777552 : CollatzResearch.WordTrace tailWord_1777552 prefixEnd_1777552 405661584160415357033419 := by
  unfold tailWord_1777552
  simp only [CollatzResearch.WordTrace]
  refine ⟨32416323828120080278667455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43221765104160107038223273 32416323828120080278667455)
  ·
    refine ⟨48624485742180120418001183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32416323828120080278667455 48624485742180120418001183)
    ·
      refine ⟨72936728613270180627001775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48624485742180120418001183 72936728613270180627001775)
      ·
        refine ⟨109405092919905270940502663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72936728613270180627001775 109405092919905270940502663)
        ·
          refine ⟨164107639379857906410753995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109405092919905270940502663 164107639379857906410753995)
          ·
            refine ⟨246161459069786859616130993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164107639379857906410753995 246161459069786859616130993)
            ·
              refine ⟨184621094302340144712098245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 246161459069786859616130993 184621094302340144712098245)
              ·
                refine ⟨34616455181688777133518421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 184621094302340144712098245 34616455181688777133518421)
                ·
                  refine ⟨405661584160415357033419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34616455181688777133518421 405661584160415357033419)
                  ·
                    rfl

theorem cell21_1777552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 8].length) (baseStart_1777552 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1777552 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1777552 prefixEnd_1777552 := by exact prefixLift 1777552
  have htrace : WordTrace (prefixWord ++ tailWord_1777552) baseStart_1777552 baseEnd_1777552 := by
    simpa [prefixWord, tailWord_1777552, baseEnd_1777552] using wordTrace_append hprefix tailTrace_1777552
  have hstable : (prefixWord ++ tailWord_1777552).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777552).length < 2 ^ (prefixWord ++ tailWord_1777552).sum := by decide
  have hdescent : baseEnd_1777552 < baseStart_1777552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777572 : List Nat := [2, 3, 1, 2, 1, 3, 3, 3, 3]
def baseStart_1777572 : Nat := 118140960795 + 1777572 * 2 ^ 59
def prefixEnd_1777572 : Nat := 4983230072969 + 3 ^ 40 * 1777572 * 2
def baseEnd_1777572 : Nat := 405666148432899766700045

theorem tailTrace_1777572 : CollatzResearch.WordTrace tailWord_1777572 prefixEnd_1777572 405666148432899766700045 := by
  unfold tailWord_1777572
  simp only [CollatzResearch.WordTrace]
  refine ⟨32416688558083851986531485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43222251410778469315375313 32416688558083851986531485)
  ·
    refine ⟨12156258209281444494949307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32416688558083851986531485 12156258209281444494949307)
    ·
      refine ⟨18234387313922166742423961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12156258209281444494949307 18234387313922166742423961)
      ·
        refine ⟨13675790485441625056817971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18234387313922166742423961 13675790485441625056817971)
        ·
          refine ⟨20513685728162437585226957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13675790485441625056817971 20513685728162437585226957)
          ·
            refine ⟨7692632148060914094460109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20513685728162437585226957 7692632148060914094460109)
            ·
              refine ⟨2884737055522842785422541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7692632148060914094460109 2884737055522842785422541)
              ·
                refine ⟨1081776395821066044533453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2884737055522842785422541 1081776395821066044533453)
                ·
                  refine ⟨405666148432899766700045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1081776395821066044533453 405666148432899766700045)
                  ·
                    rfl

theorem cell21_1777572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 3, 3].length) (baseStart_1777572 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1777572 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1777572 prefixEnd_1777572 := by exact prefixLift 1777572
  have htrace : WordTrace (prefixWord ++ tailWord_1777572) baseStart_1777572 baseEnd_1777572 := by
    simpa [prefixWord, tailWord_1777572, baseEnd_1777572] using wordTrace_append hprefix tailTrace_1777572
  have hstable : (prefixWord ++ tailWord_1777572).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777572).length < 2 ^ (prefixWord ++ tailWord_1777572).sum := by decide
  have hdescent : baseEnd_1777572 < baseStart_1777572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777589 : List Nat := [1, 3, 3, 2, 1, 3, 3, 2, 3]
def baseStart_1777589 : Nat := 118140960795 + 1777589 * 2 ^ 59
def prefixEnd_1777589 : Nat := 4983230072969 + 3 ^ 40 * 1777589 * 2
def baseEnd_1777589 : Nat := 405670028064511514916677

theorem tailTrace_1777589 : CollatzResearch.WordTrace tailWord_1777589 prefixEnd_1777589 405670028064511514916677 := by
  unfold tailWord_1777589
  simp only [CollatzResearch.WordTrace]
  refine ⟨64833997157106115876431821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43222664771404077250954547 64833997157106115876431821)
  ·
    refine ⟨24312748933914793453661933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64833997157106115876431821 24312748933914793453661933)
    ·
      refine ⟨9117280850218047545123225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24312748933914793453661933 9117280850218047545123225)
      ·
        refine ⟨6837960637663535658842419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9117280850218047545123225 6837960637663535658842419)
        ·
          refine ⟨10256940956495303488263629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6837960637663535658842419 10256940956495303488263629)
          ·
            refine ⟨3846352858685738808098861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10256940956495303488263629 3846352858685738808098861)
            ·
              refine ⟨1442382322007152053037073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3846352858685738808098861 1442382322007152053037073)
              ·
                refine ⟨1081786741505364039777805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1442382322007152053037073 1081786741505364039777805)
                ·
                  refine ⟨405670028064511514916677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1081786741505364039777805 405670028064511514916677)
                  ·
                    rfl

theorem cell21_1777589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 3, 2, 3].length) (baseStart_1777589 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1777589 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1777589 prefixEnd_1777589 := by exact prefixLift 1777589
  have htrace : WordTrace (prefixWord ++ tailWord_1777589) baseStart_1777589 baseEnd_1777589 := by
    simpa [prefixWord, tailWord_1777589, baseEnd_1777589] using wordTrace_append hprefix tailTrace_1777589
  have hstable : (prefixWord ++ tailWord_1777589).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777589).length < 2 ^ (prefixWord ++ tailWord_1777589).sum := by decide
  have hdescent : baseEnd_1777589 < baseStart_1777589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777614 : List Nat := [4, 1, 1, 1, 2, 2, 2, 1, 7]
def baseStart_1777614 : Nat := 118140960795 + 1777614 * 2 ^ 59
def prefixEnd_1777614 : Nat := 4983230072969 + 3 ^ 40 * 1777614 * 2
def baseEnd_1777614 : Nat := 405675733405117026999959

theorem tailTrace_1777614 : CollatzResearch.WordTrace tailWord_1777614 prefixEnd_1777614 405675733405117026999959 := by
  unfold tailWord_1777614
  simp only [CollatzResearch.WordTrace]
  refine ⟨8104363622751943143261487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43223272654677030097394597 8104363622751943143261487)
  ·
    refine ⟨12156545434127914714892231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8104363622751943143261487 12156545434127914714892231)
    ·
      refine ⟨18234818151191872072338347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12156545434127914714892231 18234818151191872072338347)
      ·
        refine ⟨27352227226787808108507521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18234818151191872072338347 27352227226787808108507521)
        ·
          refine ⟨20514170420090856081380641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27352227226787808108507521 20514170420090856081380641)
          ·
            refine ⟨15385627815068142061035481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20514170420090856081380641 15385627815068142061035481)
            ·
              refine ⟨11539220861301106545776611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15385627815068142061035481 11539220861301106545776611)
              ·
                refine ⟨17308831291951659818664917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11539220861301106545776611 17308831291951659818664917)
                ·
                  refine ⟨405675733405117026999959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17308831291951659818664917 405675733405117026999959)
                  ·
                    rfl

theorem cell21_1777614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 7].length) (baseStart_1777614 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1777614 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1777614 prefixEnd_1777614 := by exact prefixLift 1777614
  have htrace : WordTrace (prefixWord ++ tailWord_1777614) baseStart_1777614 baseEnd_1777614 := by
    simpa [prefixWord, tailWord_1777614, baseEnd_1777614] using wordTrace_append hprefix tailTrace_1777614
  have hstable : (prefixWord ++ tailWord_1777614).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777614).length < 2 ^ (prefixWord ++ tailWord_1777614).sum := by decide
  have hdescent : baseEnd_1777614 < baseStart_1777614 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777648 : List Nat := [2, 1, 1, 1, 3, 2, 6, 2, 3]
def baseStart_1777648 : Nat := 118140960795 + 1777648 * 2 ^ 59
def prefixEnd_1777648 : Nat := 4983230072969 + 3 ^ 40 * 1777648 * 2
def baseEnd_1777648 : Nat := 405683492668340523433223

theorem tailTrace_1777648 : CollatzResearch.WordTrace tailWord_1777648 prefixEnd_1777648 405683492668340523433223 := by
  unfold tailWord_1777648
  simp only [CollatzResearch.WordTrace]
  refine ⟨32418074531946184476414799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43224099375928245968553065 32418074531946184476414799)
  ·
    refine ⟨48627111797919276714622199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32418074531946184476414799 48627111797919276714622199)
    ·
      refine ⟨72940667696878915071933299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48627111797919276714622199 72940667696878915071933299)
      ·
        refine ⟨109411001545318372607899949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72940667696878915071933299 109411001545318372607899949)
        ·
          refine ⟨41029125579494389727962481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109411001545318372607899949 41029125579494389727962481)
          ·
            refine ⟨30771844184620792295971861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41029125579494389727962481 30771844184620792295971861)
            ·
              refine ⟨1442430196154099638873681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 30771844184620792295971861 1442430196154099638873681)
              ·
                refine ⟨1081822647115574729155261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1442430196154099638873681 1081822647115574729155261)
                ·
                  refine ⟨405683492668340523433223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1081822647115574729155261 405683492668340523433223)
                  ·
                    rfl

theorem cell21_1777648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 6, 2, 3].length) (baseStart_1777648 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1777648 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1777648 prefixEnd_1777648 := by exact prefixLift 1777648
  have htrace : WordTrace (prefixWord ++ tailWord_1777648) baseStart_1777648 baseEnd_1777648 := by
    simpa [prefixWord, tailWord_1777648, baseEnd_1777648] using wordTrace_append hprefix tailTrace_1777648
  have hstable : (prefixWord ++ tailWord_1777648).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777648).length < 2 ^ (prefixWord ++ tailWord_1777648).sum := by decide
  have hdescent : baseEnd_1777648 < baseStart_1777648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777659 : List Nat := [1, 1, 1, 1, 1, 3, 7, 6]
def baseStart_1777659 : Nat := 118140960795 + 1777659 * 2 ^ 59
def prefixEnd_1777659 : Nat := 4983230072969 + 3 ^ 40 * 1777659 * 2
def baseEnd_1777659 : Nat := 135228667672735649583289

theorem tailTrace_1777659 : CollatzResearch.WordTrace tailWord_1777659 prefixEnd_1777659 135228667672735649583289 := by
  unfold tailWord_1777659
  simp only [CollatzResearch.WordTrace]
  refine ⟨64836550266852517831480031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43224366844568345220986687 64836550266852517831480031)
  ·
    refine ⟨97254825400278776747220047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64836550266852517831480031 97254825400278776747220047)
    ·
      refine ⟨145882238100418165120830071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97254825400278776747220047 145882238100418165120830071)
      ·
        refine ⟨218823357150627247681245107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145882238100418165120830071 218823357150627247681245107)
        ·
          refine ⟨328235035725940871521867661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218823357150627247681245107 328235035725940871521867661)
          ·
            refine ⟨123088138397227826820700373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 328235035725940871521867661 123088138397227826820700373)
            ·
              refine ⟨2884878243685027191110165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 123088138397227826820700373 2884878243685027191110165)
              ·
                refine ⟨135228667672735649583289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2884878243685027191110165 135228667672735649583289)
                ·
                  rfl

theorem cell21_1777659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 6].length) (baseStart_1777659 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1777659 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1777659 prefixEnd_1777659 := by exact prefixLift 1777659
  have htrace : WordTrace (prefixWord ++ tailWord_1777659) baseStart_1777659 baseEnd_1777659 := by
    simpa [prefixWord, tailWord_1777659, baseEnd_1777659] using wordTrace_append hprefix tailTrace_1777659
  have hstable : (prefixWord ++ tailWord_1777659).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777659).length < 2 ^ (prefixWord ++ tailWord_1777659).sum := by decide
  have hdescent : baseEnd_1777659 < baseStart_1777659 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777676 : List Nat := [2, 2, 1, 2, 3, 1, 5, 5]
def baseStart_1777676 : Nat := 118140960795 + 1777676 * 2 ^ 59
def prefixEnd_1777676 : Nat := 4983230072969 + 3 ^ 40 * 1777676 * 2
def baseEnd_1777676 : Nat := 135229960883272898988833

theorem tailTrace_1777676 : CollatzResearch.WordTrace tailWord_1777676 prefixEnd_1777676 135229960883272898988833 := by
  unfold tailWord_1777676
  simp only [CollatzResearch.WordTrace]
  refine ⟨32418585153895464867424441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43224780205193953156565921 32418585153895464867424441)
  ·
    refine ⟨24313938865421598650568331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32418585153895464867424441 24313938865421598650568331)
    ·
      refine ⟨36470908298132397975852497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24313938865421598650568331 36470908298132397975852497)
      ·
        refine ⟨27353181223599298481889373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36470908298132397975852497 27353181223599298481889373)
        ·
          refine ⟨10257442958849736930708515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27353181223599298481889373 10257442958849736930708515)
          ·
            refine ⟨15386164438274605396062773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10257442958849736930708515 15386164438274605396062773)
            ·
              refine ⟨1442452916088244255880885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15386164438274605396062773 1442452916088244255880885)
              ·
                refine ⟨135229960883272898988833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1442452916088244255880885 135229960883272898988833)
                ·
                  rfl

theorem cell21_1777676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 5, 5].length) (baseStart_1777676 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1777676 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1777676 prefixEnd_1777676 := by exact prefixLift 1777676
  have htrace : WordTrace (prefixWord ++ tailWord_1777676) baseStart_1777676 baseEnd_1777676 := by
    simpa [prefixWord, tailWord_1777676, baseEnd_1777676] using wordTrace_append hprefix tailTrace_1777676
  have hstable : (prefixWord ++ tailWord_1777676).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777676).length < 2 ^ (prefixWord ++ tailWord_1777676).sum := by decide
  have hdescent : baseEnd_1777676 < baseStart_1777676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777735 : List Nat := [1, 1, 4, 1, 3, 1, 3, 7]
def baseStart_1777735 : Nat := 118140960795 + 1777735 * 2 ^ 59
def prefixEnd_1777735 : Nat := 4983230072969 + 3 ^ 40 * 1777735 * 2
def baseEnd_1777735 : Nat := 135234449084549235161015

theorem tailTrace_1777735 : CollatzResearch.WordTrace tailWord_1777735 prefixEnd_1777735 135234449084549235161015 := by
  unfold tailWord_1777735
  simp only [CollatzResearch.WordTrace]
  refine ⟨64839322214577182811246659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43226214809718121874164439 64839322214577182811246659)
  ·
    refine ⟨97258983321865774216869989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64839322214577182811246659 97258983321865774216869989)
    ·
      refine ⟨18236059372849832665663123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97258983321865774216869989 18236059372849832665663123)
      ·
        refine ⟨27354089059274748998494685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18236059372849832665663123 27354089059274748998494685)
        ·
          refine ⟨10257783397228030874435507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27354089059274748998494685 10257783397228030874435507)
          ·
            refine ⟨15386675095842046311653261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10257783397228030874435507 15386675095842046311653261)
            ·
              refine ⟨5770003160940767366869973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15386675095842046311653261 5770003160940767366869973)
              ·
                refine ⟨135234449084549235161015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5770003160940767366869973 135234449084549235161015)
                ·
                  rfl

theorem cell21_1777735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 7].length) (baseStart_1777735 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1777735 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1777735 prefixEnd_1777735 := by exact prefixLift 1777735
  have htrace : WordTrace (prefixWord ++ tailWord_1777735) baseStart_1777735 baseEnd_1777735 := by
    simpa [prefixWord, tailWord_1777735, baseEnd_1777735] using wordTrace_append hprefix tailTrace_1777735
  have hstable : (prefixWord ++ tailWord_1777735).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777735).length < 2 ^ (prefixWord ++ tailWord_1777735).sum := by decide
  have hdescent : baseEnd_1777735 < baseStart_1777735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777758 : List Nat := [4, 4, 1, 1, 2, 2, 1, 1, 5]
def baseStart_1777758 : Nat := 118140960795 + 1777758 * 2 ^ 59
def prefixEnd_1777758 : Nat := 4983230072969 + 3 ^ 40 * 1777758 * 2
def baseEnd_1777758 : Nat := 405708596167004776599665

theorem tailTrace_1777758 : CollatzResearch.WordTrace tailWord_1777758 prefixEnd_1777758 405708596167004776599665 := by
  unfold tailWord_1777758
  simp only [CollatzResearch.WordTrace]
  refine ⟨8105020136686732217416741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43226774062329238492889285 8105020136686732217416741)
  ·
    refine ⟨1519691275628762290765639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8105020136686732217416741 1519691275628762290765639)
    ·
      refine ⟨2279536913443143436148459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1519691275628762290765639 2279536913443143436148459)
      ·
        refine ⟨3419305370164715154222689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2279536913443143436148459 3419305370164715154222689)
        ·
          refine ⟨2564479027623536365667017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3419305370164715154222689 2564479027623536365667017)
          ·
            refine ⟨1923359270717652274250263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2564479027623536365667017 1923359270717652274250263)
            ·
              refine ⟨2885038906076478411375395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1923359270717652274250263 2885038906076478411375395)
              ·
                refine ⟨4327558359114717617063093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2885038906076478411375395 4327558359114717617063093)
                ·
                  refine ⟨405708596167004776599665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4327558359114717617063093 405708596167004776599665)
                  ·
                    rfl

theorem cell21_1777758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_1777758 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1777758 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1777758 prefixEnd_1777758 := by exact prefixLift 1777758
  have htrace : WordTrace (prefixWord ++ tailWord_1777758) baseStart_1777758 baseEnd_1777758 := by
    simpa [prefixWord, tailWord_1777758, baseEnd_1777758] using wordTrace_append hprefix tailTrace_1777758
  have hstable : (prefixWord ++ tailWord_1777758).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777758).length < 2 ^ (prefixWord ++ tailWord_1777758).sum := by decide
  have hdescent : baseEnd_1777758 < baseStart_1777758 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777842 : List Nat := [3, 2, 1, 1, 1, 3, 3, 2, 5]
def baseStart_1777842 : Nat := 118140960795 + 1777842 * 2 ^ 59
def prefixEnd_1777842 : Nat := 4983230072969 + 3 ^ 40 * 1777842 * 2
def baseEnd_1777842 : Nat := 405727766111439297199493

theorem tailTrace_1777842 : CollatzResearch.WordTrace tailWord_1777842 prefixEnd_1777842 405727766111439297199493 := by
  unfold tailWord_1777842
  simp only [CollatzResearch.WordTrace]
  refine ⟨16210806206297385021347945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43228816550126360056927853 16210806206297385021347945)
  ·
    refine ⟨12158104654723038766010959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16210806206297385021347945 12158104654723038766010959)
    ·
      refine ⟨18237156982084558149016439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12158104654723038766010959 18237156982084558149016439)
      ·
        refine ⟨27355735473126837223524659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18237156982084558149016439 27355735473126837223524659)
        ·
          refine ⟨41033603209690255835286989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27355735473126837223524659 41033603209690255835286989)
          ·
            refine ⟨15387601203633845938232621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41033603209690255835286989 15387601203633845938232621)
            ·
              refine ⟨5770350451362692226837233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15387601203633845938232621 5770350451362692226837233)
              ·
                refine ⟨4327762838522019170127925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5770350451362692226837233 4327762838522019170127925)
                ·
                  refine ⟨405727766111439297199493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4327762838522019170127925 405727766111439297199493)
                  ·
                    rfl

theorem cell21_1777842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 2, 5].length) (baseStart_1777842 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1777842 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1777842 prefixEnd_1777842 := by exact prefixLift 1777842
  have htrace : WordTrace (prefixWord ++ tailWord_1777842) baseStart_1777842 baseEnd_1777842 := by
    simpa [prefixWord, tailWord_1777842, baseEnd_1777842] using wordTrace_append hprefix tailTrace_1777842
  have hstable : (prefixWord ++ tailWord_1777842).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777842).length < 2 ^ (prefixWord ++ tailWord_1777842).sum := by decide
  have hdescent : baseEnd_1777842 < baseStart_1777842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777873 : List Nat := [1, 2, 2, 1, 2, 2, 5, 2, 4]
def baseStart_1777873 : Nat := 118140960795 + 1777873 * 2 ^ 59
def prefixEnd_1777873 : Nat := 4983230072969 + 3 ^ 40 * 1777873 * 2
def baseEnd_1777873 : Nat := 405734840733790132182763

theorem tailTrace_1777873 : CollatzResearch.WordTrace tailWord_1777873 prefixEnd_1777873 405734840733790132182763 := by
  unfold tailWord_1777873
  simp only [CollatzResearch.WordTrace]
  refine ⟨64844355488077232379770273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43229570325384821586513515 64844355488077232379770273)
  ·
    refine ⟨48633266616057924284827705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64844355488077232379770273 48633266616057924284827705)
    ·
      refine ⟨36474949962043443213620779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48633266616057924284827705 36474949962043443213620779)
      ·
        refine ⟨54712424943065164820431169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36474949962043443213620779 54712424943065164820431169)
        ·
          refine ⟨41034318707298873615323377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54712424943065164820431169 41034318707298873615323377)
          ·
            refine ⟨30775739030474155211492533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41034318707298873615323377 30775739030474155211492533)
            ·
              refine ⟨2885225534106952051077425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30775739030474155211492533 2885225534106952051077425)
              ·
                refine ⟨2163919150580214038308069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2885225534106952051077425 2163919150580214038308069)
                ·
                  refine ⟨405734840733790132182763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2163919150580214038308069 405734840733790132182763)
                  ·
                    rfl

theorem cell21_1777873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 2, 4].length) (baseStart_1777873 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1777873 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1777873 prefixEnd_1777873 := by exact prefixLift 1777873
  have htrace : WordTrace (prefixWord ++ tailWord_1777873) baseStart_1777873 baseEnd_1777873 := by
    simpa [prefixWord, tailWord_1777873, baseEnd_1777873] using wordTrace_append hprefix tailTrace_1777873
  have hstable : (prefixWord ++ tailWord_1777873).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777873).length < 2 ^ (prefixWord ++ tailWord_1777873).sum := by decide
  have hdescent : baseEnd_1777873 < baseStart_1777873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777932 : List Nat := [2, 2, 1, 2, 2, 2, 1, 3, 6]
def baseStart_1777932 : Nat := 118140960795 + 1777932 * 2 ^ 59
def prefixEnd_1777932 : Nat := 4983230072969 + 3 ^ 40 * 1777932 * 2
def baseEnd_1777932 : Nat := 405748305337619140699309

theorem tailTrace_1777932 : CollatzResearch.WordTrace tailWord_1777932 prefixEnd_1777932 405748305337619140699309 := by
  unfold tailWord_1777932
  simp only [CollatzResearch.WordTrace]
  refine ⟨32423253697431742728084025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43231004929908990304112033 32423253697431742728084025)
  ·
    refine ⟨24317440273073807046063019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32423253697431742728084025 24317440273073807046063019)
    ·
      refine ⟨36476160409610710569094529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24317440273073807046063019 36476160409610710569094529)
      ·
        refine ⟨27357120307208032926820897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36476160409610710569094529 27357120307208032926820897)
        ·
          refine ⟨20517840230406024695115673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27357120307208032926820897 20517840230406024695115673)
          ·
            refine ⟨15388380172804518521336755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20517840230406024695115673 15388380172804518521336755)
            ·
              refine ⟨23082570259206777782005133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15388380172804518521336755 23082570259206777782005133)
              ·
                refine ⟨8655963847202541668251925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23082570259206777782005133 8655963847202541668251925)
                ·
                  refine ⟨405748305337619140699309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8655963847202541668251925 405748305337619140699309)
                  ·
                    rfl

theorem cell21_1777932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 3, 6].length) (baseStart_1777932 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1777932 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1777932 prefixEnd_1777932 := by exact prefixLift 1777932
  have htrace : WordTrace (prefixWord ++ tailWord_1777932) baseStart_1777932 baseEnd_1777932 := by
    simpa [prefixWord, tailWord_1777932, baseEnd_1777932] using wordTrace_append hprefix tailTrace_1777932
  have hstable : (prefixWord ++ tailWord_1777932).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777932).length < 2 ^ (prefixWord ++ tailWord_1777932).sum := by decide
  have hdescent : baseEnd_1777932 < baseStart_1777932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778028 : List Nat := [2, 2, 1, 1, 6, 1, 2, 3, 3]
def baseStart_1778028 : Nat := 118140960795 + 1778028 * 2 ^ 59
def prefixEnd_1778028 : Nat := 4983230072969 + 3 ^ 40 * 1778028 * 2
def baseEnd_1778028 : Nat := 405770213845544307099113

theorem tailTrace_1778028 : CollatzResearch.WordTrace tailWord_1778028 prefixEnd_1778028 405770213845544307099113 := by
  unfold tailWord_1778028
  simp only [CollatzResearch.WordTrace]
  refine ⟨32425004401257846925831369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43233339201677129234441825 32425004401257846925831369)
  ·
    refine ⟨24318753300943385194373527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32425004401257846925831369 24318753300943385194373527)
    ·
      refine ⟨36478129951415077791560291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24318753300943385194373527 36478129951415077791560291)
      ·
        refine ⟨54717194927122616687340437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36478129951415077791560291 54717194927122616687340437)
        ·
          refine ⟨2564868512208872657219083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 54717194927122616687340437 2564868512208872657219083)
          ·
            refine ⟨3847302768313308985828625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2564868512208872657219083 3847302768313308985828625)
            ·
              refine ⟨2885477076234981739371469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3847302768313308985828625 2885477076234981739371469)
              ·
                refine ⟨1082053903588118152264301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2885477076234981739371469 1082053903588118152264301)
                ·
                  refine ⟨405770213845544307099113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1082053903588118152264301 405770213845544307099113)
                  ·
                    rfl

theorem cell21_1778028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 3, 3].length) (baseStart_1778028 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1778028 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1778028 prefixEnd_1778028 := by exact prefixLift 1778028
  have htrace : WordTrace (prefixWord ++ tailWord_1778028) baseStart_1778028 baseEnd_1778028 := by
    simpa [prefixWord, tailWord_1778028, baseEnd_1778028] using wordTrace_append hprefix tailTrace_1778028
  have hstable : (prefixWord ++ tailWord_1778028).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778028).length < 2 ^ (prefixWord ++ tailWord_1778028).sum := by decide
  have hdescent : baseEnd_1778028 < baseStart_1778028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778084 : List Nat := [2, 3, 1, 2, 1, 1, 3, 2, 6]
def baseStart_1778084 : Nat := 118140960795 + 1778084 * 2 ^ 59
def prefixEnd_1778084 : Nat := 4983230072969 + 3 ^ 40 * 1778084 * 2
def baseEnd_1778084 : Nat := 405782993808500654165665

theorem tailTrace_1778084 : CollatzResearch.WordTrace tailWord_1778084 prefixEnd_1778084 405782993808500654165665 := by
  unfold tailWord_1778084
  simp only [CollatzResearch.WordTrace]
  refine ⟨32426025645156407707850653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43234700860208543610467537 32426025645156407707850653)
  ·
    refine ⟨12159759616933652890443995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32426025645156407707850653 12159759616933652890443995)
    ·
      refine ⟨18239639425400479335665993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12159759616933652890443995 18239639425400479335665993)
      ·
        refine ⟨13679729569050359501749495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18239639425400479335665993 13679729569050359501749495)
        ·
          refine ⟨20519594353575539252624243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13679729569050359501749495 20519594353575539252624243)
          ·
            refine ⟨30779391530363308878936365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20519594353575539252624243 30779391530363308878936365)
            ·
              refine ⟨11542271823886240829601137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30779391530363308878936365 11542271823886240829601137)
              ·
                refine ⟨8656703867914680622200853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11542271823886240829601137 8656703867914680622200853)
                ·
                  refine ⟨405782993808500654165665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8656703867914680622200853 405782993808500654165665)
                  ·
                    rfl

theorem cell21_1778084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 2, 6].length) (baseStart_1778084 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1778084 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1778084 prefixEnd_1778084 := by exact prefixLift 1778084
  have htrace : WordTrace (prefixWord ++ tailWord_1778084) baseStart_1778084 baseEnd_1778084 := by
    simpa [prefixWord, tailWord_1778084, baseEnd_1778084] using wordTrace_append hprefix tailTrace_1778084
  have hstable : (prefixWord ++ tailWord_1778084).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778084).length < 2 ^ (prefixWord ++ tailWord_1778084).sum := by decide
  have hdescent : baseEnd_1778084 < baseStart_1778084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778090 : List Nat := [3, 1, 6, 1, 1, 2, 7]
def baseStart_1778090 : Nat := 118140960795 + 1778090 * 2 ^ 59
def prefixEnd_1778090 : Nat := 4983230072969 + 3 ^ 40 * 1778090 * 2
def baseEnd_1778090 : Nat := 45087151454471775229517

theorem tailTrace_1778090 : CollatzResearch.WordTrace tailWord_1778090 prefixEnd_1778090 45087151454471775229517 := by
  unfold tailWord_1778090
  simp only [CollatzResearch.WordTrace]
  refine ⟨16213067532072769610104931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43234846752194052293613149 16213067532072769610104931)
  ·
    refine ⟨24319601298109154415157397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16213067532072769610104931 24319601298109154415157397)
    ·
      refine ⟨1139981310848866613210503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 24319601298109154415157397 1139981310848866613210503)
      ·
        refine ⟨1709971966273299919815755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1139981310848866613210503 1709971966273299919815755)
        ·
          refine ⟨2564957949409949879723633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1709971966273299919815755 2564957949409949879723633)
          ·
            refine ⟨1923718462057462409792725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2564957949409949879723633 1923718462057462409792725)
            ·
              refine ⟨45087151454471775229517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1923718462057462409792725 45087151454471775229517)
              ·
                rfl

theorem cell21_1778090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 7].length) (baseStart_1778090 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1778090 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1778090 prefixEnd_1778090 := by exact prefixLift 1778090
  have htrace : WordTrace (prefixWord ++ tailWord_1778090) baseStart_1778090 baseEnd_1778090 := by
    simpa [prefixWord, tailWord_1778090, baseEnd_1778090] using wordTrace_append hprefix tailTrace_1778090
  have hstable : (prefixWord ++ tailWord_1778090).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778090).length < 2 ^ (prefixWord ++ tailWord_1778090).sum := by decide
  have hdescent : baseEnd_1778090 < baseStart_1778090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778129 : List Nat := [1, 2, 2, 1, 2, 1, 1, 6, 5]
def baseStart_1778129 : Nat := 118140960795 + 1778129 * 2 ^ 59
def prefixEnd_1778129 : Nat := 4983230072969 + 3 ^ 40 * 1778129 * 2
def baseEnd_1778129 : Nat := 405793263421590575915573

theorem tailTrace_1778129 : CollatzResearch.WordTrace tailWord_1778129 prefixEnd_1778129 405793263421590575915573 := by
  unfold tailWord_1778129
  simp only [CollatzResearch.WordTrace]
  refine ⟨64853692575149788101089441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43235795050099858734059627 64853692575149788101089441)
  ·
    refine ⟨48640269431362341075817081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64853692575149788101089441 48640269431362341075817081)
    ·
      refine ⟨36480202073521755806862811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48640269431362341075817081 36480202073521755806862811)
      ·
        refine ⟨54720303110282633710294217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36480202073521755806862811 54720303110282633710294217)
        ·
          refine ⟨41040227332711975282720663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54720303110282633710294217 41040227332711975282720663)
          ·
            refine ⟨61560340999067962924080995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41040227332711975282720663 61560340999067962924080995)
            ·
              refine ⟨92340511498601944386121493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61560340999067962924080995 92340511498601944386121493)
              ·
                refine ⟨4328461476496966143099445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 92340511498601944386121493 4328461476496966143099445)
                ·
                  refine ⟨405793263421590575915573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4328461476496966143099445 405793263421590575915573)
                  ·
                    rfl

theorem cell21_1778129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 6, 5].length) (baseStart_1778129 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1778129 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1778129 prefixEnd_1778129 := by exact prefixLift 1778129
  have htrace : WordTrace (prefixWord ++ tailWord_1778129) baseStart_1778129 baseEnd_1778129 := by
    simpa [prefixWord, tailWord_1778129, baseEnd_1778129] using wordTrace_append hprefix tailTrace_1778129
  have hstable : (prefixWord ++ tailWord_1778129).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778129).length < 2 ^ (prefixWord ++ tailWord_1778129).sum := by decide
  have hdescent : baseEnd_1778129 < baseStart_1778129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778177 : List Nat := [1, 2, 4, 1, 3, 1, 2, 3, 4]
def baseStart_1778177 : Nat := 118140960795 + 1778177 * 2 ^ 59
def prefixEnd_1778177 : Nat := 4983230072969 + 3 ^ 40 * 1778177 * 2
def baseEnd_1778177 : Nat := 405804217675553159115475

theorem tailTrace_1778177 : CollatzResearch.WordTrace tailWord_1778177 prefixEnd_1778177 405804217675553159115475 := by
  unfold tailWord_1778177
  simp only [CollatzResearch.WordTrace]
  refine ⟨64855443278975892298836785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43236962185983928199224523 64855443278975892298836785)
  ·
    refine ⟨48641582459231919224127589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64855443278975892298836785 48641582459231919224127589)
    ·
      refine ⟨9120296711105984854523923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48641582459231919224127589 9120296711105984854523923)
      ·
        refine ⟨13680445066658977281785885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9120296711105984854523923 13680445066658977281785885)
        ·
          refine ⟨5130166899997116480669707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13680445066658977281785885 5130166899997116480669707)
          ·
            refine ⟨7695250349995674721004561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5130166899997116480669707 7695250349995674721004561)
            ·
              refine ⟨5771437762496756040753421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7695250349995674721004561 5771437762496756040753421)
              ·
                refine ⟨2164289160936283515282533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5771437762496756040753421 2164289160936283515282533)
                ·
                  refine ⟨405804217675553159115475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2164289160936283515282533 405804217675553159115475)
                  ·
                    rfl

theorem cell21_1778177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 3, 4].length) (baseStart_1778177 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1778177 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1778177 prefixEnd_1778177 := by exact prefixLift 1778177
  have htrace : WordTrace (prefixWord ++ tailWord_1778177) baseStart_1778177 baseEnd_1778177 := by
    simpa [prefixWord, tailWord_1778177, baseEnd_1778177] using wordTrace_append hprefix tailTrace_1778177
  have hstable : (prefixWord ++ tailWord_1778177).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778177).length < 2 ^ (prefixWord ++ tailWord_1778177).sum := by decide
  have hdescent : baseEnd_1778177 < baseStart_1778177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778228 : List Nat := [2, 5, 1, 3, 1, 1, 3, 1, 4]
def baseStart_1778228 : Nat := 118140960795 + 1778228 * 2 ^ 59
def prefixEnd_1778228 : Nat := 4983230072969 + 3 ^ 40 * 1778228 * 2
def baseEnd_1778228 : Nat := 405815856570388403765371

theorem tailTrace_1778228 : CollatzResearch.WordTrace tailWord_1778228 prefixEnd_1778228 405815856570388403765371 := by
  unfold tailWord_1778228
  simp only [CollatzResearch.WordTrace]
  refine ⟨32428651700895564004471669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43238202267860752005962225 32428651700895564004471669)
  ·
    refine ⟨3040186096958959125419219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32428651700895564004471669 3040186096958959125419219)
    ·
      refine ⟨4560279145438438688128829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3040186096958959125419219 4560279145438438688128829)
      ·
        refine ⟨1710104679539414508048311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4560279145438438688128829 1710104679539414508048311)
        ·
          refine ⟨2565157019309121762072467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1710104679539414508048311 2565157019309121762072467)
          ·
            refine ⟨3847735528963682643108701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2565157019309121762072467 3847735528963682643108701)
            ·
              refine ⟨1442900823361380991165763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3847735528963682643108701 1442900823361380991165763)
              ·
                refine ⟨2164351235042071486748645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1442900823361380991165763 2164351235042071486748645)
                ·
                  refine ⟨405815856570388403765371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2164351235042071486748645 405815856570388403765371)
                  ·
                    rfl

theorem cell21_1778228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_1778228 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1778228 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1778228 prefixEnd_1778228 := by exact prefixLift 1778228
  have htrace : WordTrace (prefixWord ++ tailWord_1778228) baseStart_1778228 baseEnd_1778228 := by
    simpa [prefixWord, tailWord_1778228, baseEnd_1778228] using wordTrace_append hprefix tailTrace_1778228
  have hstable : (prefixWord ++ tailWord_1778228).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778228).length < 2 ^ (prefixWord ++ tailWord_1778228).sum := by decide
  have hdescent : baseEnd_1778228 < baseStart_1778228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778253 : List Nat := [1, 6, 1, 1, 2, 1, 1, 2, 6]
def baseStart_1778253 : Nat := 118140960795 + 1778253 * 2 ^ 59
def prefixEnd_1778253 : Nat := 4983230072969 + 3 ^ 40 * 1778253 * 2
def baseEnd_1778253 : Nat := 405821561910993915848653

theorem tailTrace_1778253 : CollatzResearch.WordTrace tailWord_1778253 prefixEnd_1778253 405821561910993915848653 := by
  unfold tailWord_1778253
  simp only [CollatzResearch.WordTrace]
  refine ⟨64858215226700557278603413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43238810151133704852402275 64858215226700557278603413)
  ·
    refine ⟨3040228838751588622434535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 64858215226700557278603413 3040228838751588622434535)
    ·
      refine ⟨4560343258127382933651803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3040228838751588622434535 4560343258127382933651803)
      ·
        refine ⟨6840514887191074400477705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4560343258127382933651803 6840514887191074400477705)
        ·
          refine ⟨5130386165393305800358279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6840514887191074400477705 5130386165393305800358279)
          ·
            refine ⟨7695579248089958700537419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5130386165393305800358279 7695579248089958700537419)
            ·
              refine ⟨11543368872134938050806129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7695579248089958700537419 11543368872134938050806129)
              ·
                refine ⟨8657526654101203538104597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11543368872134938050806129 8657526654101203538104597)
                ·
                  refine ⟨405821561910993915848653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8657526654101203538104597 405821561910993915848653)
                  ·
                    rfl

theorem cell21_1778253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_1778253 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1778253 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1778253 prefixEnd_1778253 := by exact prefixLift 1778253
  have htrace : WordTrace (prefixWord ++ tailWord_1778253) baseStart_1778253 baseEnd_1778253 := by
    simpa [prefixWord, tailWord_1778253, baseEnd_1778253] using wordTrace_append hprefix tailTrace_1778253
  have hstable : (prefixWord ++ tailWord_1778253).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778253).length < 2 ^ (prefixWord ++ tailWord_1778253).sum := by decide
  have hdescent : baseEnd_1778253 < baseStart_1778253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778332 : List Nat := [2, 2, 3, 2, 2, 1, 4, 2, 3]
def baseStart_1778332 : Nat := 118140960795 + 1778332 * 2 ^ 59
def prefixEnd_1778332 : Nat := 4983230072969 + 3 ^ 40 * 1778332 * 2
def baseEnd_1778332 : Nat := 405839590787307334031825

theorem tailTrace_1778332 : CollatzResearch.WordTrace tailWord_1778332 prefixEnd_1778332 405839590787307334031825 := by
  unfold tailWord_1778332
  simp only [CollatzResearch.WordTrace]
  refine ⟨32430548296707176885364625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43240731062276235847152833 32430548296707176885364625)
  ·
    refine ⟨24322911222530382664023469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32430548296707176885364625 24322911222530382664023469)
    ·
      refine ⟨9121091708448893499008801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24322911222530382664023469 9121091708448893499008801)
      ·
        refine ⟨6840818781336670124256601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9121091708448893499008801 6840818781336670124256601)
        ·
          refine ⟨5130614086002502593192451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6840818781336670124256601 5130614086002502593192451)
          ·
            refine ⟨7695921129003753889788677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5130614086002502593192451 7695921129003753889788677)
            ·
              refine ⟨1442985211688203854335377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7695921129003753889788677 1442985211688203854335377)
              ·
                refine ⟨1082238908766152890751533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1442985211688203854335377 1082238908766152890751533)
                ·
                  refine ⟨405839590787307334031825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1082238908766152890751533 405839590787307334031825)
                  ·
                    rfl

theorem cell21_1778332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 4, 2, 3].length) (baseStart_1778332 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1778332 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1778332 prefixEnd_1778332 := by exact prefixLift 1778332
  have htrace : WordTrace (prefixWord ++ tailWord_1778332) baseStart_1778332 baseEnd_1778332 := by
    simpa [prefixWord, tailWord_1778332, baseEnd_1778332] using wordTrace_append hprefix tailTrace_1778332
  have hstable : (prefixWord ++ tailWord_1778332).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778332).length < 2 ^ (prefixWord ++ tailWord_1778332).sum := by decide
  have hdescent : baseEnd_1778332 < baseStart_1778332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778447 : List Nat := [1, 1, 2, 1, 1, 1, 5, 3, 6]
def baseStart_1778447 : Nat := 118140960795 + 1778447 * 2 ^ 59
def prefixEnd_1778447 : Nat := 4983230072969 + 3 ^ 40 * 1778447 * 2
def baseEnd_1778447 : Nat := 405865835354092689614923

theorem tailTrace_1778447 : CollatzResearch.WordTrace tailWord_1778447 prefixEnd_1778447 405865835354092689614923 := by
  unfold tailWord_1778447
  simp only [CollatzResearch.WordTrace]
  refine ⟨64865290987997728411165595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43243527325331818940777063 64865290987997728411165595)
  ·
    refine ⟨97297936481996592616748393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64865290987997728411165595 97297936481996592616748393)
    ·
      refine ⟨72973452361497444462561295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97297936481996592616748393 72973452361497444462561295)
      ·
        refine ⟨109460178542246166693841943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72973452361497444462561295 109460178542246166693841943)
        ·
          refine ⟨164190267813369250040762915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109460178542246166693841943 164190267813369250040762915)
          ·
            refine ⟨246285401720053875061144373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164190267813369250040762915 246285401720053875061144373)
            ·
              refine ⟨23089256411255050786982285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 246285401720053875061144373 23089256411255050786982285)
              ·
                refine ⟨8658471154220644045118357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23089256411255050786982285 8658471154220644045118357)
                ·
                  refine ⟨405865835354092689614923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8658471154220644045118357 405865835354092689614923)
                  ·
                    rfl

theorem cell21_1778447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 3, 6].length) (baseStart_1778447 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1778447 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1778447 prefixEnd_1778447 := by exact prefixLift 1778447
  have htrace : WordTrace (prefixWord ++ tailWord_1778447) baseStart_1778447 baseEnd_1778447 := by
    simpa [prefixWord, tailWord_1778447, baseEnd_1778447] using wordTrace_append hprefix tailTrace_1778447
  have hstable : (prefixWord ++ tailWord_1778447).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778447).length < 2 ^ (prefixWord ++ tailWord_1778447).sum := by decide
  have hdescent : baseEnd_1778447 < baseStart_1778447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778605 : List Nat := [1, 5, 2, 3, 2, 1, 7]
def baseStart_1778605 : Nat := 118140960795 + 1778605 * 2 ^ 59
def prefixEnd_1778605 : Nat := 4983230072969 + 3 ^ 40 * 1778605 * 2
def baseEnd_1778605 : Nat := 45100210345191058442363

theorem tailTrace_1778605 : CollatzResearch.WordTrace tailWord_1778605 prefixEnd_1778605 45100210345191058442363 := by
  unfold tailWord_1778605
  simp only [CollatzResearch.WordTrace]
  refine ⟨64871053721425321395417269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43247369147616880930278179 64871053721425321395417269)
  ·
    refine ⟨6081661286383623880820369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 64871053721425321395417269 6081661286383623880820369)
    ·
      refine ⟨4561245964787717910615277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6081661286383623880820369 4561245964787717910615277)
      ·
        refine ⟨1710467236795394216480729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4561245964787717910615277 1710467236795394216480729)
        ·
          refine ⟨1282850427596545662360547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1710467236795394216480729 1282850427596545662360547)
          ·
            refine ⟨1924275641394818493540821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1282850427596545662360547 1924275641394818493540821)
            ·
              refine ⟨45100210345191058442363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1924275641394818493540821 45100210345191058442363)
              ·
                rfl

theorem cell21_1778605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 7].length) (baseStart_1778605 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1778605 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1778605 prefixEnd_1778605 := by exact prefixLift 1778605
  have htrace : WordTrace (prefixWord ++ tailWord_1778605) baseStart_1778605 baseEnd_1778605 := by
    simpa [prefixWord, tailWord_1778605, baseEnd_1778605] using wordTrace_append hprefix tailTrace_1778605
  have hstable : (prefixWord ++ tailWord_1778605).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778605).length < 2 ^ (prefixWord ++ tailWord_1778605).sum := by decide
  have hdescent : baseEnd_1778605 < baseStart_1778605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778737 : List Nat := [1, 2, 2, 3, 1, 2, 4, 1, 5]
def baseStart_1778737 : Nat := 118140960795 + 1778737 * 2 ^ 59
def prefixEnd_1778737 : Nat := 4983230072969 + 3 ^ 40 * 1778737 * 2
def baseEnd_1778737 : Nat := 405932017305116629780997

theorem tailTrace_1778737 : CollatzResearch.WordTrace tailWord_1778737 prefixEnd_1778737 405932017305116629780997 := by
  unfold tailWord_1778737
  simp only [CollatzResearch.WordTrace]
  refine ⟨64875868156947107939222465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43250578771298071959481643 64875868156947107939222465)
  ·
    refine ⟨48656901117710330954416849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64875868156947107939222465 48656901117710330954416849)
    ·
      refine ⟨36492675838282748215812637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48656901117710330954416849 36492675838282748215812637)
      ·
        refine ⟨13684753439356030580929739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36492675838282748215812637 13684753439356030580929739)
        ·
          refine ⟨20527130159034045871394609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13684753439356030580929739 20527130159034045871394609)
          ·
            refine ⟨15395347619275534403545957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20527130159034045871394609 15395347619275534403545957)
            ·
              refine ⟨2886627678614162700664867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15395347619275534403545957 2886627678614162700664867)
              ·
                refine ⟨4329941517921244050997301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2886627678614162700664867 4329941517921244050997301)
                ·
                  refine ⟨405932017305116629780997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4329941517921244050997301 405932017305116629780997)
                  ·
                    rfl

theorem cell21_1778737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 1, 5].length) (baseStart_1778737 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1778737 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1778737 prefixEnd_1778737 := by exact prefixLift 1778737
  have htrace : WordTrace (prefixWord ++ tailWord_1778737) baseStart_1778737 baseEnd_1778737 := by
    simpa [prefixWord, tailWord_1778737, baseEnd_1778737] using wordTrace_append hprefix tailTrace_1778737
  have hstable : (prefixWord ++ tailWord_1778737).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778737).length < 2 ^ (prefixWord ++ tailWord_1778737).sum := by decide
  have hdescent : baseEnd_1778737 < baseStart_1778737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778844 : List Nat := [2, 2, 3, 2, 1, 2, 1, 4, 4]
def baseStart_1778844 : Nat := 118140960795 + 1778844 * 2 ^ 59
def prefixEnd_1778844 : Nat := 4983230072969 + 3 ^ 40 * 1778844 * 2
def baseEnd_1778844 : Nat := 405956436162908221497445

theorem tailTrace_1778844 : CollatzResearch.WordTrace tailWord_1778844 prefixEnd_1778844 405956436162908221497445 := by
  unfold tailWord_1778844
  simp only [CollatzResearch.WordTrace]
  refine ⟨32439885383779732606683793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43253180511706310142245057 32439885383779732606683793)
  ·
    refine ⟨24329914037834799455012845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32439885383779732606683793 24329914037834799455012845)
    ·
      refine ⟨9123717764188049795629817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24329914037834799455012845 9123717764188049795629817)
      ·
        refine ⟨6842788323141037346722363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9123717764188049795629817 6842788323141037346722363)
        ·
          refine ⟨10264182484711556020083545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6842788323141037346722363 10264182484711556020083545)
          ·
            refine ⟨7698136863533667015062659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10264182484711556020083545 7698136863533667015062659)
            ·
              refine ⟨11547205295300500522593989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7698136863533667015062659 11547205295300500522593989)
              ·
                refine ⟨2165100992868843847986373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11547205295300500522593989 2165100992868843847986373)
                ·
                  refine ⟨405956436162908221497445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2165100992868843847986373 405956436162908221497445)
                  ·
                    rfl

theorem cell21_1778844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 4, 4].length) (baseStart_1778844 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1778844 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1778844 prefixEnd_1778844 := by exact prefixLift 1778844
  have htrace : WordTrace (prefixWord ++ tailWord_1778844) baseStart_1778844 baseEnd_1778844 := by
    simpa [prefixWord, tailWord_1778844, baseEnd_1778844] using wordTrace_append hprefix tailTrace_1778844
  have hstable : (prefixWord ++ tailWord_1778844).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778844).length < 2 ^ (prefixWord ++ tailWord_1778844).sum := by decide
  have hdescent : baseEnd_1778844 < baseStart_1778844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778847 : List Nat := [1, 1, 2, 6, 2, 1, 1, 4, 3]
def baseStart_1778847 : Nat := 118140960795 + 1778847 * 2 ^ 59
def prefixEnd_1778847 : Nat := 4983230072969 + 3 ^ 40 * 1778847 * 2
def baseEnd_1778847 : Nat := 405957120803780882947439

theorem tailTrace_1778847 : CollatzResearch.WordTrace tailWord_1778847 prefixEnd_1778847 405957120803780882947439 := by
  unfold tailWord_1778847
  simp only [CollatzResearch.WordTrace]
  refine ⟨64879880186548596725726795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43253253457699064483817863 64879880186548596725726795)
  ·
    refine ⟨97319820279822895088590193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64879880186548596725726795 97319820279822895088590193)
    ·
      refine ⟨72989865209867171316442645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97319820279822895088590193 72989865209867171316442645)
      ·
        refine ⟨3421399931712523655458249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 72989865209867171316442645 3421399931712523655458249)
        ·
          refine ⟨2566049948784392741593687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3421399931712523655458249 2566049948784392741593687)
          ·
            refine ⟨3849074923176589112390531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2566049948784392741593687 3849074923176589112390531)
            ·
              refine ⟨5773612384764883668585797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3849074923176589112390531 5773612384764883668585797)
              ·
                refine ⟨1082552322143415687859837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5773612384764883668585797 1082552322143415687859837)
                ·
                  refine ⟨405957120803780882947439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1082552322143415687859837 405957120803780882947439)
                  ·
                    rfl

theorem cell21_1778847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 4, 3].length) (baseStart_1778847 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1778847 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1778847 prefixEnd_1778847 := by exact prefixLift 1778847
  have htrace : WordTrace (prefixWord ++ tailWord_1778847) baseStart_1778847 baseEnd_1778847 := by
    simpa [prefixWord, tailWord_1778847, baseEnd_1778847] using wordTrace_append hprefix tailTrace_1778847
  have hstable : (prefixWord ++ tailWord_1778847).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778847).length < 2 ^ (prefixWord ++ tailWord_1778847).sum := by decide
  have hdescent : baseEnd_1778847 < baseStart_1778847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778940 : List Nat := [2, 2, 2, 1, 6, 1, 1, 3, 3]
def baseStart_1778940 : Nat := 118140960795 + 1778940 * 2 ^ 59
def prefixEnd_1778940 : Nat := 4983230072969 + 3 ^ 40 * 1778940 * 2
def baseEnd_1778940 : Nat := 405978344670833387897249

theorem tailTrace_1778940 : CollatzResearch.WordTrace tailWord_1778940 prefixEnd_1778940 405978344670833387897249 := by
  unfold tailWord_1778940
  simp only [CollatzResearch.WordTrace]
  refine ⟨32441636087605836804431137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43255514783474449072574849 32441636087605836804431137)
  ·
    refine ⟨24331227065704377603323353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32441636087605836804431137 24331227065704377603323353)
    ·
      refine ⟨18248420299278283202492515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24331227065704377603323353 18248420299278283202492515)
      ·
        refine ⟨27372630448917424803738773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18248420299278283202492515 27372630448917424803738773)
        ·
          refine ⟨1283092052293004287675255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 27372630448917424803738773 1283092052293004287675255)
          ·
            refine ⟨1924638078439506431512883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1283092052293004287675255 1924638078439506431512883)
            ·
              refine ⟨2886957117659259647269325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1924638078439506431512883 2886957117659259647269325)
              ·
                refine ⟨1082608919122222367725997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2886957117659259647269325 1082608919122222367725997)
                ·
                  refine ⟨405978344670833387897249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1082608919122222367725997 405978344670833387897249)
                  ·
                    rfl

theorem cell21_1778940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 3, 3].length) (baseStart_1778940 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1778940 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1778940 prefixEnd_1778940 := by exact prefixLift 1778940
  have htrace : WordTrace (prefixWord ++ tailWord_1778940) baseStart_1778940 baseEnd_1778940 := by
    simpa [prefixWord, tailWord_1778940, baseEnd_1778940] using wordTrace_append hprefix tailTrace_1778940
  have hstable : (prefixWord ++ tailWord_1778940).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778940).length < 2 ^ (prefixWord ++ tailWord_1778940).sum := by decide
  have hdescent : baseEnd_1778940 < baseStart_1778940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779024 : List Nat := [2, 1, 1, 1, 1, 5, 2, 3, 5]
def baseStart_1779024 : Nat := 118140960795 + 1779024 * 2 ^ 59
def prefixEnd_1779024 : Nat := 4983230072969 + 3 ^ 40 * 1779024 * 2
def baseEnd_1779024 : Nat := 405997514615267908497077

theorem tailTrace_1779024 : CollatzResearch.WordTrace tailWord_1779024 prefixEnd_1779024 405997514615267908497077 := by
  unfold tailWord_1779024
  simp only [CollatzResearch.WordTrace]
  refine ⟨32443167953453677977460063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43257557271271570636613417 32443167953453677977460063)
  ·
    refine ⟨48664751930180516966190095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32443167953453677977460063 48664751930180516966190095)
    ·
      refine ⟨72997127895270775449285143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48664751930180516966190095 72997127895270775449285143)
      ·
        refine ⟨109495691842906163173927715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72997127895270775449285143 109495691842906163173927715)
        ·
          refine ⟨164243537764359244760891573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109495691842906163173927715 164243537764359244760891573)
          ·
            refine ⟨15397831665408679196333585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 164243537764359244760891573 15397831665408679196333585)
            ·
              refine ⟨11548373749056509397250189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15397831665408679196333585 11548373749056509397250189)
              ·
                refine ⟨4330640155896191023968821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11548373749056509397250189 4330640155896191023968821)
                ·
                  refine ⟨405997514615267908497077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4330640155896191023968821 405997514615267908497077)
                  ·
                    rfl

theorem cell21_1779024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 3, 5].length) (baseStart_1779024 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1779024 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1779024 prefixEnd_1779024 := by exact prefixLift 1779024
  have htrace : WordTrace (prefixWord ++ tailWord_1779024) baseStart_1779024 baseEnd_1779024 := by
    simpa [prefixWord, tailWord_1779024, baseEnd_1779024] using wordTrace_append hprefix tailTrace_1779024
  have hstable : (prefixWord ++ tailWord_1779024).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779024).length < 2 ^ (prefixWord ++ tailWord_1779024).sum := by decide
  have hdescent : baseEnd_1779024 < baseStart_1779024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779058 : List Nat := [3, 2, 1, 2, 1, 2, 4, 3, 3]
def baseStart_1779058 : Nat := 118140960795 + 1779058 * 2 ^ 59
def prefixEnd_1779058 : Nat := 4983230072969 + 3 ^ 40 * 1779058 * 2
def baseEnd_1779058 : Nat := 406005273878491404930341

theorem tailTrace_1779058 : CollatzResearch.WordTrace tailWord_1779058 prefixEnd_1779058 406005273878491404930341 := by
  unfold tailWord_1779058
  simp only [CollatzResearch.WordTrace]
  refine ⟨16221893997196044940414457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43258383992522786507771885 16221893997196044940414457)
  ·
    refine ⟨12166420497897033705310843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16221893997196044940414457 12166420497897033705310843)
    ·
      refine ⟨18249630746845550557966265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12166420497897033705310843 18249630746845550557966265)
      ·
        refine ⟨13687223060134162918474699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18249630746845550557966265 13687223060134162918474699)
        ·
          refine ⟨20530834590201244377712049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13687223060134162918474699 20530834590201244377712049)
          ·
            refine ⟨15398125942650933283284037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20530834590201244377712049 15398125942650933283284037)
            ·
              refine ⟨2887148614247049990615757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15398125942650933283284037 2887148614247049990615757)
              ·
                refine ⟨1082680730342643746480909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2887148614247049990615757 1082680730342643746480909)
                ·
                  refine ⟨406005273878491404930341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1082680730342643746480909 406005273878491404930341)
                  ·
                    rfl

theorem cell21_1779058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 3, 3].length) (baseStart_1779058 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1779058 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1779058 prefixEnd_1779058 := by exact prefixLift 1779058
  have htrace : WordTrace (prefixWord ++ tailWord_1779058) baseStart_1779058 baseEnd_1779058 := by
    simpa [prefixWord, tailWord_1779058, baseEnd_1779058] using wordTrace_append hprefix tailTrace_1779058
  have hstable : (prefixWord ++ tailWord_1779058).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779058).length < 2 ^ (prefixWord ++ tailWord_1779058).sum := by decide
  have hdescent : baseEnd_1779058 < baseStart_1779058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779069 : List Nat := [1, 4, 1, 1, 2, 2, 10]
def baseStart_1779069 : Nat := 118140960795 + 1779069 * 2 ^ 59
def prefixEnd_1779069 : Nat := 4983230072969 + 3 ^ 40 * 1779069 * 2
def baseEnd_1779069 : Nat := 45111976025373092249665

theorem tailTrace_1779069 : CollatzResearch.WordTrace tailWord_1779069 prefixEnd_1779069 45111976025373092249665 := by
  unfold tailWord_1779069
  simp only [CollatzResearch.WordTrace]
  refine ⟨64887977191744328640308261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43258651461162885760205507 64887977191744328640308261)
  ·
    refine ⟨12166495723452061620057799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64887977191744328640308261 12166495723452061620057799)
    ·
      refine ⟨18249743585178092430086699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12166495723452061620057799 18249743585178092430086699)
      ·
        refine ⟨27374615377767138645130049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18249743585178092430086699 27374615377767138645130049)
        ·
          refine ⟨20530961533325353983847537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27374615377767138645130049 20530961533325353983847537)
          ·
            refine ⟨15398221149994015487885653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20530961533325353983847537 15398221149994015487885653)
            ·
              refine ⟨45111976025373092249665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15398221149994015487885653 45111976025373092249665)
              ·
                rfl

theorem cell21_1779069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 10].length) (baseStart_1779069 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1779069 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1779069 prefixEnd_1779069 := by exact prefixLift 1779069
  have htrace : WordTrace (prefixWord ++ tailWord_1779069) baseStart_1779069 baseEnd_1779069 := by
    simpa [prefixWord, tailWord_1779069, baseEnd_1779069] using wordTrace_append hprefix tailTrace_1779069
  have hstable : (prefixWord ++ tailWord_1779069).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779069).length < 2 ^ (prefixWord ++ tailWord_1779069).sum := by decide
  have hdescent : baseEnd_1779069 < baseStart_1779069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779103 : List Nat := [1, 1, 2, 5, 1, 4, 2, 5]
def baseStart_1779103 : Nat := 118140960795 + 1779103 * 2 ^ 59
def prefixEnd_1779103 : Nat := 4983230072969 + 3 ^ 40 * 1779103 * 2
def baseEnd_1779103 : Nat := 135338514497193775560083

theorem tailTrace_1779103 : CollatzResearch.WordTrace tailWord_1779103 prefixEnd_1779103 135338514497193775560083 := by
  unfold tailWord_1779103
  simp only [CollatzResearch.WordTrace]
  refine ⟨64889217273621152447045963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43259478182414101631363975 64889217273621152447045963)
  ·
    refine ⟨97333825910431728670568945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64889217273621152447045963 97333825910431728670568945)
    ·
      refine ⟨73000369432823796502926709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97333825910431728670568945 73000369432823796502926709)
      ·
        refine ⟨6843784634327230922149379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 73000369432823796502926709 6843784634327230922149379)
        ·
          refine ⟨10265676951490846383224069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6843784634327230922149379 10265676951490846383224069)
          ·
            refine ⟨1924814428404533696854513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10265676951490846383224069 1924814428404533696854513)
            ·
              refine ⟨1443610821303400272640885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1924814428404533696854513 1443610821303400272640885)
              ·
                refine ⟨135338514497193775560083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1443610821303400272640885 135338514497193775560083)
                ·
                  rfl

theorem cell21_1779103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 2, 5].length) (baseStart_1779103 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1779103 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1779103 prefixEnd_1779103 := by exact prefixLift 1779103
  have htrace : WordTrace (prefixWord ++ tailWord_1779103) baseStart_1779103 baseEnd_1779103 := by
    simpa [prefixWord, tailWord_1779103, baseEnd_1779103] using wordTrace_append hprefix tailTrace_1779103
  have hstable : (prefixWord ++ tailWord_1779103).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779103).length < 2 ^ (prefixWord ++ tailWord_1779103).sum := by decide
  have hdescent : baseEnd_1779103 < baseStart_1779103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779148 : List Nat := [2, 2, 1, 4, 2, 2, 1, 3, 4]
def baseStart_1779148 : Nat := 118140960795 + 1779148 * 2 ^ 59
def prefixEnd_1779148 : Nat := 4983230072969 + 3 ^ 40 * 1779148 * 2
def baseEnd_1779148 : Nat := 406025813104671248430157

theorem tailTrace_1779148 : CollatzResearch.WordTrace tailWord_1779148 prefixEnd_1779148 406025813104671248430157 := by
  unfold tailWord_1779148
  simp only [CollatzResearch.WordTrace]
  refine ⟨32445429279229062566217049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43260572372305416754956065 32445429279229062566217049)
  ·
    refine ⟨24334071959421796924662787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32445429279229062566217049 24334071959421796924662787)
    ·
      refine ⟨36501107939132695386994181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24334071959421796924662787 36501107939132695386994181)
      ·
        refine ⟨6843957738587380385061409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36501107939132695386994181 6843957738587380385061409)
        ·
          refine ⟨5132968303940535288796057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6843957738587380385061409 5132968303940535288796057)
          ·
            refine ⟨3849726227955401466597043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5132968303940535288796057 3849726227955401466597043)
            ·
              refine ⟨5774589341933102199895565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3849726227955401466597043 5774589341933102199895565)
              ·
                refine ⟨2165471003224913324960837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5774589341933102199895565 2165471003224913324960837)
                ·
                  refine ⟨406025813104671248430157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2165471003224913324960837 406025813104671248430157)
                  ·
                    rfl

theorem cell21_1779148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 3, 4].length) (baseStart_1779148 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1779148 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1779148 prefixEnd_1779148 := by exact prefixLift 1779148
  have htrace : WordTrace (prefixWord ++ tailWord_1779148) baseStart_1779148 baseEnd_1779148 := by
    simpa [prefixWord, tailWord_1779148, baseEnd_1779148] using wordTrace_append hprefix tailTrace_1779148
  have hstable : (prefixWord ++ tailWord_1779148).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779148).length < 2 ^ (prefixWord ++ tailWord_1779148).sum := by decide
  have hdescent : baseEnd_1779148 < baseStart_1779148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779213 : List Nat := [1, 7, 1, 1, 2, 1, 3, 5]
def baseStart_1779213 : Nat := 118140960795 + 1779213 * 2 ^ 59
def prefixEnd_1779213 : Nat := 4983230072969 + 3 ^ 40 * 1779213 * 2
def baseEnd_1779213 : Nat := 135346882330081859948897

theorem tailTrace_1779213 : CollatzResearch.WordTrace tailWord_1779213 prefixEnd_1779213 135346882330081859948897 := by
  unfold tailWord_1779213
  simp only [CollatzResearch.WordTrace]
  refine ⟨64893229303222641233550293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43262152868815094155700195 64893229303222641233550293)
  ·
    refine ⟨1520935061794280653911335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 64893229303222641233550293 1520935061794280653911335)
    ·
      refine ⟨2281402592691420980867003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1520935061794280653911335 2281402592691420980867003)
      ·
        refine ⟨3422103889037131471300505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2281402592691420980867003 3422103889037131471300505)
        ·
          refine ⟨2566577916777848603475379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3422103889037131471300505 2566577916777848603475379)
          ·
            refine ⟨3849866875166772905213069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2566577916777848603475379 3849866875166772905213069)
            ·
              refine ⟨1443700078187539839454901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3849866875166772905213069 1443700078187539839454901)
              ·
                refine ⟨135346882330081859948897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1443700078187539839454901 135346882330081859948897)
                ·
                  rfl

theorem cell21_1779213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 3, 5].length) (baseStart_1779213 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1779213 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1779213 prefixEnd_1779213 := by exact prefixLift 1779213
  have htrace : WordTrace (prefixWord ++ tailWord_1779213) baseStart_1779213 baseEnd_1779213 := by
    simpa [prefixWord, tailWord_1779213, baseEnd_1779213] using wordTrace_append hprefix tailTrace_1779213
  have hstable : (prefixWord ++ tailWord_1779213).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779213).length < 2 ^ (prefixWord ++ tailWord_1779213).sum := by decide
  have hdescent : baseEnd_1779213 < baseStart_1779213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779314 : List Nat := [3, 2, 1, 2, 3, 2, 2, 6]
def baseStart_1779314 : Nat := 118140960795 + 1779314 * 2 ^ 59
def prefixEnd_1779314 : Nat := 4983230072969 + 3 ^ 40 * 1779314 * 2
def baseEnd_1779314 : Nat := 135354565522097282887717

theorem tailTrace_1779314 : CollatzResearch.WordTrace tailWord_1779314 prefixEnd_1779314 135354565522097282887717 := by
  unfold tailWord_1779314
  simp only [CollatzResearch.WordTrace]
  refine ⟨16224228268964183870744249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43264608717237823655317997 16224228268964183870744249)
  ·
    refine ⟨12168171201723137903058187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16224228268964183870744249 12168171201723137903058187)
    ·
      refine ⟨18252256802584706854587281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12168171201723137903058187 18252256802584706854587281)
      ·
        refine ⟨13689192601938530140940461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18252256802584706854587281 13689192601938530140940461)
        ·
          refine ⟨5133447225726948802852673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13689192601938530140940461 5133447225726948802852673)
          ·
            refine ⟨3850085419295211602139505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5133447225726948802852673 3850085419295211602139505)
            ·
              refine ⟨2887564064471408701604629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3850085419295211602139505 2887564064471408701604629)
              ·
                refine ⟨135354565522097282887717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2887564064471408701604629 135354565522097282887717)
                ·
                  rfl

theorem cell21_1779314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 6].length) (baseStart_1779314 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1779314 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1779314 prefixEnd_1779314 := by exact prefixLift 1779314
  have htrace : WordTrace (prefixWord ++ tailWord_1779314) baseStart_1779314 baseEnd_1779314 := by
    simpa [prefixWord, tailWord_1779314, baseEnd_1779314] using wordTrace_append hprefix tailTrace_1779314
  have hstable : (prefixWord ++ tailWord_1779314).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779314).length < 2 ^ (prefixWord ++ tailWord_1779314).sum := by decide
  have hdescent : baseEnd_1779314 < baseStart_1779314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779317 : List Nat := [1, 3, 4, 2, 1, 1, 4, 1, 4]
def baseStart_1779317 : Nat := 118140960795 + 1779317 * 2 ^ 59
def prefixEnd_1779317 : Nat := 4983230072969 + 3 ^ 40 * 1779317 * 2
def baseEnd_1779317 : Nat := 406064381207164510113145

theorem tailTrace_1779317 : CollatzResearch.WordTrace tailWord_1779317 prefixEnd_1779317 406064381207164510113145 := by
  unfold tailWord_1779317
  simp only [CollatzResearch.WordTrace]
  refine ⟨64897022494845866995336205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43264681663230577996890803 64897022494845866995336205)
  ·
    refine ⟨24336383435567200123251077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64897022494845866995336205 24336383435567200123251077)
    ·
      refine ⟨4563071894168850023109577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24336383435567200123251077 4563071894168850023109577)
      ·
        refine ⟨3422303920626637517332183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4563071894168850023109577 3422303920626637517332183)
        ·
          refine ⟨5133455880939956275998275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3422303920626637517332183 5133455880939956275998275)
          ·
            refine ⟨7700183821409934413997413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5133455880939956275998275 7700183821409934413997413)
            ·
              refine ⟨1443784466514362702624515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7700183821409934413997413 1443784466514362702624515)
              ·
                refine ⟨2165676699771544053936773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1443784466514362702624515 2165676699771544053936773)
                ·
                  refine ⟨406064381207164510113145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2165676699771544053936773 406064381207164510113145)
                  ·
                    rfl

theorem cell21_1779317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 4, 1, 4].length) (baseStart_1779317 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1779317 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1779317 prefixEnd_1779317 := by exact prefixLift 1779317
  have htrace : WordTrace (prefixWord ++ tailWord_1779317) baseStart_1779317 baseEnd_1779317 := by
    simpa [prefixWord, tailWord_1779317, baseEnd_1779317] using wordTrace_append hprefix tailTrace_1779317
  have hstable : (prefixWord ++ tailWord_1779317).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779317).length < 2 ^ (prefixWord ++ tailWord_1779317).sum := by decide
  have hdescent : baseEnd_1779317 < baseStart_1779317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779480 : List Nat := [2, 1, 2, 3, 1, 1, 5, 1, 5]
def baseStart_1779480 : Nat := 118140960795 + 1779480 * 2 ^ 59
def prefixEnd_1779480 : Nat := 4983230072969 + 3 ^ 40 * 1779480 * 2
def baseEnd_1779480 : Nat := 406101580027912448896145

theorem tailTrace_1779480 : CollatzResearch.WordTrace tailWord_1779480 prefixEnd_1779480 406101580027912448896145 := by
  unfold tailWord_1779480
  simp only [CollatzResearch.WordTrace]
  refine ⟨32451483796627672916759947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43268645062170230555679929 32451483796627672916759947)
  ·
    refine ⟨48677225694941509375139921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32451483796627672916759947 48677225694941509375139921)
    ·
      refine ⟨36507919271206132031354941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48677225694941509375139921 36507919271206132031354941)
      ·
        refine ⟨13690469726702299511758103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36507919271206132031354941 13690469726702299511758103)
        ·
          refine ⟨20535704590053449267637155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13690469726702299511758103 20535704590053449267637155)
          ·
            refine ⟨30803556885080173901455733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20535704590053449267637155 30803556885080173901455733)
            ·
              refine ⟨2887833457976266303261475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30803556885080173901455733 2887833457976266303261475)
              ·
                refine ⟨4331750186964399454892213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2887833457976266303261475 4331750186964399454892213)
                ·
                  refine ⟨406101580027912448896145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4331750186964399454892213 406101580027912448896145)
                  ·
                    rfl

theorem cell21_1779480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 1, 5].length) (baseStart_1779480 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1779480 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1779480 prefixEnd_1779480 := by exact prefixLift 1779480
  have htrace : WordTrace (prefixWord ++ tailWord_1779480) baseStart_1779480 baseEnd_1779480 := by
    simpa [prefixWord, tailWord_1779480, baseEnd_1779480] using wordTrace_append hprefix tailTrace_1779480
  have hstable : (prefixWord ++ tailWord_1779480).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779480).length < 2 ^ (prefixWord ++ tailWord_1779480).sum := by decide
  have hdescent : baseEnd_1779480 < baseStart_1779480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779486 : List Nat := [4, 3, 2, 2, 1, 1, 1, 3, 4]
def baseStart_1779486 : Nat := 118140960795 + 1779486 * 2 ^ 59
def prefixEnd_1779486 : Nat := 4983230072969 + 3 ^ 40 * 1779486 * 2
def baseEnd_1779486 : Nat := 406102949309657771796133

theorem tailTrace_1779486 : CollatzResearch.WordTrace tailWord_1779486 prefixEnd_1779486 406102949309657771796133 := by
  unfold tailWord_1779486
  simp only [CollatzResearch.WordTrace]
  refine ⟨8112898303904201107279789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43268790954155739238825541 8112898303904201107279789)
  ·
    refine ⟨3042336863964075415229921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8112898303904201107279789 3042336863964075415229921)
    ·
      refine ⟨2281752647973056561422441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3042336863964075415229921 2281752647973056561422441)
      ·
        refine ⟨1711314485979792421066831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2281752647973056561422441 1711314485979792421066831)
        ·
          refine ⟨2566971728969688631600247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1711314485979792421066831 2566971728969688631600247)
          ·
            refine ⟨3850457593454532947400371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2566971728969688631600247 3850457593454532947400371)
            ·
              refine ⟨5775686390181799421100557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3850457593454532947400371 5775686390181799421100557)
              ·
                refine ⟨2165882396318174782912709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5775686390181799421100557 2165882396318174782912709)
                ·
                  refine ⟨406102949309657771796133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2165882396318174782912709 406102949309657771796133)
                  ·
                    rfl

theorem cell21_1779486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_1779486 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1779486 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1779486 prefixEnd_1779486 := by exact prefixLift 1779486
  have htrace : WordTrace (prefixWord ++ tailWord_1779486) baseStart_1779486 baseEnd_1779486 := by
    simpa [prefixWord, tailWord_1779486, baseEnd_1779486] using wordTrace_append hprefix tailTrace_1779486
  have hstable : (prefixWord ++ tailWord_1779486).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779486).length < 2 ^ (prefixWord ++ tailWord_1779486).sum := by decide
  have hdescent : baseEnd_1779486 < baseStart_1779486 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779570 : List Nat := [3, 2, 1, 2, 1, 1, 1, 4, 6]
def baseStart_1779570 : Nat := 118140960795 + 1779570 * 2 ^ 59
def prefixEnd_1779570 : Nat := 4983230072969 + 3 ^ 40 * 1779570 * 2
def baseEnd_1779570 : Nat := 406122119254092292395961

theorem tailTrace_1779570 : CollatzResearch.WordTrace tailWord_1779570 prefixEnd_1779570 406122119254092292395961 := by
  unfold tailWord_1779570
  simp only [CollatzResearch.WordTrace]
  refine ⟨16226562540732322801074041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43270833441952860802864109 16226562540732322801074041)
  ·
    refine ⟨12169921905549242100805531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16226562540732322801074041 12169921905549242100805531)
    ·
      refine ⟨18254882858323863151208297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12169921905549242100805531 18254882858323863151208297)
      ·
        refine ⟨13691162143742897363406223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18254882858323863151208297 13691162143742897363406223)
        ·
          refine ⟨20536743215614346045109335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13691162143742897363406223 20536743215614346045109335)
          ·
            refine ⟨30805114823421519067664003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20536743215614346045109335 30805114823421519067664003)
            ·
              refine ⟨46207672235132278601496005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30805114823421519067664003 46207672235132278601496005)
              ·
                refine ⟨8663938544087302237780501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46207672235132278601496005 8663938544087302237780501)
                ·
                  refine ⟨406122119254092292395961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8663938544087302237780501 406122119254092292395961)
                  ·
                    rfl

theorem cell21_1779570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 4, 6].length) (baseStart_1779570 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1779570 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1779570 prefixEnd_1779570 := by exact prefixLift 1779570
  have htrace : WordTrace (prefixWord ++ tailWord_1779570) baseStart_1779570 baseEnd_1779570 := by
    simpa [prefixWord, tailWord_1779570, baseEnd_1779570] using wordTrace_append hprefix tailTrace_1779570
  have hstable : (prefixWord ++ tailWord_1779570).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779570).length < 2 ^ (prefixWord ++ tailWord_1779570).sum := by decide
  have hdescent : baseEnd_1779570 < baseStart_1779570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779584 : List Nat := [2, 1, 1, 2, 1, 2, 12]
def baseStart_1779584 : Nat := 118140960795 + 1779584 * 2 ^ 59
def prefixEnd_1779584 : Nat := 4983230072969 + 3 ^ 40 * 1779584 * 2
def baseEnd_1779584 : Nat := 45125034916092375462511

theorem tailTrace_1779584 : CollatzResearch.WordTrace tailWord_1779584 prefixEnd_1779584 45125034916092375462511 := by
  unfold tailWord_1779584
  simp only [CollatzResearch.WordTrace]
  refine ⟨32453380392439285797652903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43271173856585714396870537 32453380392439285797652903)
  ·
    refine ⟨48680070588658928696479355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32453380392439285797652903 48680070588658928696479355)
    ·
      refine ⟨73020105882988393044719033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48680070588658928696479355 73020105882988393044719033)
      ·
        refine ⟨54765079412241294783539275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73020105882988393044719033 54765079412241294783539275)
        ·
          refine ⟨82147619118361942175308913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54765079412241294783539275 82147619118361942175308913)
          ·
            refine ⟨61610714338771456631481685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82147619118361942175308913 61610714338771456631481685)
            ·
              refine ⟨45125034916092375462511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 61610714338771456631481685 45125034916092375462511)
              ·
                rfl

theorem cell21_1779584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 12].length) (baseStart_1779584 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1779584 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1779584 prefixEnd_1779584 := by exact prefixLift 1779584
  have htrace : WordTrace (prefixWord ++ tailWord_1779584) baseStart_1779584 baseEnd_1779584 := by
    simpa [prefixWord, tailWord_1779584, baseEnd_1779584] using wordTrace_append hprefix tailTrace_1779584
  have hstable : (prefixWord ++ tailWord_1779584).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779584).length < 2 ^ (prefixWord ++ tailWord_1779584).sum := by decide
  have hdescent : baseEnd_1779584 < baseStart_1779584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779587 : List Nat := [1, 1, 1, 3, 4, 2, 3, 2, 4]
def baseStart_1779587 : Nat := 118140960795 + 1779587 * 2 ^ 59
def prefixEnd_1779587 : Nat := 4983230072969 + 3 ^ 40 * 1779587 * 2
def baseEnd_1779587 : Nat := 406125998885704040612593

theorem tailTrace_1779587 : CollatzResearch.WordTrace tailWord_1779587 prefixEnd_1779587 406125998885704040612593 := by
  unfold tailWord_1779587
  simp only [CollatzResearch.WordTrace]
  refine ⟨64906870203867703107665015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43271246802578468738443343 64906870203867703107665015)
  ·
    refine ⟨97360305305801554661497523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64906870203867703107665015 97360305305801554661497523)
    ·
      refine ⟨146040457958702331992246285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97360305305801554661497523 146040457958702331992246285)
      ·
        refine ⟨54765171734513374497092357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146040457958702331992246285 54765171734513374497092357)
        ·
          refine ⟨10268469700221257718204817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54765171734513374497092357 10268469700221257718204817)
          ·
            refine ⟨7701352275165943288653613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10268469700221257718204817 7701352275165943288653613)
            ·
              refine ⟨2888007103187228733245105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7701352275165943288653613 2888007103187228733245105)
              ·
                refine ⟨2166005327390421549933829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2888007103187228733245105 2166005327390421549933829)
                ·
                  refine ⟨406125998885704040612593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2166005327390421549933829 406125998885704040612593)
                  ·
                    rfl

theorem cell21_1779587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 2, 4].length) (baseStart_1779587 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1779587 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1779587 prefixEnd_1779587 := by exact prefixLift 1779587
  have htrace : WordTrace (prefixWord ++ tailWord_1779587) baseStart_1779587 baseEnd_1779587 := by
    simpa [prefixWord, tailWord_1779587, baseEnd_1779587] using wordTrace_append hprefix tailTrace_1779587
  have hstable : (prefixWord ++ tailWord_1779587).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779587).length < 2 ^ (prefixWord ++ tailWord_1779587).sum := by decide
  have hdescent : baseEnd_1779587 < baseStart_1779587 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779618 : List Nat := [3, 3, 1, 2, 3, 1, 1, 7]
def baseStart_1779618 : Nat := 118140960795 + 1779618 * 2 ^ 59
def prefixEnd_1779618 : Nat := 4983230072969 + 3 ^ 40 * 1779618 * 2
def baseEnd_1779618 : Nat := 135377691169351625198621

theorem tailTrace_1779618 : CollatzResearch.WordTrace tailWord_1779618 prefixEnd_1779618 135377691169351625198621 := by
  unfold tailWord_1779618
  simp only [CollatzResearch.WordTrace]
  refine ⟨16227000216688848850510877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43272000577836930268029005 16227000216688848850510877)
  ·
    refine ⟨6085125081258318318941579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16227000216688848850510877 6085125081258318318941579)
    ·
      refine ⟨9127687621887477478412369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6085125081258318318941579 9127687621887477478412369)
      ·
        refine ⟨6845765716415608108809277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9127687621887477478412369 6845765716415608108809277)
        ·
          refine ⟨2567162143655853040803479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6845765716415608108809277 2567162143655853040803479)
          ·
            refine ⟨3850743215483779561205219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2567162143655853040803479 3850743215483779561205219)
            ·
              refine ⟨5776114823225669341807829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3850743215483779561205219 5776114823225669341807829)
              ·
                refine ⟨135377691169351625198621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5776114823225669341807829 135377691169351625198621)
                ·
                  rfl

theorem cell21_1779618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 7].length) (baseStart_1779618 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1779618 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1779618 prefixEnd_1779618 := by exact prefixLift 1779618
  have htrace : WordTrace (prefixWord ++ tailWord_1779618) baseStart_1779618 baseEnd_1779618 := by
    simpa [prefixWord, tailWord_1779618, baseEnd_1779618] using wordTrace_append hprefix tailTrace_1779618
  have hstable : (prefixWord ++ tailWord_1779618).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779618).length < 2 ^ (prefixWord ++ tailWord_1779618).sum := by decide
  have hdescent : baseEnd_1779618 < baseStart_1779618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779624 : List Nat := [2, 1, 6, 2, 1, 2, 1, 3, 3]
def baseStart_1779624 : Nat := 118140960795 + 1779624 * 2 ^ 59
def prefixEnd_1779624 : Nat := 4983230072969 + 3 ^ 40 * 1779624 * 2
def baseEnd_1779624 : Nat := 406134442789800198495851

theorem tailTrace_1779624 : CollatzResearch.WordTrace tailWord_1779624 prefixEnd_1779624 406134442789800198495851 := by
  unfold tailWord_1779624
  simp only [CollatzResearch.WordTrace]
  refine ⟨32454109852366829213380963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43272146469822438951174617 32454109852366829213380963)
  ·
    refine ⟨48681164778550243820071445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32454109852366829213380963 48681164778550243820071445)
    ·
      refine ⟨2281929598994542679065849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 48681164778550243820071445 2281929598994542679065849)
      ·
        refine ⟨1711447199245907009299387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2281929598994542679065849 1711447199245907009299387)
        ·
          refine ⟨2567170798868860513949081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1711447199245907009299387 2567170798868860513949081)
          ·
            refine ⟨1925378099151645385461811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2567170798868860513949081 1925378099151645385461811)
            ·
              refine ⟨2888067148727468078192717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1925378099151645385461811 2888067148727468078192717)
              ·
                refine ⟨1083025180772800529322269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2888067148727468078192717 1083025180772800529322269)
                ·
                  refine ⟨406134442789800198495851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1083025180772800529322269 406134442789800198495851)
                  ·
                    rfl

theorem cell21_1779624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 3, 3].length) (baseStart_1779624 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1779624 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1779624 prefixEnd_1779624 := by exact prefixLift 1779624
  have htrace : WordTrace (prefixWord ++ tailWord_1779624) baseStart_1779624 baseEnd_1779624 := by
    simpa [prefixWord, tailWord_1779624, baseEnd_1779624] using wordTrace_append hprefix tailTrace_1779624
  have hstable : (prefixWord ++ tailWord_1779624).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779624).length < 2 ^ (prefixWord ++ tailWord_1779624).sum := by decide
  have hdescent : baseEnd_1779624 < baseStart_1779624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779767 : List Nat := [1, 1, 3, 1, 2, 2, 3, 3, 5]
def baseStart_1779767 : Nat := 118140960795 + 1779767 * 2 ^ 59
def prefixEnd_1779767 : Nat := 4983230072969 + 3 ^ 40 * 1779767 * 2
def baseEnd_1779767 : Nat := 406167077338063727612225

theorem tailTrace_1779767 : CollatzResearch.WordTrace tailWord_1779767 prefixEnd_1779767 406167077338063727612225 := by
  unfold tailWord_1779767
  simp only [CollatzResearch.WordTrace]
  refine ⟨64913435343215593849217555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43275623562143729232811703 64913435343215593849217555)
  ·
    refine ⟨97370153014823390773826333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64913435343215593849217555 97370153014823390773826333)
    ·
      refine ⟨36513807380558771540184875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97370153014823390773826333 36513807380558771540184875)
      ·
        refine ⟨54770711070838157310277313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36513807380558771540184875 54770711070838157310277313)
        ·
          refine ⟨41078033303128617982707985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54770711070838157310277313 41078033303128617982707985)
          ·
            refine ⟨30808524977346463487030989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41078033303128617982707985 30808524977346463487030989)
            ·
              refine ⟨11553196866504923807636621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30808524977346463487030989 11553196866504923807636621)
              ·
                refine ⟨4332448824939346427863733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11553196866504923807636621 4332448824939346427863733)
                ·
                  refine ⟨406167077338063727612225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4332448824939346427863733 406167077338063727612225)
                  ·
                    rfl

theorem cell21_1779767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 3, 5].length) (baseStart_1779767 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1779767 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1779767 prefixEnd_1779767 := by exact prefixLift 1779767
  have htrace : WordTrace (prefixWord ++ tailWord_1779767) baseStart_1779767 baseEnd_1779767 := by
    simpa [prefixWord, tailWord_1779767, baseEnd_1779767] using wordTrace_append hprefix tailTrace_1779767
  have hstable : (prefixWord ++ tailWord_1779767).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779767).length < 2 ^ (prefixWord ++ tailWord_1779767).sum := by decide
  have hdescent : baseEnd_1779767 < baseStart_1779767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779812 : List Nat := [2, 3, 1, 1, 2, 1, 11]
def baseStart_1779812 : Nat := 118140960795 + 1779812 * 2 ^ 59
def prefixEnd_1779812 : Nat := 4983230072969 + 3 ^ 40 * 1779812 * 2
def baseEnd_1779812 : Nat := 45130816327905961040237

theorem tailTrace_1779812 : CollatzResearch.WordTrace tailWord_1779812 prefixEnd_1779812 45130816327905961040237 := by
  unfold tailWord_1779812
  simp only [CollatzResearch.WordTrace]
  refine ⟨32457538314026283267302845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43276717752035044356403793 32457538314026283267302845)
  ·
    refine ⟨12171576867759856225238567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32457538314026283267302845 12171576867759856225238567)
    ·
      refine ⟨18257365301639784337857851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12171576867759856225238567 18257365301639784337857851)
      ·
        refine ⟨27386047952459676506786777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18257365301639784337857851 27386047952459676506786777)
        ·
          refine ⟨20539535964344757380090083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27386047952459676506786777 20539535964344757380090083)
          ·
            refine ⟨30809303946517136070135125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20539535964344757380090083 30809303946517136070135125)
            ·
              refine ⟨45130816327905961040237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 30809303946517136070135125 45130816327905961040237)
              ·
                rfl

theorem cell21_1779812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 11].length) (baseStart_1779812 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1779812 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1779812 prefixEnd_1779812 := by exact prefixLift 1779812
  have htrace : WordTrace (prefixWord ++ tailWord_1779812) baseStart_1779812 baseEnd_1779812 := by
    simpa [prefixWord, tailWord_1779812, baseEnd_1779812] using wordTrace_append hprefix tailTrace_1779812
  have hstable : (prefixWord ++ tailWord_1779812).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779812).length < 2 ^ (prefixWord ++ tailWord_1779812).sum := by decide
  have hdescent : baseEnd_1779812 < baseStart_1779812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779818 : List Nat := [3, 1, 3, 2, 4, 1, 1, 1, 5]
def baseStart_1779818 : Nat := 118140960795 + 1779818 * 2 ^ 59
def prefixEnd_1779818 : Nat := 4983230072969 + 3 ^ 40 * 1779818 * 2
def baseEnd_1779818 : Nat := 406178716232898972262121

theorem tailTrace_1779818 : CollatzResearch.WordTrace tailWord_1779818 prefixEnd_1779818 406178716232898972262121 := by
  unfold tailWord_1779818
  simp only [CollatzResearch.WordTrace]
  refine ⟨16228823866507707389831027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43276863644020553039549405 16228823866507707389831027)
  ·
    refine ⟨24343235799761561084746541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16228823866507707389831027 24343235799761561084746541)
    ·
      refine ⟨9128713424910585406779953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24343235799761561084746541 9128713424910585406779953)
      ·
        refine ⟨6846535068682939055084965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9128713424910585406779953 6846535068682939055084965)
        ·
          refine ⟨1283725325378051072828431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6846535068682939055084965 1283725325378051072828431)
          ·
            refine ⟨1925587988067076609242647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1283725325378051072828431 1925587988067076609242647)
            ·
              refine ⟨2888381982100614913863971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1925587988067076609242647 2888381982100614913863971)
              ·
                refine ⟨4332572973150922370795957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2888381982100614913863971 4332572973150922370795957)
                ·
                  refine ⟨406178716232898972262121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4332572973150922370795957 406178716232898972262121)
                  ·
                    rfl

theorem cell21_1779818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 1, 5].length) (baseStart_1779818 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1779818 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1779818 prefixEnd_1779818 := by exact prefixLift 1779818
  have htrace : WordTrace (prefixWord ++ tailWord_1779818) baseStart_1779818 baseEnd_1779818 := by
    simpa [prefixWord, tailWord_1779818, baseEnd_1779818] using wordTrace_append hprefix tailTrace_1779818
  have hstable : (prefixWord ++ tailWord_1779818).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779818).length < 2 ^ (prefixWord ++ tailWord_1779818).sum := by decide
  have hdescent : baseEnd_1779818 < baseStart_1779818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779925 : List Nat := [1, 3, 2, 4, 3, 1, 1, 2, 4]
def baseStart_1779925 : Nat := 118140960795 + 1779925 * 2 ^ 59
def prefixEnd_1779925 : Nat := 4983230072969 + 3 ^ 40 * 1779925 * 2
def baseEnd_1779925 : Nat := 406203135090690563978569

theorem tailTrace_1779925 : CollatzResearch.WordTrace tailWord_1779925 prefixEnd_1779925 406203135090690563978569 := by
  unfold tailWord_1779925
  simp only [CollatzResearch.WordTrace]
  refine ⟨64919198076643186833469229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43279465384428791222312819 64919198076643186833469229)
  ·
    refine ⟨24344699278741195062550961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64919198076643186833469229 24344699278741195062550961)
    ·
      refine ⟨18258524459055896296913221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24344699278741195062550961 18258524459055896296913221)
      ·
        refine ⟨3423473336072980555671229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18258524459055896296913221 3423473336072980555671229)
        ·
          refine ⟨1283802501027367708376711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3423473336072980555671229 1283802501027367708376711)
          ·
            refine ⟨1925703751541051562565067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1283802501027367708376711 1925703751541051562565067)
            ·
              refine ⟨2888555627311577343847601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1925703751541051562565067 2888555627311577343847601)
              ·
                refine ⟨2166416720483683007885701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2888555627311577343847601 2166416720483683007885701)
                ·
                  refine ⟨406203135090690563978569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2166416720483683007885701 406203135090690563978569)
                  ·
                    rfl

theorem cell21_1779925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 2, 4].length) (baseStart_1779925 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1779925 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1779925 prefixEnd_1779925 := by exact prefixLift 1779925
  have htrace : WordTrace (prefixWord ++ tailWord_1779925) baseStart_1779925 baseEnd_1779925 := by
    simpa [prefixWord, tailWord_1779925, baseEnd_1779925] using wordTrace_append hprefix tailTrace_1779925
  have hstable : (prefixWord ++ tailWord_1779925).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779925).length < 2 ^ (prefixWord ++ tailWord_1779925).sum := by decide
  have hdescent : baseEnd_1779925 < baseStart_1779925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779936 : List Nat := [2, 1, 1, 3, 1, 3, 1, 6, 3]
def baseStart_1779936 : Nat := 118140960795 + 1779936 * 2 ^ 59
def prefixEnd_1779936 : Nat := 4983230072969 + 3 ^ 40 * 1779936 * 2
def baseEnd_1779936 : Nat := 406205645440556989295213

theorem tailTrace_1779936 : CollatzResearch.WordTrace tailWord_1779936 prefixEnd_1779936 406205645440556989295213 := by
  unfold tailWord_1779936
  simp only [CollatzResearch.WordTrace]
  refine ⟨32459799639801667856059831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43279732853068890474746441 32459799639801667856059831)
  ·
    refine ⟨48689699459702501784089747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32459799639801667856059831 48689699459702501784089747)
    ·
      refine ⟨73034549189553752676134621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48689699459702501784089747 73034549189553752676134621)
      ·
        refine ⟨27387955946082657253550483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73034549189553752676134621 27387955946082657253550483)
        ·
          refine ⟨41081933919123985880325725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27387955946082657253550483 41081933919123985880325725)
          ·
            refine ⟨15405725219671494705122147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41081933919123985880325725 15405725219671494705122147)
            ·
              refine ⟨23108587829507242057683221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15405725219671494705122147 23108587829507242057683221)
              ·
                refine ⟨1083215054508151971453901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 23108587829507242057683221 1083215054508151971453901)
                ·
                  refine ⟨406205645440556989295213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1083215054508151971453901 406205645440556989295213)
                  ·
                    rfl

theorem cell21_1779936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 6, 3].length) (baseStart_1779936 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1779936 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1779936 prefixEnd_1779936 := by exact prefixLift 1779936
  have htrace : WordTrace (prefixWord ++ tailWord_1779936) baseStart_1779936 baseEnd_1779936 := by
    simpa [prefixWord, tailWord_1779936, baseEnd_1779936] using wordTrace_append hprefix tailTrace_1779936
  have hstable : (prefixWord ++ tailWord_1779936).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779936).length < 2 ^ (prefixWord ++ tailWord_1779936).sum := by decide
  have hdescent : baseEnd_1779936 < baseStart_1779936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779970 : List Nat := [3, 4, 1, 1, 2, 1, 3, 3, 3]
def baseStart_1779970 : Nat := 118140960795 + 1779970 * 2 ^ 59
def prefixEnd_1779970 : Nat := 4983230072969 + 3 ^ 40 * 1779970 * 2
def baseEnd_1779970 : Nat := 406213404703780485728477

theorem tailTrace_1779970 : CollatzResearch.WordTrace tailWord_1779970 prefixEnd_1779970 406213404703780485728477 := by
  unfold tailWord_1779970
  simp only [CollatzResearch.WordTrace]
  refine ⟨16230209840370039879714341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43280559574320106345904909 16230209840370039879714341)
  ·
    refine ⟨3043164345069382477446439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16230209840370039879714341 3043164345069382477446439)
    ·
      refine ⟨4564746517604073716169659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3043164345069382477446439 4564746517604073716169659)
      ·
        refine ⟨6847119776406110574254489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4564746517604073716169659 6847119776406110574254489)
        ·
          refine ⟨5135339832304582930690867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6847119776406110574254489 5135339832304582930690867)
          ·
            refine ⟨7703009748456874396036301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5135339832304582930690867 7703009748456874396036301)
            ·
              refine ⟨2888628655671327898513613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7703009748456874396036301 2888628655671327898513613)
              ·
                refine ⟨1083235745876747961942605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2888628655671327898513613 1083235745876747961942605)
                ·
                  refine ⟨406213404703780485728477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1083235745876747961942605 406213404703780485728477)
                  ·
                    rfl

theorem cell21_1779970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_1779970 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1779970 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1779970 prefixEnd_1779970 := by exact prefixLift 1779970
  have htrace : WordTrace (prefixWord ++ tailWord_1779970) baseStart_1779970 baseEnd_1779970 := by
    simpa [prefixWord, tailWord_1779970, baseEnd_1779970] using wordTrace_append hprefix tailTrace_1779970
  have hstable : (prefixWord ++ tailWord_1779970).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779970).length < 2 ^ (prefixWord ++ tailWord_1779970).sum := by decide
  have hdescent : baseEnd_1779970 < baseStart_1779970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779995 : List Nat := [1, 1, 1, 1, 1, 1, 9, 1, 5]
def baseStart_1779995 : Nat := 118140960795 + 1779995 * 2 ^ 59
def prefixEnd_1779995 : Nat := 4983230072969 + 3 ^ 40 * 1779995 * 2
def baseEnd_1779995 : Nat := 406219110044385997811759

theorem tailTrace_1779995 : CollatzResearch.WordTrace tailWord_1779995 prefixEnd_1779995 406219110044385997811759 := by
  unfold tailWord_1779995
  simp only [CollatzResearch.WordTrace]
  refine ⟨64921751186389588788517439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43281167457593059192344959 64921751186389588788517439)
  ·
    refine ⟨97382626779584383182776159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64921751186389588788517439 97382626779584383182776159)
    ·
      refine ⟨146073940169376574774164239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97382626779584383182776159 146073940169376574774164239)
      ·
        refine ⟨219110910254064862161246359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146073940169376574774164239 219110910254064862161246359)
        ·
          refine ⟨328666365381097293241869539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219110910254064862161246359 328666365381097293241869539)
          ·
            refine ⟨492999548071645939862804309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 328666365381097293241869539 492999548071645939862804309)
            ·
              refine ⟨2888669226982300428883619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 492999548071645939862804309 2888669226982300428883619)
              ·
                refine ⟨4333003840473450643325429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2888669226982300428883619 4333003840473450643325429)
                ·
                  refine ⟨406219110044385997811759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4333003840473450643325429 406219110044385997811759)
                  ·
                    rfl

theorem cell21_1779995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 1, 5].length) (baseStart_1779995 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1779995 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1779995 prefixEnd_1779995 := by exact prefixLift 1779995
  have htrace : WordTrace (prefixWord ++ tailWord_1779995) baseStart_1779995 baseEnd_1779995 := by
    simpa [prefixWord, tailWord_1779995, baseEnd_1779995] using wordTrace_append hprefix tailTrace_1779995
  have hstable : (prefixWord ++ tailWord_1779995).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779995).length < 2 ^ (prefixWord ++ tailWord_1779995).sum := by decide
  have hdescent : baseEnd_1779995 < baseStart_1779995 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779998 : List Nat := [4, 3, 2, 1, 1, 1, 1, 8]
def baseStart_1779998 : Nat := 118140960795 + 1779998 * 2 ^ 59
def prefixEnd_1779998 : Nat := 4983230072969 + 3 ^ 40 * 1779998 * 2
def baseEnd_1779998 : Nat := 135406598228419553087251

theorem tailTrace_1779998 : CollatzResearch.WordTrace tailWord_1779998 prefixEnd_1779998 135406598228419553087251 := by
  unfold tailWord_1779998
  simp only [CollatzResearch.WordTrace]
  refine ⟨8115232575672340037609581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43281240403585813533917765 8115232575672340037609581)
  ·
    refine ⟨3043212215877127514103593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8115232575672340037609581 3043212215877127514103593)
    ·
      refine ⟨2282409161907845635577695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3043212215877127514103593 2282409161907845635577695)
      ·
        refine ⟨3423613742861768453366543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2282409161907845635577695 3423613742861768453366543)
        ·
          refine ⟨5135420614292652680049815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3423613742861768453366543 5135420614292652680049815)
          ·
            refine ⟨7703130921438979020074723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5135420614292652680049815 7703130921438979020074723)
            ·
              refine ⟨11554696382158468530112085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7703130921438979020074723 11554696382158468530112085)
              ·
                refine ⟨135406598228419553087251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11554696382158468530112085 135406598228419553087251)
                ·
                  rfl

theorem cell21_1779998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 8].length) (baseStart_1779998 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1779998 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1779998 prefixEnd_1779998 := by exact prefixLift 1779998
  have htrace : WordTrace (prefixWord ++ tailWord_1779998) baseStart_1779998 baseEnd_1779998 := by
    simpa [prefixWord, tailWord_1779998, baseEnd_1779998] using wordTrace_append hprefix tailTrace_1779998
  have hstable : (prefixWord ++ tailWord_1779998).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779998).length < 2 ^ (prefixWord ++ tailWord_1779998).sum := by decide
  have hdescent : baseEnd_1779998 < baseStart_1779998 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780071 : List Nat := [1, 1, 5, 1, 3, 1, 1, 1, 7]
def baseStart_1780071 : Nat := 118140960795 + 1780071 * 2 ^ 59
def prefixEnd_1780071 : Nat := 4983230072969 + 3 ^ 40 * 1780071 * 2
def baseEnd_1780071 : Nat := 406236454279826754544937

theorem tailTrace_1780071 : CollatzResearch.WordTrace tailWord_1780071 prefixEnd_1780071 406236454279826754544937 := by
  unfold tailWord_1780071
  simp only [CollatzResearch.WordTrace]
  refine ⟨64924523134114253768284067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43283015422742835845522711 64924523134114253768284067)
  ·
    refine ⟨97386784701171380652426101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64924523134114253768284067 97386784701171380652426101)
    ·
      refine ⟨9130011065734816936164947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 97386784701171380652426101 9130011065734816936164947)
      ·
        refine ⟨13695016598602225404247421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9130011065734816936164947 13695016598602225404247421)
        ·
          refine ⟨5135631224475834526592783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13695016598602225404247421 5135631224475834526592783)
          ·
            refine ⟨7703446836713751789889175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5135631224475834526592783 7703446836713751789889175)
            ·
              refine ⟨11555170255070627684833763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7703446836713751789889175 11555170255070627684833763)
              ·
                refine ⟨17332755382605941527250645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11555170255070627684833763 17332755382605941527250645)
                ·
                  refine ⟨406236454279826754544937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17332755382605941527250645 406236454279826754544937)
                  ·
                    rfl

theorem cell21_1780071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 7].length) (baseStart_1780071 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1780071 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1780071 prefixEnd_1780071 := by exact prefixLift 1780071
  have htrace : WordTrace (prefixWord ++ tailWord_1780071) baseStart_1780071 baseEnd_1780071 := by
    simpa [prefixWord, tailWord_1780071, baseEnd_1780071] using wordTrace_append hprefix tailTrace_1780071
  have hstable : (prefixWord ++ tailWord_1780071).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780071).length < 2 ^ (prefixWord ++ tailWord_1780071).sum := by decide
  have hdescent : baseEnd_1780071 < baseStart_1780071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
