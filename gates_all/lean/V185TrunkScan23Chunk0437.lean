import V185TrunkScan23Chunk0436

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2583719 : List Nat := [1, 1, 6, 2, 1, 1, 3, 3, 1, 4]
def baseStart_2583719 : Nat := 118140960795 + 2583719 * 2 ^ 59
def prefixEnd_2583719 : Nat := 4983230072969 + 3 ^ 40 * 2583719 * 2
def baseEnd_2583719 : Nat := 442229907718027307076733

theorem tailTrace_2583719 : CollatzResearch.WordTrace tailWord_2583719 prefixEnd_2583719 442229907718027307076733 := by
  unfold tailWord_2583719
  simp only [CollatzResearch.WordTrace]
  refine ⟨94235973726634801919482211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62823982484423201279654807 94235973726634801919482211)
  ·
    refine ⟨141353960589952202879223317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94235973726634801919482211 141353960589952202879223317)
    ·
      refine ⟨6625966902654009509963593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 141353960589952202879223317 6625966902654009509963593)
      ·
        refine ⟨4969475176990507132472695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6625966902654009509963593 4969475176990507132472695)
        ·
          refine ⟨7454212765485760698709043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4969475176990507132472695 7454212765485760698709043)
          ·
            refine ⟨11181319148228641048063565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7454212765485760698709043 11181319148228641048063565)
            ·
              refine ⟨4192994680585740393023837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11181319148228641048063565 4192994680585740393023837)
              ·
                refine ⟨1572373005219652647383939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4192994680585740393023837 1572373005219652647383939)
                ·
                  refine ⟨2358559507829478971075909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1572373005219652647383939 2358559507829478971075909)
                  ·
                    refine ⟨442229907718027307076733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2358559507829478971075909 442229907718027307076733)
                    ·
                      rfl

theorem cell23_2583719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 3, 1, 4].length) (baseStart_2583719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2583719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2583719 prefixEnd_2583719 := by exact prefixLift 2583719
  have htrace : WordTrace (prefixWord ++ tailWord_2583719) baseStart_2583719 baseEnd_2583719 := by
    simpa [prefixWord, tailWord_2583719, baseEnd_2583719] using wordTrace_append hprefix tailTrace_2583719
  have hstable : (prefixWord ++ tailWord_2583719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2583719).length < 2 ^ (prefixWord ++ tailWord_2583719).sum := by decide
  have hdescent : baseEnd_2583719 < baseStart_2583719 := by decide
  rcases family_descends (prefixWord ++ tailWord_2583719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2583721 : List Nat := [1, 2, 1, 1, 1, 1, 2, 1, 3, 3, 7]
def baseStart_2583721 : Nat := 118140960795 + 2583721 * 2 ^ 59
def prefixEnd_2583721 : Nat := 4983230072969 + 3 ^ 40 * 2583721 * 2
def baseEnd_2583721 : Nat := 1326690750115390913405189

theorem tailTrace_2583721 : CollatzResearch.WordTrace tailWord_2583721 prefixEnd_2583721 1326690750115390913405189 := by
  unfold tailWord_2583721
  simp only [CollatzResearch.WordTrace]
  refine ⟨94236046672627556261055017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62824031115085037507370011 94236046672627556261055017)
  ·
    refine ⟨70677035004470667195791263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94236046672627556261055017 70677035004470667195791263)
    ·
      refine ⟨106015552506706000793686895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70677035004470667195791263 106015552506706000793686895)
      ·
        refine ⟨159023328760059001190530343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106015552506706000793686895 159023328760059001190530343)
        ·
          refine ⟨238534993140088501785795515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159023328760059001190530343 238534993140088501785795515)
          ·
            refine ⟨357802489710132752678693273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 238534993140088501785795515 357802489710132752678693273)
            ·
              refine ⟨268351867282599564509019955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 357802489710132752678693273 268351867282599564509019955)
              ·
                refine ⟨402527800923899346763529933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 268351867282599564509019955 402527800923899346763529933)
                ·
                  refine ⟨150947925346462255036323725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 402527800923899346763529933 150947925346462255036323725)
                  ·
                    refine ⟨56605472004923345638621397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 150947925346462255036323725 56605472004923345638621397)
                    ·
                      refine ⟨1326690750115390913405189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 56605472004923345638621397 1326690750115390913405189)
                      ·
                        rfl

theorem cell23_2583721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 3, 7].length) (baseStart_2583721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2583721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2583721 prefixEnd_2583721 := by exact prefixLift 2583721
  have htrace : WordTrace (prefixWord ++ tailWord_2583721) baseStart_2583721 baseEnd_2583721 := by
    simpa [prefixWord, tailWord_2583721, baseEnd_2583721] using wordTrace_append hprefix tailTrace_2583721
  have hstable : (prefixWord ++ tailWord_2583721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2583721).length < 2 ^ (prefixWord ++ tailWord_2583721).sum := by decide
  have hdescent : baseEnd_2583721 < baseStart_2583721 := by decide
  rcases family_descends (prefixWord ++ tailWord_2583721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2583799 : List Nat := [1, 1, 3, 1, 1, 1, 2, 8, 1, 2, 2]
def baseStart_2583799 : Nat := 118140960795 + 2583799 * 2 ^ 59
def prefixEnd_2583799 : Nat := 4983230072969 + 3 ^ 40 * 2583799 * 2
def baseEnd_2583799 : Nat := 1326730801606441608229831

theorem tailTrace_2583799 : CollatzResearch.WordTrace tailWord_2583799 prefixEnd_2583799 1326730801606441608229831 := by
  unfold tailWord_2583799
  simp only [CollatzResearch.WordTrace]
  refine ⟨94238891566344975582394451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62825927710896650388262967 94238891566344975582394451)
  ·
    refine ⟨141358337349517463373591677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94238891566344975582394451 141358337349517463373591677)
    ·
      refine ⟨53009376506069048765096879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141358337349517463373591677 53009376506069048765096879)
      ·
        refine ⟨79514064759103573147645319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53009376506069048765096879 79514064759103573147645319)
        ·
          refine ⟨119271097138655359721467979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79514064759103573147645319 119271097138655359721467979)
          ·
            refine ⟨178906645707983039582201969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119271097138655359721467979 178906645707983039582201969)
            ·
              refine ⟨134179984280987279686651477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 178906645707983039582201969 134179984280987279686651477)
              ·
                refine ⟨1572421690792819683827947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 134179984280987279686651477 1572421690792819683827947)
                ·
                  refine ⟨2358632536189229525741921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1572421690792819683827947 2358632536189229525741921)
                  ·
                    refine ⟨1768974402141922144306441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2358632536189229525741921 1768974402141922144306441)
                    ·
                      refine ⟨1326730801606441608229831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1768974402141922144306441 1326730801606441608229831)
                      ·
                        rfl

theorem cell23_2583799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 8, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 8, 1, 2, 2].length) (baseStart_2583799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2583799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2583799 prefixEnd_2583799 := by exact prefixLift 2583799
  have htrace : WordTrace (prefixWord ++ tailWord_2583799) baseStart_2583799 baseEnd_2583799 := by
    simpa [prefixWord, tailWord_2583799, baseEnd_2583799] using wordTrace_append hprefix tailTrace_2583799
  have hstable : (prefixWord ++ tailWord_2583799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2583799).length < 2 ^ (prefixWord ++ tailWord_2583799).sum := by decide
  have hdescent : baseEnd_2583799 < baseStart_2583799 := by decide
  rcases family_descends (prefixWord ++ tailWord_2583799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2583812 : List Nat := [2, 3, 2, 2, 2, 2, 2, 1, 1, 2, 4]
def baseStart_2583812 : Nat := 118140960795 + 2583812 * 2 ^ 59
def prefixEnd_2583812 : Nat := 4983230072969 + 3 ^ 40 * 2583812 * 2
def baseEnd_2583812 : Nat := 1326737476854950057367271

theorem tailTrace_2583812 : CollatzResearch.WordTrace tailWord_2583812 prefixEnd_2583812 1326737476854950057367271 := by
  unfold tailWord_2583812
  simp only [CollatzResearch.WordTrace]
  refine ⟨47119682857648939401308845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62826243810198585868411793 47119682857648939401308845)
  ·
    refine ⟨17669881071618352275490817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47119682857648939401308845 17669881071618352275490817)
    ·
      refine ⟨13252410803713764206618113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17669881071618352275490817 13252410803713764206618113)
      ·
        refine ⟨9939308102785323154963585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13252410803713764206618113 9939308102785323154963585)
        ·
          refine ⟨7454481077088992366222689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9939308102785323154963585 7454481077088992366222689)
          ·
            refine ⟨5590860807816744274667017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7454481077088992366222689 5590860807816744274667017)
            ·
              refine ⟨4193145605862558206000263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5590860807816744274667017 4193145605862558206000263)
              ·
                refine ⟨6289718408793837309000395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4193145605862558206000263 6289718408793837309000395)
                ·
                  refine ⟨9434577613190755963500593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6289718408793837309000395 9434577613190755963500593)
                  ·
                    refine ⟨7075933209893066972625445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9434577613190755963500593 7075933209893066972625445)
                    ·
                      refine ⟨1326737476854950057367271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7075933209893066972625445 1326737476854950057367271)
                      ·
                        rfl

theorem cell23_2583812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_2583812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2583812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2583812 prefixEnd_2583812 := by exact prefixLift 2583812
  have htrace : WordTrace (prefixWord ++ tailWord_2583812) baseStart_2583812 baseEnd_2583812 := by
    simpa [prefixWord, tailWord_2583812, baseEnd_2583812] using wordTrace_append hprefix tailTrace_2583812
  have hstable : (prefixWord ++ tailWord_2583812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2583812).length < 2 ^ (prefixWord ++ tailWord_2583812).sum := by decide
  have hdescent : baseEnd_2583812 < baseStart_2583812 := by decide
  rcases family_descends (prefixWord ++ tailWord_2583812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2583818 : List Nat := [3, 1, 2, 2, 1, 1, 1, 1, 4, 7]
def baseStart_2583818 : Nat := 118140960795 + 2583818 * 2 ^ 59
def prefixEnd_2583818 : Nat := 4983230072969 + 3 ^ 40 * 2583818 * 2
def baseEnd_2583818 : Nat := 442246852579625677964081

theorem tailTrace_2583818 : CollatzResearch.WordTrace tailWord_2583818 prefixEnd_2583818 442246852579625677964081 := by
  unfold tailWord_2583818
  simp only [CollatzResearch.WordTrace]
  refine ⟨23559896138319035456834027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62826389702184094551557405 23559896138319035456834027)
  ·
    refine ⟨35339844207478553185251041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23559896138319035456834027 35339844207478553185251041)
    ·
      refine ⟨26504883155608914888938281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35339844207478553185251041 26504883155608914888938281)
      ·
        refine ⟨19878662366706686166703711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26504883155608914888938281 19878662366706686166703711)
        ·
          refine ⟨29817993550060029250055567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19878662366706686166703711 29817993550060029250055567)
          ·
            refine ⟨44726990325090043875083351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29817993550060029250055567 44726990325090043875083351)
            ·
              refine ⟨67090485487635065812625027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44726990325090043875083351 67090485487635065812625027)
              ·
                refine ⟨100635728231452598718937541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67090485487635065812625027 100635728231452598718937541)
                ·
                  refine ⟨18869199043397362259800789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 100635728231452598718937541 18869199043397362259800789)
                  ·
                    refine ⟨442246852579625677964081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18869199043397362259800789 442246852579625677964081)
                    ·
                      rfl

theorem cell23_2583818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 4, 7].length) (baseStart_2583818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2583818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2583818 prefixEnd_2583818 := by exact prefixLift 2583818
  have htrace : WordTrace (prefixWord ++ tailWord_2583818) baseStart_2583818 baseEnd_2583818 := by
    simpa [prefixWord, tailWord_2583818, baseEnd_2583818] using wordTrace_append hprefix tailTrace_2583818
  have hstable : (prefixWord ++ tailWord_2583818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2583818).length < 2 ^ (prefixWord ++ tailWord_2583818).sum := by decide
  have hdescent : baseEnd_2583818 < baseStart_2583818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2583818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2583876 : List Nat := [2, 3, 4, 1, 1, 1, 1, 4, 1, 3, 2]
def baseStart_2583876 : Nat := 118140960795 + 2583876 * 2 ^ 59
def prefixEnd_2583876 : Nat := 4983230072969 + 3 ^ 40 * 2583876 * 2
def baseEnd_2583876 : Nat := 1326770339616837806966977

theorem tailTrace_2583876 : CollatzResearch.WordTrace tailWord_2583876 prefixEnd_2583876 1326770339616837806966977 := by
  unfold tailWord_2583876
  simp only [CollatzResearch.WordTrace]
  refine ⟨47120849993533008866473741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62827799991377345155298321 47120849993533008866473741)
  ·
    refine ⟨17670318747574878324927653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47120849993533008866473741 17670318747574878324927653)
    ·
      refine ⟨3313184765170289685923935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17670318747574878324927653 3313184765170289685923935)
      ·
        refine ⟨4969777147755434528885903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3313184765170289685923935 4969777147755434528885903)
        ·
          refine ⟨7454665721633151793328855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4969777147755434528885903 7454665721633151793328855)
          ·
            refine ⟨11181998582449727689993283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7454665721633151793328855 11181998582449727689993283)
            ·
              refine ⟨16772997873674591534989925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11181998582449727689993283 16772997873674591534989925)
              ·
                refine ⟨3144937101313985912810611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16772997873674591534989925 3144937101313985912810611)
                ·
                  refine ⟨4717405651970978869215917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3144937101313985912810611 4717405651970978869215917)
                  ·
                    refine ⟨1769027119489117075955969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4717405651970978869215917 1769027119489117075955969)
                    ·
                      refine ⟨1326770339616837806966977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1769027119489117075955969 1326770339616837806966977)
                      ·
                        rfl

theorem cell23_2583876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_2583876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2583876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2583876 prefixEnd_2583876 := by exact prefixLift 2583876
  have htrace : WordTrace (prefixWord ++ tailWord_2583876) baseStart_2583876 baseEnd_2583876 := by
    simpa [prefixWord, tailWord_2583876, baseEnd_2583876] using wordTrace_append hprefix tailTrace_2583876
  have hstable : (prefixWord ++ tailWord_2583876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2583876).length < 2 ^ (prefixWord ++ tailWord_2583876).sum := by decide
  have hdescent : baseEnd_2583876 < baseStart_2583876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2583876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2583905 : List Nat := [1, 2, 3, 1, 1, 1, 1, 3, 4, 3, 3]
def baseStart_2583905 : Nat := 118140960795 + 2583905 * 2 ^ 59
def prefixEnd_2583905 : Nat := 4983230072969 + 3 ^ 40 * 2583905 * 2
def baseEnd_2583905 : Nat := 1326785230555818193504343

theorem tailTrace_2583905 : CollatzResearch.WordTrace tailWord_2583905 prefixEnd_2583905 1326785230555818193504343 := by
  unfold tailWord_2583905
  simp only [CollatzResearch.WordTrace]
  refine ⟨94242757703960955685753169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62828505135973970457168779 94242757703960955685753169)
  ·
    refine ⟨70682068277970716764314877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94242757703960955685753169 70682068277970716764314877)
    ·
      refine ⟨26505775604239018786618079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70682068277970716764314877 26505775604239018786618079)
      ·
        refine ⟨39758663406358528179927119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26505775604239018786618079 39758663406358528179927119)
        ·
          refine ⟨59637995109537792269890679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39758663406358528179927119 59637995109537792269890679)
          ·
            refine ⟨89456992664306688404836019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59637995109537792269890679 89456992664306688404836019)
            ·
              refine ⟨134185488996460032607254029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89456992664306688404836019 134185488996460032607254029)
              ·
                refine ⟨50319558373672512227720261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 134185488996460032607254029 50319558373672512227720261)
                ·
                  refine ⟨9434917195063596042697549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50319558373672512227720261 9434917195063596042697549)
                  ·
                    refine ⟨3538093948148848516011581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9434917195063596042697549 3538093948148848516011581)
                    ·
                      refine ⟨1326785230555818193504343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3538093948148848516011581 1326785230555818193504343)
                      ·
                        rfl

theorem cell23_2583905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 4, 3, 3].length) (baseStart_2583905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2583905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2583905 prefixEnd_2583905 := by exact prefixLift 2583905
  have htrace : WordTrace (prefixWord ++ tailWord_2583905) baseStart_2583905 baseEnd_2583905 := by
    simpa [prefixWord, tailWord_2583905, baseEnd_2583905] using wordTrace_append hprefix tailTrace_2583905
  have hstable : (prefixWord ++ tailWord_2583905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2583905).length < 2 ^ (prefixWord ++ tailWord_2583905).sum := by decide
  have hdescent : baseEnd_2583905 < baseStart_2583905 := by decide
  rcases family_descends (prefixWord ++ tailWord_2583905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2583906 : List Nat := [3, 3, 2, 1, 1, 1, 2, 4, 2, 2, 2]
def baseStart_2583906 : Nat := 118140960795 + 2583906 * 2 ^ 59
def prefixEnd_2583906 : Nat := 4983230072969 + 3 ^ 40 * 2583906 * 2
def baseEnd_2583906 : Nat := 1326785744036472689591839

theorem tailTrace_2583906 : CollatzResearch.WordTrace tailWord_2583906 prefixEnd_2583906 1326785744036472689591839 := by
  unfold tailWord_2583906
  simp only [CollatzResearch.WordTrace]
  refine ⟨23560698544239333214134893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62828529451304888571026381 23560698544239333214134893)
  ·
    refine ⟨8835261954089749955300585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23560698544239333214134893 8835261954089749955300585)
    ·
      refine ⟨6626446465567312466475439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8835261954089749955300585 6626446465567312466475439)
      ·
        refine ⟨9939669698350968699713159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6626446465567312466475439 9939669698350968699713159)
        ·
          refine ⟨14909504547526453049569739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9939669698350968699713159 14909504547526453049569739)
          ·
            refine ⟨22364256821289679574354609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14909504547526453049569739 22364256821289679574354609)
            ·
              refine ⟨16773192615967259680765957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22364256821289679574354609 16773192615967259680765957)
              ·
                refine ⟨3144973615493861190143617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16773192615967259680765957 3144973615493861190143617)
                ·
                  refine ⟨2358730211620395892607713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3144973615493861190143617 2358730211620395892607713)
                  ·
                    refine ⟨1769047658715296919455785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2358730211620395892607713 1769047658715296919455785)
                    ·
                      refine ⟨1326785744036472689591839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1769047658715296919455785 1326785744036472689591839)
                      ·
                        rfl

theorem cell23_2583906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 4, 2, 2, 2].length) (baseStart_2583906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2583906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2583906 prefixEnd_2583906 := by exact prefixLift 2583906
  have htrace : WordTrace (prefixWord ++ tailWord_2583906) baseStart_2583906 baseEnd_2583906 := by
    simpa [prefixWord, tailWord_2583906, baseEnd_2583906] using wordTrace_append hprefix tailTrace_2583906
  have hstable : (prefixWord ++ tailWord_2583906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2583906).length < 2 ^ (prefixWord ++ tailWord_2583906).sum := by decide
  have hdescent : baseEnd_2583906 < baseStart_2583906 := by decide
  rcases family_descends (prefixWord ++ tailWord_2583906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2583962 : List Nat := [3, 1, 1, 4, 1, 1, 1, 4, 2, 1, 4]
def baseStart_2583962 : Nat := 118140960795 + 2583962 * 2 ^ 59
def prefixEnd_2583962 : Nat := 4983230072969 + 3 ^ 40 * 2583962 * 2
def baseEnd_2583962 : Nat := 1326814498953124470491581

theorem tailTrace_2583962 : CollatzResearch.WordTrace tailWord_2583962 prefixEnd_2583962 1326814498953124470491581 := by
  unfold tailWord_2583962
  simp only [CollatzResearch.WordTrace]
  refine ⟨23561209166188613605144535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62829891109836302947052093 23561209166188613605144535)
  ·
    refine ⟨35341813749282920407716803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23561209166188613605144535 35341813749282920407716803)
    ·
      refine ⟨53012720623924380611575205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35341813749282920407716803 53012720623924380611575205)
      ·
        refine ⟨9939885116985821364670351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53012720623924380611575205 9939885116985821364670351)
        ·
          refine ⟨14909827675478732047005527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9939885116985821364670351 14909827675478732047005527)
          ·
            refine ⟨22364741513218098070508291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14909827675478732047005527 22364741513218098070508291)
            ·
              refine ⟨33547112269827147105762437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22364741513218098070508291 33547112269827147105762437)
              ·
                refine ⟨6290083550592590082330457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33547112269827147105762437 6290083550592590082330457)
                ·
                  refine ⟨4717562662944442561747843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6290083550592590082330457 4717562662944442561747843)
                  ·
                    refine ⟨7076343994416663842621765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4717562662944442561747843 7076343994416663842621765)
                    ·
                      refine ⟨1326814498953124470491581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7076343994416663842621765 1326814498953124470491581)
                      ·
                        rfl

theorem cell23_2583962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_2583962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2583962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2583962 prefixEnd_2583962 := by exact prefixLift 2583962
  have htrace : WordTrace (prefixWord ++ tailWord_2583962) baseStart_2583962 baseEnd_2583962 := by
    simpa [prefixWord, tailWord_2583962, baseEnd_2583962] using wordTrace_append hprefix tailTrace_2583962
  have hstable : (prefixWord ++ tailWord_2583962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2583962).length < 2 ^ (prefixWord ++ tailWord_2583962).sum := by decide
  have hdescent : baseEnd_2583962 < baseStart_2583962 := by decide
  rcases family_descends (prefixWord ++ tailWord_2583962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2583972 : List Nat := [2, 3, 1, 2, 1, 1, 1, 5, 3, 4]
def baseStart_2583972 : Nat := 118140960795 + 2583972 * 2 ^ 59
def prefixEnd_2583972 : Nat := 4983230072969 + 3 ^ 40 * 2583972 * 2
def baseEnd_2583972 : Nat := 442273211253223143788845

theorem tailTrace_2583972 : CollatzResearch.WordTrace tailWord_2583972 prefixEnd_2583972 442273211253223143788845 := by
  unfold tailWord_2583972
  simp only [CollatzResearch.WordTrace]
  refine ⟨47122600697359113064221085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62830134263145484085628113 47122600697359113064221085)
  ·
    refine ⟨17670975261509667399082907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47122600697359113064221085 17670975261509667399082907)
    ·
      refine ⟨26506462892264501098624361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17670975261509667399082907 26506462892264501098624361)
      ·
        refine ⟨19879847169198375823968271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26506462892264501098624361 19879847169198375823968271)
        ·
          refine ⟨29819770753797563735952407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19879847169198375823968271 29819770753797563735952407)
          ·
            refine ⟨44729656130696345603928611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29819770753797563735952407 44729656130696345603928611)
            ·
              refine ⟨67094484196044518405892917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44729656130696345603928611 67094484196044518405892917)
              ·
                refine ⟨6290107893379173600552461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 67094484196044518405892917 6290107893379173600552461)
                ·
                  refine ⟨2358790460017190100207173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6290107893379173600552461 2358790460017190100207173)
                  ·
                    refine ⟨442273211253223143788845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2358790460017190100207173 442273211253223143788845)
                    ·
                      rfl

theorem cell23_2583972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 5, 3, 4].length) (baseStart_2583972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2583972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2583972 prefixEnd_2583972 := by exact prefixLift 2583972
  have htrace : WordTrace (prefixWord ++ tailWord_2583972) baseStart_2583972 baseEnd_2583972 := by
    simpa [prefixWord, tailWord_2583972, baseEnd_2583972] using wordTrace_append hprefix tailTrace_2583972
  have hstable : (prefixWord ++ tailWord_2583972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2583972).length < 2 ^ (prefixWord ++ tailWord_2583972).sum := by decide
  have hdescent : baseEnd_2583972 < baseStart_2583972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2583972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2583989 : List Nat := [1, 3, 3, 2, 2, 2, 1, 2, 3, 4]
def baseStart_2583989 : Nat := 118140960795 + 2583989 * 2 ^ 59
def prefixEnd_2583989 : Nat := 4983230072969 + 3 ^ 40 * 2583989 * 2
def baseEnd_2583989 : Nat := 442276120976931954951319

theorem tailTrace_2583989 : CollatzResearch.WordTrace tailWord_2583989 prefixEnd_2583989 442276120976931954951319 := by
  unfold tailWord_2583989
  simp only [CollatzResearch.WordTrace]
  refine ⟨94245821435656638031811021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62830547623771092021207347 94245821435656638031811021)
  ·
    refine ⟨35342183038371239261929133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94245821435656638031811021 35342183038371239261929133)
    ·
      refine ⟨13253318639389214723223425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35342183038371239261929133 13253318639389214723223425)
      ·
        refine ⟨9939988979541911042417569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13253318639389214723223425 9939988979541911042417569)
        ·
          refine ⟨7454991734656433281813177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9939988979541911042417569 7454991734656433281813177)
          ·
            refine ⟨5591243800992324961359883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7454991734656433281813177 5591243800992324961359883)
            ·
              refine ⟨8386865701488487442039825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5591243800992324961359883 8386865701488487442039825)
              ·
                refine ⟨6290149276116365581529869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8386865701488487442039825 6290149276116365581529869)
                ·
                  refine ⟨2358805978543637093073701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6290149276116365581529869 2358805978543637093073701)
                  ·
                    refine ⟨442276120976931954951319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2358805978543637093073701 442276120976931954951319)
                    ·
                      rfl

theorem cell23_2583989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 2, 3, 4].length) (baseStart_2583989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2583989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2583989 prefixEnd_2583989 := by exact prefixLift 2583989
  have htrace : WordTrace (prefixWord ++ tailWord_2583989) baseStart_2583989 baseEnd_2583989 := by
    simpa [prefixWord, tailWord_2583989, baseEnd_2583989] using wordTrace_append hprefix tailTrace_2583989
  have hstable : (prefixWord ++ tailWord_2583989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2583989).length < 2 ^ (prefixWord ++ tailWord_2583989).sum := by decide
  have hdescent : baseEnd_2583989 < baseStart_2583989 := by decide
  rcases family_descends (prefixWord ++ tailWord_2583989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2583996 : List Nat := [2, 2, 2, 4, 2, 2, 1, 1, 2, 1, 4]
def baseStart_2583996 : Nat := 118140960795 + 2583996 * 2 ^ 59
def prefixEnd_2583996 : Nat := 4983230072969 + 3 ^ 40 * 2583996 * 2
def baseEnd_2583996 : Nat := 1326831957295377337466425

theorem tailTrace_2583996 : CollatzResearch.WordTrace tailWord_2583996 prefixEnd_2583996 1326831957295377337466425 := by
  unfold tailWord_2583996
  simp only [CollatzResearch.WordTrace]
  refine ⟨47123038373315639113657921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62830717831087518818210561 47123038373315639113657921)
  ·
    refine ⟨35342278779986729335243441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47123038373315639113657921 35342278779986729335243441)
    ·
      refine ⟨26506709084990047001432581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35342278779986729335243441 26506709084990047001432581)
      ·
        refine ⟨4970007953435633812768609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26506709084990047001432581 4970007953435633812768609)
        ·
          refine ⟨3727505965076725359576457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4970007953435633812768609 3727505965076725359576457)
          ·
            refine ⟨2795629473807544019682343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3727505965076725359576457 2795629473807544019682343)
            ·
              refine ⟨4193444210711316029523515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2795629473807544019682343 4193444210711316029523515)
              ·
                refine ⟨6290166316066974044285273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4193444210711316029523515 6290166316066974044285273)
                ·
                  refine ⟨4717624737050230533213955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6290166316066974044285273 4717624737050230533213955)
                  ·
                    refine ⟨7076437105575345799820933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4717624737050230533213955 7076437105575345799820933)
                    ·
                      refine ⟨1326831957295377337466425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7076437105575345799820933 1326831957295377337466425)
                      ·
                        rfl

theorem cell23_2583996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_2583996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2583996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2583996 prefixEnd_2583996 := by exact prefixLift 2583996
  have htrace : WordTrace (prefixWord ++ tailWord_2583996) baseStart_2583996 baseEnd_2583996 := by
    simpa [prefixWord, tailWord_2583996, baseEnd_2583996] using wordTrace_append hprefix tailTrace_2583996
  have hstable : (prefixWord ++ tailWord_2583996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2583996).length < 2 ^ (prefixWord ++ tailWord_2583996).sum := by decide
  have hdescent : baseEnd_2583996 < baseStart_2583996 := by decide
  rcases family_descends (prefixWord ++ tailWord_2583996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584039 : List Nat := [1, 1, 5, 2, 1, 2, 1, 2, 1, 5, 2]
def baseStart_2584039 : Nat := 118140960795 + 2584039 * 2 ^ 59
def prefixEnd_2584039 : Nat := 4983230072969 + 3 ^ 40 * 2584039 * 2
def baseEnd_2584039 : Nat := 1326854036963520669228727

theorem tailTrace_2584039 : CollatzResearch.WordTrace tailWord_2584039 prefixEnd_2584039 1326854036963520669228727 := by
  unfold tailWord_2584039
  simp only [CollatzResearch.WordTrace]
  refine ⟨94247645085475496571131171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62831763390316997714087447 94247645085475496571131171)
  ·
    refine ⟨141371467628213244856696757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94247645085475496571131171 141371467628213244856696757)
    ·
      refine ⟨13253575090144991705315321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 141371467628213244856696757 13253575090144991705315321)
      ·
        refine ⟨9940181317608743778986491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13253575090144991705315321 9940181317608743778986491)
        ·
          refine ⟨14910271976413115668479737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9940181317608743778986491 14910271976413115668479737)
          ·
            refine ⟨11182703982309836751359803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14910271976413115668479737 11182703982309836751359803)
            ·
              refine ⟨16774055973464755127039705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11182703982309836751359803 16774055973464755127039705)
              ·
                refine ⟨12580541980098566345279779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16774055973464755127039705 12580541980098566345279779)
                ·
                  refine ⟨18870812970147849517919669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12580541980098566345279779 18870812970147849517919669)
                  ·
                    refine ⟨1769138715951360892304969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18870812970147849517919669 1769138715951360892304969)
                    ·
                      refine ⟨1326854036963520669228727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1769138715951360892304969 1326854036963520669228727)
                      ·
                        rfl

theorem cell23_2584039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 2, 1, 5, 2].length) (baseStart_2584039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2584039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2584039 prefixEnd_2584039 := by exact prefixLift 2584039
  have htrace : WordTrace (prefixWord ++ tailWord_2584039) baseStart_2584039 baseEnd_2584039 := by
    simpa [prefixWord, tailWord_2584039, baseEnd_2584039] using wordTrace_append hprefix tailTrace_2584039
  have hstable : (prefixWord ++ tailWord_2584039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584039).length < 2 ^ (prefixWord ++ tailWord_2584039).sum := by decide
  have hdescent : baseEnd_2584039 < baseStart_2584039 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584049 : List Nat := [1, 2, 2, 2, 3, 3, 2, 2, 1, 5]
def baseStart_2584049 : Nat := 118140960795 + 2584049 * 2 ^ 59
def prefixEnd_2584049 : Nat := 4983230072969 + 3 ^ 40 * 2584049 * 2
def baseEnd_2584049 : Nat := 442286390590021876701227

theorem tailTrace_2584049 : CollatzResearch.WordTrace tailWord_2584049 prefixEnd_2584049 442286390590021876701227 := by
  unfold tailWord_2584049
  simp only [CollatzResearch.WordTrace]
  refine ⟨94248009815439268278995201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62832006543626178852663467 94248009815439268278995201)
  ·
    refine ⟨70686007361579451209246401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94248009815439268278995201 70686007361579451209246401)
    ·
      refine ⟨53014505521184588406934801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70686007361579451209246401 53014505521184588406934801)
      ·
        refine ⟨39760879140888441305201101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53014505521184588406934801 39760879140888441305201101)
        ·
          refine ⟨14910329677833165489450413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39760879140888441305201101 14910329677833165489450413)
          ·
            refine ⟨5591373629187437058543905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14910329677833165489450413 5591373629187437058543905)
            ·
              refine ⟨4193530221890577793907929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5591373629187437058543905 4193530221890577793907929)
              ·
                refine ⟨3145147666417933345430947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4193530221890577793907929 3145147666417933345430947)
                ·
                  refine ⟨4717721499626900018146421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3145147666417933345430947 4717721499626900018146421)
                  ·
                    refine ⟨442286390590021876701227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4717721499626900018146421 442286390590021876701227)
                    ·
                      rfl

theorem cell23_2584049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 2, 1, 5].length) (baseStart_2584049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2584049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2584049 prefixEnd_2584049 := by exact prefixLift 2584049
  have htrace : WordTrace (prefixWord ++ tailWord_2584049) baseStart_2584049 baseEnd_2584049 := by
    simpa [prefixWord, tailWord_2584049, baseEnd_2584049] using wordTrace_append hprefix tailTrace_2584049
  have hstable : (prefixWord ++ tailWord_2584049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584049).length < 2 ^ (prefixWord ++ tailWord_2584049).sum := by decide
  have hdescent : baseEnd_2584049 < baseStart_2584049 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584066 : List Nat := [3, 4, 1, 2, 1, 1, 2, 3, 1, 5]
def baseStart_2584066 : Nat := 118140960795 + 2584066 * 2 ^ 59
def prefixEnd_2584066 : Nat := 4983230072969 + 3 ^ 40 * 2584066 * 2
def baseEnd_2584066 : Nat := 442289300313730687863701

theorem tailTrace_2584066 : CollatzResearch.WordTrace tailWord_2584066 prefixEnd_2584066 442289300313730687863701 := by
  unfold tailWord_2584066
  simp only [CollatzResearch.WordTrace]
  refine ⟨23562157464094420045591013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62832419904251786788242701 23562157464094420045591013)
  ·
    refine ⟨4417904524517703758548315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23562157464094420045591013 4417904524517703758548315)
    ·
      refine ⟨6626856786776555637822473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4417904524517703758548315 6626856786776555637822473)
      ·
        refine ⟨4970142590082416728366855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6626856786776555637822473 4970142590082416728366855)
        ·
          refine ⟨7455213885123625092550283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4970142590082416728366855 7455213885123625092550283)
          ·
            refine ⟨11182820827685437638825425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7455213885123625092550283 11182820827685437638825425)
            ·
              refine ⟨8387115620764078229119069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11182820827685437638825425 8387115620764078229119069)
              ·
                refine ⟨3145168357786529335919651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8387115620764078229119069 3145168357786529335919651)
                ·
                  refine ⟨4717752536679794003879477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3145168357786529335919651 4717752536679794003879477)
                  ·
                    refine ⟨442289300313730687863701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4717752536679794003879477 442289300313730687863701)
                    ·
                      rfl

theorem cell23_2584066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_2584066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2584066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2584066 prefixEnd_2584066 := by exact prefixLift 2584066
  have htrace : WordTrace (prefixWord ++ tailWord_2584066) baseStart_2584066 baseEnd_2584066 := by
    simpa [prefixWord, tailWord_2584066, baseEnd_2584066] using wordTrace_append hprefix tailTrace_2584066
  have hstable : (prefixWord ++ tailWord_2584066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584066).length < 2 ^ (prefixWord ++ tailWord_2584066).sum := by decide
  have hdescent : baseEnd_2584066 < baseStart_2584066 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584072 : List Nat := [2, 1, 3, 2, 1, 1, 3, 3, 1, 1, 5]
def baseStart_2584072 : Nat := 118140960795 + 2584072 * 2 ^ 59
def prefixEnd_2584072 : Nat := 4983230072969 + 3 ^ 40 * 2584072 * 2
def baseEnd_2584072 : Nat := 1326870981825119040116075

theorem tailTrace_2584072 : CollatzResearch.WordTrace tailWord_2584072 prefixEnd_2584072 1326870981825119040116075 := by
  unfold tailWord_2584072
  simp only [CollatzResearch.WordTrace]
  refine ⟨47124424347177971603541235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62832565796237295471388313 47124424347177971603541235)
  ·
    refine ⟨70686636520766957405311853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47124424347177971603541235 70686636520766957405311853)
    ·
      refine ⟨26507488695287609026991945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70686636520766957405311853 26507488695287609026991945)
      ·
        refine ⟨19880616521465706770243959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26507488695287609026991945 19880616521465706770243959)
        ·
          refine ⟨29820924782198560155365939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19880616521465706770243959 29820924782198560155365939)
          ·
            refine ⟨44731387173297840233048909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29820924782198560155365939 44731387173297840233048909)
            ·
              refine ⟨16774270189986690087393341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44731387173297840233048909 16774270189986690087393341)
              ·
                refine ⟨6290351321245008782772503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16774270189986690087393341 6290351321245008782772503)
                ·
                  refine ⟨9435526981867513174158755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6290351321245008782772503 9435526981867513174158755)
                  ·
                    refine ⟨14153290472801269761238133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9435526981867513174158755 14153290472801269761238133)
                    ·
                      refine ⟨1326870981825119040116075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14153290472801269761238133 1326870981825119040116075)
                      ·
                        rfl

theorem cell23_2584072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 3, 1, 1, 5].length) (baseStart_2584072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2584072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2584072 prefixEnd_2584072 := by exact prefixLift 2584072
  have htrace : WordTrace (prefixWord ++ tailWord_2584072) baseStart_2584072 baseEnd_2584072 := by
    simpa [prefixWord, tailWord_2584072, baseEnd_2584072] using wordTrace_append hprefix tailTrace_2584072
  have hstable : (prefixWord ++ tailWord_2584072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584072).length < 2 ^ (prefixWord ++ tailWord_2584072).sum := by decide
  have hdescent : baseEnd_2584072 < baseStart_2584072 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584092 : List Nat := [2, 2, 3, 1, 2, 1, 4, 8]
def baseStart_2584092 : Nat := 118140960795 + 2584092 * 2 ^ 59
def prefixEnd_2584092 : Nat := 4983230072969 + 3 ^ 40 * 2584092 * 2
def baseEnd_2584092 : Nat := 49143750053266998587629

theorem tailTrace_2584092 : CollatzResearch.WordTrace tailWord_2584092 prefixEnd_2584092 49143750053266998587629 := by
  unfold tailWord_2584092
  simp only [CollatzResearch.WordTrace]
  refine ⟨47124789077141743311405265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62833052102855657748540353 47124789077141743311405265)
  ·
    refine ⟨35343591807856307483553949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47124789077141743311405265 35343591807856307483553949)
    ·
      refine ⟨13253846927946115306332731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35343591807856307483553949 13253846927946115306332731)
      ·
        refine ⟨19880770391919172959499097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13253846927946115306332731 19880770391919172959499097)
        ·
          refine ⟨14910577793939379719624323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19880770391919172959499097 14910577793939379719624323)
          ·
            refine ⟨22365866690909069579436485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14910577793939379719624323 22365866690909069579436485)
            ·
              refine ⟨4193600004545450546144341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22365866690909069579436485 4193600004545450546144341)
              ·
                refine ⟨49143750053266998587629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4193600004545450546144341 49143750053266998587629)
                ·
                  rfl

theorem cell23_2584092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 8].length) (baseStart_2584092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2584092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2584092 prefixEnd_2584092 := by exact prefixLift 2584092
  have htrace : WordTrace (prefixWord ++ tailWord_2584092) baseStart_2584092 baseEnd_2584092 := by
    simpa [prefixWord, tailWord_2584092, baseEnd_2584092] using wordTrace_append hprefix tailTrace_2584092
  have hstable : (prefixWord ++ tailWord_2584092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584092).length < 2 ^ (prefixWord ++ tailWord_2584092).sum := by decide
  have hdescent : baseEnd_2584092 < baseStart_2584092 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584096 : List Nat := [2, 1, 1, 6, 1, 2, 1, 3, 2, 4]
def baseStart_2584096 : Nat := 118140960795 + 2584096 * 2 ^ 59
def prefixEnd_2584096 : Nat := 4983230072969 + 3 ^ 40 * 2584096 * 2
def baseEnd_2584096 : Nat := 442294435120275648738655

theorem tailTrace_2584096 : CollatzResearch.WordTrace tailWord_2584096 prefixEnd_2584096 442294435120275648738655 := by
  unfold tailWord_2584096
  simp only [CollatzResearch.WordTrace]
  refine ⟨47124862023134497652978071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62833149364179330203970761 47124862023134497652978071)
  ·
    refine ⟨70687293034701746479467107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47124862023134497652978071 70687293034701746479467107)
    ·
      refine ⟨106030939552052619719200661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70687293034701746479467107 106030939552052619719200661)
      ·
        refine ⟨4970200291502466549337531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 106030939552052619719200661 4970200291502466549337531)
        ·
          refine ⟨7455300437253699824006297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4970200291502466549337531 7455300437253699824006297)
          ·
            refine ⟨5591475327940274868004723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7455300437253699824006297 5591475327940274868004723)
            ·
              refine ⟨8387212991910412302007085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5591475327940274868004723 8387212991910412302007085)
              ·
                refine ⟨3145204871966404613252657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8387212991910412302007085 3145204871966404613252657)
                ·
                  refine ⟨2358903653974803459939493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3145204871966404613252657 2358903653974803459939493)
                  ·
                    refine ⟨442294435120275648738655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2358903653974803459939493 442294435120275648738655)
                    ·
                      rfl

theorem cell23_2584096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 3, 2, 4].length) (baseStart_2584096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2584096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2584096 prefixEnd_2584096 := by exact prefixLift 2584096
  have htrace : WordTrace (prefixWord ++ tailWord_2584096) baseStart_2584096 baseEnd_2584096 := by
    simpa [prefixWord, tailWord_2584096, baseEnd_2584096] using wordTrace_append hprefix tailTrace_2584096
  have hstable : (prefixWord ++ tailWord_2584096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584096).length < 2 ^ (prefixWord ++ tailWord_2584096).sum := by decide
  have hdescent : baseEnd_2584096 < baseStart_2584096 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584119 : List Nat := [1, 1, 3, 1, 2, 5, 1, 2, 1, 3, 3]
def baseStart_2584119 : Nat := 118140960795 + 2584119 * 2 ^ 59
def prefixEnd_2584119 : Nat := 4983230072969 + 3 ^ 40 * 2584119 * 2
def baseEnd_2584119 : Nat := 1326895115415880356228359

theorem tailTrace_2584119 : CollatzResearch.WordTrace tailWord_2584119 prefixEnd_2584119 1326895115415880356228359 := by
  unfold tailWord_2584119
  simp only [CollatzResearch.WordTrace]
  refine ⟨94250562925185670234043411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62833708616790446822695607 94250562925185670234043411)
  ·
    refine ⟨141375844387778505351065117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94250562925185670234043411 141375844387778505351065117)
    ·
      refine ⟨53015941645416939506649419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141375844387778505351065117 53015941645416939506649419)
      ·
        refine ⟨79523912468125409259974129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53015941645416939506649419 79523912468125409259974129)
        ·
          refine ⟨59642934351094056944980597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79523912468125409259974129 59642934351094056944980597)
          ·
            refine ⟨5591525095415067838591931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 59642934351094056944980597 5591525095415067838591931)
            ·
              refine ⟨8387287643122601757887897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5591525095415067838591931 8387287643122601757887897)
              ·
                refine ⟨6290465732341951318415923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8387287643122601757887897 6290465732341951318415923)
                ·
                  refine ⟨9435698598512926977623885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6290465732341951318415923 9435698598512926977623885)
                  ·
                    refine ⟨3538386974442347616608957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9435698598512926977623885 3538386974442347616608957)
                    ·
                      refine ⟨1326895115415880356228359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3538386974442347616608957 1326895115415880356228359)
                      ·
                        rfl

theorem cell23_2584119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 2, 1, 3, 3].length) (baseStart_2584119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2584119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2584119 prefixEnd_2584119 := by exact prefixLift 2584119
  have htrace : WordTrace (prefixWord ++ tailWord_2584119) baseStart_2584119 baseEnd_2584119 := by
    simpa [prefixWord, tailWord_2584119, baseEnd_2584119] using wordTrace_append hprefix tailTrace_2584119
  have hstable : (prefixWord ++ tailWord_2584119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584119).length < 2 ^ (prefixWord ++ tailWord_2584119).sum := by decide
  have hdescent : baseEnd_2584119 < baseStart_2584119 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584146 : List Nat := [3, 2, 2, 1, 2, 2, 1, 2, 3, 3, 2]
def baseStart_2584146 : Nat := 118140960795 + 2584146 * 2 ^ 59
def prefixEnd_2584146 : Nat := 4983230072969 + 3 ^ 40 * 2584146 * 2
def baseEnd_2584146 : Nat := 1326908979393551750590735

theorem tailTrace_2584146 : CollatzResearch.WordTrace tailWord_2584146 prefixEnd_2584146 1326908979393551750590735 := by
  unfold tailWord_2584146
  simp only [CollatzResearch.WordTrace]
  refine ⟨23562886924021963461319073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62834365130725235896850861 23562886924021963461319073)
  ·
    refine ⟨17672165193016472595989305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23562886924021963461319073 17672165193016472595989305)
    ·
      refine ⟨13254123894762354446991979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17672165193016472595989305 13254123894762354446991979)
      ·
        refine ⟨19881185842143531670487969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13254123894762354446991979 19881185842143531670487969)
        ·
          refine ⟨14910889381607648752865977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19881185842143531670487969 14910889381607648752865977)
          ·
            refine ⟨11183167036205736564649483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14910889381607648752865977 11183167036205736564649483)
            ·
              refine ⟨16774750554308604846974225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11183167036205736564649483 16774750554308604846974225)
              ·
                refine ⟨12581062915731453635230669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16774750554308604846974225 12581062915731453635230669)
                ·
                  refine ⟨4717898593399295113211501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12581062915731453635230669 4717898593399295113211501)
                  ·
                    refine ⟨1769211972524735667454313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4717898593399295113211501 1769211972524735667454313)
                    ·
                      refine ⟨1326908979393551750590735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1769211972524735667454313 1326908979393551750590735)
                      ·
                        rfl

theorem cell23_2584146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 2, 3, 3, 2].length) (baseStart_2584146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2584146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2584146 prefixEnd_2584146 := by exact prefixLift 2584146
  have htrace : WordTrace (prefixWord ++ tailWord_2584146) baseStart_2584146 baseEnd_2584146 := by
    simpa [prefixWord, tailWord_2584146, baseEnd_2584146] using wordTrace_append hprefix tailTrace_2584146
  have hstable : (prefixWord ++ tailWord_2584146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584146).length < 2 ^ (prefixWord ++ tailWord_2584146).sum := by decide
  have hdescent : baseEnd_2584146 < baseStart_2584146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584150 : List Nat := [5, 2, 2, 2, 1, 1, 2, 1, 1, 2, 4]
def baseStart_2584150 : Nat := 118140960795 + 2584150 * 2 ^ 59
def prefixEnd_2584150 : Nat := 4983230072969 + 3 ^ 40 * 2584150 * 2
def baseEnd_2584150 : Nat := 1326911033316169734940717

theorem tailTrace_2584150 : CollatzResearch.WordTrace tailWord_2584150 prefixEnd_2584150 1326911033316169734940717 := by
  unfold tailWord_2584150
  simp only [CollatzResearch.WordTrace]
  refine ⟨5890730849254585158026369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 62834462392048908352281269 5890730849254585158026369)
  ·
    refine ⟨4418048136940938868519777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5890730849254585158026369 4418048136940938868519777)
    ·
      refine ⟨3313536102705704151389833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4418048136940938868519777 3313536102705704151389833)
      ·
        refine ⟨2485152077029278113542375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3313536102705704151389833 2485152077029278113542375)
        ·
          refine ⟨3727728115543917170313563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2485152077029278113542375 3727728115543917170313563)
          ·
            refine ⟨5591592173315875755470345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3727728115543917170313563 5591592173315875755470345)
            ·
              refine ⟨4193694129986906816602759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5591592173315875755470345 4193694129986906816602759)
              ·
                refine ⟨6290541194980360224904139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4193694129986906816602759 6290541194980360224904139)
                ·
                  refine ⟨9435811792470540337356209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6290541194980360224904139 9435811792470540337356209)
                  ·
                    refine ⟨7076858844352905253017157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9435811792470540337356209 7076858844352905253017157)
                    ·
                      refine ⟨1326911033316169734940717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7076858844352905253017157 1326911033316169734940717)
                      ·
                        rfl

theorem cell23_2584150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_2584150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2584150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2584150 prefixEnd_2584150 := by exact prefixLift 2584150
  have htrace : WordTrace (prefixWord ++ tailWord_2584150) baseStart_2584150 baseEnd_2584150 := by
    simpa [prefixWord, tailWord_2584150, baseEnd_2584150] using wordTrace_append hprefix tailTrace_2584150
  have hstable : (prefixWord ++ tailWord_2584150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584150).length < 2 ^ (prefixWord ++ tailWord_2584150).sum := by decide
  have hdescent : baseEnd_2584150 < baseStart_2584150 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584172 : List Nat := [2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 4]
def baseStart_2584172 : Nat := 118140960795 + 2584172 * 2 ^ 59
def prefixEnd_2584172 : Nat := 4983230072969 + 3 ^ 40 * 2584172 * 2
def baseEnd_2584172 : Nat := 1326922329890568648865615

theorem tailTrace_2584172 : CollatzResearch.WordTrace tailWord_2584172 prefixEnd_2584172 1326922329890568648865615 := by
  unfold tailWord_2584172
  simp only [CollatzResearch.WordTrace]
  refine ⟨47126247996996830142861385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62834997329329106857148513 47126247996996830142861385)
  ·
    refine ⟨35344685997747622607146039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47126247996996830142861385 35344685997747622607146039)
    ·
      refine ⟨53017028996621433910719059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35344685997747622607146039 53017028996621433910719059)
      ·
        refine ⟨79525543494932150866078589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53017028996621433910719059 79525543494932150866078589)
        ·
          refine ⟨29822078810599556574779471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79525543494932150866078589 29822078810599556574779471)
          ·
            refine ⟨44733118215899334862169207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29822078810599556574779471 44733118215899334862169207)
            ·
              refine ⟨67099677323849002293253811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44733118215899334862169207 67099677323849002293253811)
              ·
                refine ⟨100649515985773503439880717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67099677323849002293253811 100649515985773503439880717)
                ·
                  refine ⟨37743568494665063789955269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 100649515985773503439880717 37743568494665063789955269)
                  ·
                    refine ⟨7076919092749699460616613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37743568494665063789955269 7076919092749699460616613)
                    ·
                      refine ⟨1326922329890568648865615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7076919092749699460616613 1326922329890568648865615)
                      ·
                        rfl

theorem cell23_2584172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 4].length) (baseStart_2584172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2584172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2584172 prefixEnd_2584172 := by exact prefixLift 2584172
  have htrace : WordTrace (prefixWord ++ tailWord_2584172) baseStart_2584172 baseEnd_2584172 := by
    simpa [prefixWord, tailWord_2584172, baseEnd_2584172] using wordTrace_append hprefix tailTrace_2584172
  have hstable : (prefixWord ++ tailWord_2584172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584172).length < 2 ^ (prefixWord ++ tailWord_2584172).sum := by decide
  have hdescent : baseEnd_2584172 < baseStart_2584172 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584176 : List Nat := [2, 1, 1, 1, 6, 1, 2, 2, 1, 4, 2]
def baseStart_2584176 : Nat := 118140960795 + 2584176 * 2 ^ 59
def prefixEnd_2584176 : Nat := 4983230072969 + 3 ^ 40 * 2584176 * 2
def baseEnd_2584176 : Nat := 1326924383813186633215597

theorem tailTrace_2584176 : CollatzResearch.WordTrace tailWord_2584176 prefixEnd_2584176 1326924383813186633215597 := by
  unfold tailWord_2584176
  simp only [CollatzResearch.WordTrace]
  refine ⟨47126320942989584484434191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62835094590652779312578921 47126320942989584484434191)
  ·
    refine ⟨70689481414484376726651287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47126320942989584484434191 70689481414484376726651287)
    ·
      refine ⟨106034222121726565089976931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70689481414484376726651287 106034222121726565089976931)
      ·
        refine ⟨159051333182589847634965397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106034222121726565089976931 159051333182589847634965397)
        ·
          refine ⟨7455531242933899107889003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 159051333182589847634965397 7455531242933899107889003)
          ·
            refine ⟨11183296864400848661833505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7455531242933899107889003 11183296864400848661833505)
            ·
              refine ⟨8387472648300636496375129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11183296864400848661833505 8387472648300636496375129)
              ·
                refine ⟨6290604486225477372281347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8387472648300636496375129 6290604486225477372281347)
                ·
                  refine ⟨9435906729338216058422021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6290604486225477372281347 9435906729338216058422021)
                  ·
                    refine ⟨1769232511750915510954129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9435906729338216058422021 1769232511750915510954129)
                    ·
                      refine ⟨1326924383813186633215597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1769232511750915510954129 1326924383813186633215597)
                      ·
                        rfl

theorem cell23_2584176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 2, 1, 4, 2].length) (baseStart_2584176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2584176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2584176 prefixEnd_2584176 := by exact prefixLift 2584176
  have htrace : WordTrace (prefixWord ++ tailWord_2584176) baseStart_2584176 baseEnd_2584176 := by
    simpa [prefixWord, tailWord_2584176, baseEnd_2584176] using wordTrace_append hprefix tailTrace_2584176
  have hstable : (prefixWord ++ tailWord_2584176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584176).length < 2 ^ (prefixWord ++ tailWord_2584176).sum := by decide
  have hdescent : baseEnd_2584176 < baseStart_2584176 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584189 : List Nat := [1, 4, 1, 1, 4, 1, 1, 2, 2, 2, 4]
def baseStart_2584189 : Nat := 118140960795 + 2584189 * 2 ^ 59
def prefixEnd_2584189 : Nat := 4983230072969 + 3 ^ 40 * 2584189 * 2
def baseEnd_2584189 : Nat := 1326931059061695082353037

theorem tailTrace_2584189 : CollatzResearch.WordTrace tailWord_2584189 prefixEnd_2584189 1326931059061695082353037 := by
  unfold tailWord_2584189
  simp only [CollatzResearch.WordTrace]
  refine ⟨94253116034932072189091621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62835410689954714792727747 94253116034932072189091621)
  ·
    refine ⟨17672459256549763535454679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94253116034932072189091621 17672459256549763535454679)
    ·
      refine ⟨26508688884824645303182019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17672459256549763535454679 26508688884824645303182019)
      ·
        refine ⟨39763033327236967954773029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26508688884824645303182019 39763033327236967954773029)
        ·
          refine ⟨7455568748856931491519943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39763033327236967954773029 7455568748856931491519943)
          ·
            refine ⟨11183353123285397237279915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7455568748856931491519943 11183353123285397237279915)
            ·
              refine ⟨16775029684928095855919873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11183353123285397237279915 16775029684928095855919873)
              ·
                refine ⟨12581272263696071891939905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16775029684928095855919873 12581272263696071891939905)
                ·
                  refine ⟨9435954197772053918954929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12581272263696071891939905 9435954197772053918954929)
                  ·
                    refine ⟨7076965648329040439216197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9435954197772053918954929 7076965648329040439216197)
                    ·
                      refine ⟨1326931059061695082353037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7076965648329040439216197 1326931059061695082353037)
                      ·
                        rfl

theorem cell23_2584189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 2, 2, 2, 4].length) (baseStart_2584189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2584189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2584189 prefixEnd_2584189 := by exact prefixLift 2584189
  have htrace : WordTrace (prefixWord ++ tailWord_2584189) baseStart_2584189 baseEnd_2584189 := by
    simpa [prefixWord, tailWord_2584189, baseEnd_2584189] using wordTrace_append hprefix tailTrace_2584189
  have hstable : (prefixWord ++ tailWord_2584189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584189).length < 2 ^ (prefixWord ++ tailWord_2584189).sum := by decide
  have hdescent : baseEnd_2584189 < baseStart_2584189 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584193 : List Nat := [1, 2, 4, 2, 1, 3, 1, 1, 4, 2, 2]
def baseStart_2584193 : Nat := 118140960795 + 2584193 * 2 ^ 59
def prefixEnd_2584193 : Nat := 4983230072969 + 3 ^ 40 * 2584193 * 2
def baseEnd_2584193 : Nat := 1326933112984313066703019

theorem tailTrace_2584193 : CollatzResearch.WordTrace tailWord_2584193 prefixEnd_2584193 1326933112984313066703019 := by
  unfold tailWord_2584193
  simp only [CollatzResearch.WordTrace]
  refine ⟨94253261926917580872237233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62835507951278387248158155 94253261926917580872237233)
  ·
    refine ⟨70689946445188185654177925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94253261926917580872237233 70689946445188185654177925)
    ·
      refine ⟨13254364958472784810158361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70689946445188185654177925 13254364958472784810158361)
      ·
        refine ⟨9940773718854588607618771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13254364958472784810158361 9940773718854588607618771)
        ·
          refine ⟨14911160578281882911428157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9940773718854588607618771 14911160578281882911428157)
          ·
            refine ⟨5591685216855706091785559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14911160578281882911428157 5591685216855706091785559)
            ·
              refine ⟨8387527825283559137678339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5591685216855706091785559 8387527825283559137678339)
              ·
                refine ⟨12581291737925338706517509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8387527825283559137678339 12581291737925338706517509)
                ·
                  refine ⟨2358992200861001007472033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12581291737925338706517509 2358992200861001007472033)
                  ·
                    refine ⟨1769244150645750755604025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2358992200861001007472033 1769244150645750755604025)
                    ·
                      refine ⟨1326933112984313066703019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1769244150645750755604025 1326933112984313066703019)
                      ·
                        rfl

theorem cell23_2584193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 1, 4, 2, 2].length) (baseStart_2584193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2584193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2584193 prefixEnd_2584193 := by exact prefixLift 2584193
  have htrace : WordTrace (prefixWord ++ tailWord_2584193) baseStart_2584193 baseEnd_2584193 := by
    simpa [prefixWord, tailWord_2584193, baseEnd_2584193] using wordTrace_append hprefix tailTrace_2584193
  have hstable : (prefixWord ++ tailWord_2584193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584193).length < 2 ^ (prefixWord ++ tailWord_2584193).sum := by decide
  have hdescent : baseEnd_2584193 < baseStart_2584193 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584199 : List Nat := [1, 1, 4, 2, 1, 4, 2, 1, 7]
def baseStart_2584199 : Nat := 118140960795 + 2584199 * 2 ^ 59
def prefixEnd_2584199 : Nat := 4983230072969 + 3 ^ 40 * 2584199 * 2
def baseEnd_2584199 : Nat := 147437354874248893691999

theorem tailTrace_2584199 : CollatzResearch.WordTrace tailWord_2584199 prefixEnd_2584199 147437354874248893691999 := by
  unfold tailWord_2584199
  simp only [CollatzResearch.WordTrace]
  refine ⟨94253480764895843896955651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62835653843263895931303767 94253480764895843896955651)
  ·
    refine ⟨141380221147343765845433477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94253480764895843896955651 141380221147343765845433477)
    ·
      refine ⟨26508791465126956096018777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 141380221147343765845433477 26508791465126956096018777)
      ·
        refine ⟨19881593598845217072014083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26508791465126956096018777 19881593598845217072014083)
        ·
          refine ⟨29822390398267825608021125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19881593598845217072014083 29822390398267825608021125)
          ·
            refine ⟨5591698199675217301503961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29822390398267825608021125 5591698199675217301503961)
            ·
              refine ⟨4193773649756412976127971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5591698199675217301503961 4193773649756412976127971)
              ·
                refine ⟨6290660474634619464191957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4193773649756412976127971 6290660474634619464191957)
                ·
                  refine ⟨147437354874248893691999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6290660474634619464191957 147437354874248893691999)
                  ·
                    rfl

theorem cell23_2584199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 1, 7].length) (baseStart_2584199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2584199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2584199 prefixEnd_2584199 := by exact prefixLift 2584199
  have htrace : WordTrace (prefixWord ++ tailWord_2584199) baseStart_2584199 baseEnd_2584199 := by
    simpa [prefixWord, tailWord_2584199, baseEnd_2584199] using wordTrace_append hprefix tailTrace_2584199
  have hstable : (prefixWord ++ tailWord_2584199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584199).length < 2 ^ (prefixWord ++ tailWord_2584199).sum := by decide
  have hdescent : baseEnd_2584199 < baseStart_2584199 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584210 : List Nat := [3, 2, 3, 1, 3, 2, 1, 1, 1, 4, 2]
def baseStart_2584210 : Nat := 118140960795 + 2584210 * 2 ^ 59
def prefixEnd_2584210 : Nat := 4983230072969 + 3 ^ 40 * 2584210 * 2
def baseEnd_2584210 : Nat := 1326941842155439500190441

theorem tailTrace_2584210 : CollatzResearch.WordTrace tailWord_2584210 prefixEnd_2584210 1326941842155439500190441 := by
  unfold tailWord_2584210
  simp only [CollatzResearch.WordTrace]
  refine ⟨23563470491963998193901521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62835921311903995183737389 23563470491963998193901521)
  ·
    refine ⟨17672602868972998645426141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23563470491963998193901521 17672602868972998645426141)
    ·
      refine ⟨6627226075864874492034803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17672602868972998645426141 6627226075864874492034803)
      ·
        refine ⟨9940839113797311738052205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6627226075864874492034803 9940839113797311738052205)
        ·
          refine ⟨3727814667673991901769577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9940839113797311738052205 3727814667673991901769577)
          ·
            refine ⟨2795861000755493926327183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3727814667673991901769577 2795861000755493926327183)
            ·
              refine ⟨4193791501133240889490775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2795861000755493926327183 4193791501133240889490775)
              ·
                refine ⟨6290687251699861334236163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4193791501133240889490775 6290687251699861334236163)
                ·
                  refine ⟨9436030877549792001354245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6290687251699861334236163 9436030877549792001354245)
                  ·
                    refine ⟨1769255789540586000253921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9436030877549792001354245 1769255789540586000253921)
                    ·
                      refine ⟨1326941842155439500190441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1769255789540586000253921 1326941842155439500190441)
                      ·
                        rfl

theorem cell23_2584210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 1, 1, 4, 2].length) (baseStart_2584210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2584210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2584210 prefixEnd_2584210 := by exact prefixLift 2584210
  have htrace : WordTrace (prefixWord ++ tailWord_2584210) baseStart_2584210 baseEnd_2584210 := by
    simpa [prefixWord, tailWord_2584210, baseEnd_2584210] using wordTrace_append hprefix tailTrace_2584210
  have hstable : (prefixWord ++ tailWord_2584210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584210).length < 2 ^ (prefixWord ++ tailWord_2584210).sum := by decide
  have hdescent : baseEnd_2584210 < baseStart_2584210 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584249 : List Nat := [1, 2, 1, 4, 1, 1, 3, 1, 4, 1, 4]
def baseStart_2584249 : Nat := 118140960795 + 2584249 * 2 ^ 59
def prefixEnd_2584249 : Nat := 4983230072969 + 3 ^ 40 * 2584249 * 2
def baseEnd_2584249 : Nat := 1326961867900964847602761

theorem tailTrace_2584249 : CollatzResearch.WordTrace tailWord_2584249 prefixEnd_2584249 1326961867900964847602761 := by
  unfold tailWord_2584249
  simp only [CollatzResearch.WordTrace]
  refine ⟨94255304414714702436275801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62836869609809801624183867 94255304414714702436275801)
  ·
    refine ⟨70691478311036026827206851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94255304414714702436275801 70691478311036026827206851)
    ·
      refine ⟨106037217466554040240810277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70691478311036026827206851 106037217466554040240810277)
      ·
        refine ⟨19881978274978882545151927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106037217466554040240810277 19881978274978882545151927)
        ·
          refine ⟨29822967412468323817727891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19881978274978882545151927 29822967412468323817727891)
          ·
            refine ⟨44734451118702485726591837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29822967412468323817727891 44734451118702485726591837)
            ·
              refine ⟨16775419169513432147471939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44734451118702485726591837 16775419169513432147471939)
              ·
                refine ⟨25163128754270148221207909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16775419169513432147471939 25163128754270148221207909)
                ·
                  refine ⟨4718086641425652791476483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25163128754270148221207909 4718086641425652791476483)
                  ·
                    refine ⟨7077129962138479187214725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4718086641425652791476483 7077129962138479187214725)
                    ·
                      refine ⟨1326961867900964847602761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7077129962138479187214725 1326961867900964847602761)
                      ·
                        rfl

theorem cell23_2584249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 4, 1, 4].length) (baseStart_2584249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2584249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2584249 prefixEnd_2584249 := by exact prefixLift 2584249
  have htrace : WordTrace (prefixWord ++ tailWord_2584249) baseStart_2584249 baseEnd_2584249 := by
    simpa [prefixWord, tailWord_2584249, baseEnd_2584249] using wordTrace_append hprefix tailTrace_2584249
  have hstable : (prefixWord ++ tailWord_2584249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584249).length < 2 ^ (prefixWord ++ tailWord_2584249).sum := by decide
  have hdescent : baseEnd_2584249 < baseStart_2584249 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584272 : List Nat := [2, 1, 1, 1, 1, 2, 1, 4, 10]
def baseStart_2584272 : Nat := 118140960795 + 2584272 * 2 ^ 59
def prefixEnd_2584272 : Nat := 4983230072969 + 3 ^ 40 * 2584272 * 2
def baseEnd_2584272 : Nat := 147441519772890917512795

theorem tailTrace_2584272 : CollatzResearch.WordTrace tailWord_2584272 prefixEnd_2584272 147441519772890917512795 := by
  unfold tailWord_2584272
  simp only [CollatzResearch.WordTrace]
  refine ⟨47128071646815688682181535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62837428862420918242908713 47128071646815688682181535)
  ·
    refine ⟨70692107470223533023272303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47128071646815688682181535 70692107470223533023272303)
    ·
      refine ⟨106038161205335299534908455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70692107470223533023272303 106038161205335299534908455)
      ·
        refine ⟨159057241808002949302362683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106038161205335299534908455 159057241808002949302362683)
        ·
          refine ⟨238585862712004423953544025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159057241808002949302362683 238585862712004423953544025)
          ·
            refine ⟨178939397034003317965158019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 238585862712004423953544025 178939397034003317965158019)
            ·
              refine ⟨268409095551004976947737029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 178939397034003317965158019 268409095551004976947737029)
              ·
                refine ⟨50326705415813433177700693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 268409095551004976947737029 50326705415813433177700693)
                ·
                  refine ⟨147441519772890917512795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 50326705415813433177700693 147441519772890917512795)
                  ·
                    rfl

theorem cell23_2584272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 10].length) (baseStart_2584272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2584272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2584272 prefixEnd_2584272 := by exact prefixLift 2584272
  have htrace : WordTrace (prefixWord ++ tailWord_2584272) baseStart_2584272 baseEnd_2584272 := by
    simpa [prefixWord, tailWord_2584272, baseEnd_2584272] using wordTrace_append hprefix tailTrace_2584272
  have hstable : (prefixWord ++ tailWord_2584272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584272).length < 2 ^ (prefixWord ++ tailWord_2584272).sum := by decide
  have hdescent : baseEnd_2584272 < baseStart_2584272 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584293 : List Nat := [1, 3, 1, 4, 1, 1, 2, 5, 1, 4]
def baseStart_2584293 : Nat := 118140960795 + 2584293 * 2 ^ 59
def prefixEnd_2584293 : Nat := 4983230072969 + 3 ^ 40 * 2584293 * 2
def baseEnd_2584293 : Nat := 442328153683254225150853

theorem tailTrace_2584293 : CollatzResearch.WordTrace tailWord_2584293 prefixEnd_2584293 442328153683254225150853 := by
  unfold tailWord_2584293
  simp only [CollatzResearch.WordTrace]
  refine ⟨94256909226555297950877533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62837939484370198633918355 94256909226555297950877533)
  ·
    refine ⟨35346340959958236731579075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94256909226555297950877533 35346340959958236731579075)
    ·
      refine ⟨53019511439937355097368613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35346340959958236731579075 53019511439937355097368613)
      ·
        refine ⟨9941158394988254080756615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53019511439937355097368613 9941158394988254080756615)
        ·
          refine ⟨14911737592482381121134923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9941158394988254080756615 14911737592482381121134923)
          ·
            refine ⟨22367606388723571681702385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14911737592482381121134923 22367606388723571681702385)
            ·
              refine ⟨16775704791542678761276789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22367606388723571681702385 16775704791542678761276789)
              ·
                refine ⟨1572722324207126133869699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16775704791542678761276789 1572722324207126133869699)
                ·
                  refine ⟨2359083486310689200804549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1572722324207126133869699 2359083486310689200804549)
                  ·
                    refine ⟨442328153683254225150853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2359083486310689200804549 442328153683254225150853)
                    ·
                      rfl

theorem cell23_2584293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 5, 1, 4].length) (baseStart_2584293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2584293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2584293 prefixEnd_2584293 := by exact prefixLift 2584293
  have htrace : WordTrace (prefixWord ++ tailWord_2584293) baseStart_2584293 baseEnd_2584293 := by
    simpa [prefixWord, tailWord_2584293, baseEnd_2584293] using wordTrace_append hprefix tailTrace_2584293
  have hstable : (prefixWord ++ tailWord_2584293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584293).length < 2 ^ (prefixWord ++ tailWord_2584293).sum := by decide
  have hdescent : baseEnd_2584293 < baseStart_2584293 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584306 : List Nat := [3, 2, 1, 3, 1, 1, 4, 2, 6]
def baseStart_2584306 : Nat := 118140960795 + 2584306 * 2 ^ 59
def prefixEnd_2584306 : Nat := 4983230072969 + 3 ^ 40 * 2584306 * 2
def baseEnd_2584306 : Nat := 147443459588696791621111

theorem tailTrace_2584306 : CollatzResearch.WordTrace tailWord_2584306 prefixEnd_2584306 147443459588696791621111 := by
  unfold tailWord_2584306
  simp only [CollatzResearch.WordTrace]
  refine ⟨23564345843877050292775193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62838255583672134114067181 23564345843877050292775193)
  ·
    refine ⟨17673259382907787719581395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23564345843877050292775193 17673259382907787719581395)
    ·
      refine ⟨26509889074361681579372093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17673259382907787719581395 26509889074361681579372093)
      ·
        refine ⟨9941208402885630592264535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26509889074361681579372093 9941208402885630592264535)
        ·
          refine ⟨14911812604328445888396803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9941208402885630592264535 14911812604328445888396803)
          ·
            refine ⟨22367718906492668832595205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14911812604328445888396803 22367718906492668832595205)
            ·
              refine ⟨4193947294967375406111601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22367718906492668832595205 4193947294967375406111601)
              ·
                refine ⟨3145460471225531554583701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4193947294967375406111601 3145460471225531554583701)
                ·
                  refine ⟨147443459588696791621111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3145460471225531554583701 147443459588696791621111)
                  ·
                    rfl

theorem cell23_2584306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 2, 6].length) (baseStart_2584306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2584306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2584306 prefixEnd_2584306 := by exact prefixLift 2584306
  have htrace : WordTrace (prefixWord ++ tailWord_2584306) baseStart_2584306 baseEnd_2584306 := by
    simpa [prefixWord, tailWord_2584306, baseEnd_2584306] using wordTrace_append hprefix tailTrace_2584306
  have hstable : (prefixWord ++ tailWord_2584306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584306).length < 2 ^ (prefixWord ++ tailWord_2584306).sum := by decide
  have hdescent : baseEnd_2584306 < baseStart_2584306 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584310 : List Nat := [5, 1, 1, 1, 1, 4, 1, 4, 1, 4]
def baseStart_2584310 : Nat := 118140960795 + 2584310 * 2 ^ 59
def prefixEnd_2584310 : Nat := 4983230072969 + 3 ^ 40 * 2584310 * 2
def baseEnd_2584310 : Nat := 442331063406963036313327

theorem tailTrace_2584310 : CollatzResearch.WordTrace tailWord_2584310 prefixEnd_2584310 442331063406963036313327 := by
  unfold tailWord_2584310
  simp only [CollatzResearch.WordTrace]
  refine ⟨5891095579218356865890399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 62838352844995806569497589 5891095579218356865890399)
  ·
    refine ⟨8836643368827535298835599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5891095579218356865890399 8836643368827535298835599)
    ·
      refine ⟨13254965053241302948253399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8836643368827535298835599 13254965053241302948253399)
      ·
        refine ⟨19882447579861954422380099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13254965053241302948253399 19882447579861954422380099)
        ·
          refine ⟨29823671369792931633570149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19882447579861954422380099 29823671369792931633570149)
          ·
            refine ⟨5591938381836174681294403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29823671369792931633570149 5591938381836174681294403)
            ·
              refine ⟨8387907572754262021941605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5591938381836174681294403 8387907572754262021941605)
              ·
                refine ⟨1572732669891424129114051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8387907572754262021941605 1572732669891424129114051)
                ·
                  refine ⟨2359099004837136193671077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1572732669891424129114051 2359099004837136193671077)
                  ·
                    refine ⟨442331063406963036313327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2359099004837136193671077 442331063406963036313327)
                    ·
                      rfl

theorem cell23_2584310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 4, 1, 4].length) (baseStart_2584310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2584310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2584310 prefixEnd_2584310 := by exact prefixLift 2584310
  have htrace : WordTrace (prefixWord ++ tailWord_2584310) baseStart_2584310 baseEnd_2584310 := by
    simpa [prefixWord, tailWord_2584310, baseEnd_2584310] using wordTrace_append hprefix tailTrace_2584310
  have hstable : (prefixWord ++ tailWord_2584310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584310).length < 2 ^ (prefixWord ++ tailWord_2584310).sum := by decide
  have hdescent : baseEnd_2584310 < baseStart_2584310 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584319 : List Nat := [1, 1, 2, 2, 1, 3, 3, 2, 3, 5]
def baseStart_2584319 : Nat := 118140960795 + 2584319 * 2 ^ 59
def prefixEnd_2584319 : Nat := 4983230072969 + 3 ^ 40 * 2584319 * 2
def baseEnd_2584319 : Nat := 442332603848926524575813

theorem tailTrace_2584319 : CollatzResearch.WordTrace tailWord_2584319 prefixEnd_2584319 442332603848926524575813 := by
  unfold tailWord_2584319
  simp only [CollatzResearch.WordTrace]
  refine ⟨94257857524461104391324011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62838571682974069594216007 94257857524461104391324011)
  ·
    refine ⟨141386786286691656586986017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94257857524461104391324011 141386786286691656586986017)
    ·
      refine ⟨106040089715018742440239513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141386786286691656586986017 106040089715018742440239513)
      ·
        refine ⟨79530067286264056830179635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106040089715018742440239513 79530067286264056830179635)
        ·
          refine ⟨119295100929396085245269453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79530067286264056830179635 119295100929396085245269453)
          ·
            refine ⟨44735662848523531966976045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 119295100929396085245269453 44735662848523531966976045)
            ·
              refine ⟨16775873568196324487616017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44735662848523531966976045 16775873568196324487616017)
              ·
                refine ⟨12581905176147243365712013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16775873568196324487616017 12581905176147243365712013)
                ·
                  refine ⟨4718214441055216262142005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12581905176147243365712013 4718214441055216262142005)
                  ·
                    refine ⟨442332603848926524575813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4718214441055216262142005 442332603848926524575813)
                    ·
                      rfl

theorem cell23_2584319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 2, 3, 5].length) (baseStart_2584319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2584319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2584319 prefixEnd_2584319 := by exact prefixLift 2584319
  have htrace : WordTrace (prefixWord ++ tailWord_2584319) baseStart_2584319 baseEnd_2584319 := by
    simpa [prefixWord, tailWord_2584319, baseEnd_2584319] using wordTrace_append hprefix tailTrace_2584319
  have hstable : (prefixWord ++ tailWord_2584319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584319).length < 2 ^ (prefixWord ++ tailWord_2584319).sum := by decide
  have hdescent : baseEnd_2584319 < baseStart_2584319 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584343 : List Nat := [1, 1, 3, 4, 2, 2, 1, 1, 1, 5, 2]
def baseStart_2584343 : Nat := 118140960795 + 2584343 * 2 ^ 59
def prefixEnd_2584343 : Nat := 4983230072969 + 3 ^ 40 * 2584343 * 2
def baseEnd_2584343 : Nat := 1327010135082487479827329

theorem tailTrace_2584343 : CollatzResearch.WordTrace tailWord_2584343 prefixEnd_2584343 1327010135082487479827329 := by
  unfold tailWord_2584343
  simp only [CollatzResearch.WordTrace]
  refine ⟨94258732876374156490197683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62839155250916104326798455 94258732876374156490197683)
  ·
    refine ⟨141388099314561234735296525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94258732876374156490197683 141388099314561234735296525)
    ·
      refine ⟨53020537242960463025736197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141388099314561234735296525 53020537242960463025736197)
      ·
        refine ⟨9941350733055086817325537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53020537242960463025736197 9941350733055086817325537)
        ·
          refine ⟨7456013049791315112994153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9941350733055086817325537 7456013049791315112994153)
          ·
            refine ⟨5592009787343486334745615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7456013049791315112994153 5592009787343486334745615)
            ·
              refine ⟨8388014681015229502118423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5592009787343486334745615 8388014681015229502118423)
              ·
                refine ⟨12582022021522844253177635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8388014681015229502118423 12582022021522844253177635)
                ·
                  refine ⟨18873033032284266379766453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12582022021522844253177635 18873033032284266379766453)
                  ·
                    refine ⟨1769346846776649973103105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18873033032284266379766453 1769346846776649973103105)
                    ·
                      refine ⟨1327010135082487479827329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1769346846776649973103105 1327010135082487479827329)
                      ·
                        rfl

theorem cell23_2584343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 1, 1, 5, 2].length) (baseStart_2584343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2584343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2584343 prefixEnd_2584343 := by exact prefixLift 2584343
  have htrace : WordTrace (prefixWord ++ tailWord_2584343) baseStart_2584343 baseEnd_2584343 := by
    simpa [prefixWord, tailWord_2584343, baseEnd_2584343] using wordTrace_append hprefix tailTrace_2584343
  have hstable : (prefixWord ++ tailWord_2584343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584343).length < 2 ^ (prefixWord ++ tailWord_2584343).sum := by decide
  have hdescent : baseEnd_2584343 < baseStart_2584343 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584353 : List Nat := [1, 2, 3, 2, 1, 3, 4, 1, 1, 5]
def baseStart_2584353 : Nat := 118140960795 + 2584353 * 2 ^ 59
def prefixEnd_2584353 : Nat := 4983230072969 + 3 ^ 40 * 2584353 * 2
def baseEnd_2584353 : Nat := 442338423296344146900761

theorem tailTrace_2584353 : CollatzResearch.WordTrace tailWord_2584353 prefixEnd_2584353 442338423296344146900761 := by
  unfold tailWord_2584353
  simp only [CollatzResearch.WordTrace]
  refine ⟨94259097606337928198061713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62839398404225285465374475 94259097606337928198061713)
  ·
    refine ⟨70694323204753446148546285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94259097606337928198061713 70694323204753446148546285)
    ·
      refine ⟨26510371201782542305704857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70694323204753446148546285 26510371201782542305704857)
      ·
        refine ⟨19882778401336906729278643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26510371201782542305704857 19882778401336906729278643)
        ·
          refine ⟨29824167602005360093917965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19882778401336906729278643 29824167602005360093917965)
          ·
            refine ⟨11184062850752010035219237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29824167602005360093917965 11184062850752010035219237)
            ·
              refine ⟨2097011784516001881603607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11184062850752010035219237 2097011784516001881603607)
              ·
                refine ⟨3145517676774002822405411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2097011784516001881603607 3145517676774002822405411)
                ·
                  refine ⟨4718276515161004233608117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3145517676774002822405411 4718276515161004233608117)
                  ·
                    refine ⟨442338423296344146900761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4718276515161004233608117 442338423296344146900761)
                    ·
                      rfl

theorem cell23_2584353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 4, 1, 1, 5].length) (baseStart_2584353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2584353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2584353 prefixEnd_2584353 := by exact prefixLift 2584353
  have htrace : WordTrace (prefixWord ++ tailWord_2584353) baseStart_2584353 baseEnd_2584353 := by
    simpa [prefixWord, tailWord_2584353, baseEnd_2584353] using wordTrace_append hprefix tailTrace_2584353
  have hstable : (prefixWord ++ tailWord_2584353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584353).length < 2 ^ (prefixWord ++ tailWord_2584353).sum := by decide
  have hdescent : baseEnd_2584353 < baseStart_2584353 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584376 : List Nat := [2, 1, 2, 1, 3, 4, 1, 2, 1, 1, 5]
def baseStart_2584376 : Nat := 118140960795 + 2584376 * 2 ^ 59
def prefixEnd_2584376 : Nat := 4983230072969 + 3 ^ 40 * 2584376 * 2
def baseEnd_2584376 : Nat := 1327027079944085850714677

theorem tailTrace_2584376 : CollatzResearch.WordTrace tailWord_2584376 prefixEnd_2584376 1327027079944085850714677 := by
  unfold tailWord_2584376
  simp only [CollatzResearch.WordTrace]
  refine ⟨47129968242627301563074491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62839957656836402084099321 47129968242627301563074491)
  ·
    refine ⟨70694952363940952344611737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47129968242627301563074491 70694952363940952344611737)
    ·
      refine ⟨53021214272955714258458803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70694952363940952344611737 53021214272955714258458803)
      ·
        refine ⟨79531821409433571387688205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53021214272955714258458803 79531821409433571387688205)
        ·
          refine ⟨29824433028537589270383077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79531821409433571387688205 29824433028537589270383077)
          ·
            refine ⟨5592081192850797988196827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29824433028537589270383077 5592081192850797988196827)
            ·
              refine ⟨8388121789276196982295241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5592081192850797988196827 8388121789276196982295241)
              ·
                refine ⟨6291091341957147736721431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8388121789276196982295241 6291091341957147736721431)
                ·
                  refine ⟨9436637012935721605082147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6291091341957147736721431 9436637012935721605082147)
                  ·
                    refine ⟨14154955519403582407623221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9436637012935721605082147 14154955519403582407623221)
                    ·
                      refine ⟨1327027079944085850714677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14154955519403582407623221 1327027079944085850714677)
                      ·
                        rfl

theorem cell23_2584376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 2, 1, 1, 5].length) (baseStart_2584376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2584376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2584376 prefixEnd_2584376 := by exact prefixLift 2584376
  have htrace : WordTrace (prefixWord ++ tailWord_2584376) baseStart_2584376 baseEnd_2584376 := by
    simpa [prefixWord, tailWord_2584376, baseEnd_2584376] using wordTrace_append hprefix tailTrace_2584376
  have hstable : (prefixWord ++ tailWord_2584376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584376).length < 2 ^ (prefixWord ++ tailWord_2584376).sum := by decide
  have hdescent : baseEnd_2584376 < baseStart_2584376 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584383 : List Nat := [1, 1, 2, 2, 6, 2, 1, 1, 1, 6]
def baseStart_2584383 : Nat := 118140960795 + 2584383 * 2 ^ 59
def prefixEnd_2584383 : Nat := 4983230072969 + 3 ^ 40 * 2584383 * 2
def baseEnd_2584383 : Nat := 442343558102889107775715

theorem tailTrace_2584383 : CollatzResearch.WordTrace tailWord_2584383 prefixEnd_2584383 442343558102889107775715 := by
  unfold tailWord_2584383
  simp only [CollatzResearch.WordTrace]
  refine ⟨94260191796229243321653803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62840127864152828881102535 94260191796229243321653803)
  ·
    refine ⟨141390287694343864982480705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94260191796229243321653803 141390287694343864982480705)
    ·
      refine ⟨106042715770757898736860529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141390287694343864982480705 106042715770757898736860529)
      ·
        refine ⟨79532036828068424052645397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106042715770757898736860529 79532036828068424052645397)
        ·
          refine ⟨3728064226315707377467753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 79532036828068424052645397 3728064226315707377467753)
          ·
            refine ⟨2796048169736780533100815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3728064226315707377467753 2796048169736780533100815)
            ·
              refine ⟨4194072254605170799651223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2796048169736780533100815 4194072254605170799651223)
              ·
                refine ⟨6291108381907756199476835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4194072254605170799651223 6291108381907756199476835)
                ·
                  refine ⟨9436662572861634299215253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6291108381907756199476835 9436662572861634299215253)
                  ·
                    refine ⟨442343558102889107775715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9436662572861634299215253 442343558102889107775715)
                    ·
                      rfl

theorem cell23_2584383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 1, 1, 6].length) (baseStart_2584383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2584383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2584383 prefixEnd_2584383 := by exact prefixLift 2584383
  have htrace : WordTrace (prefixWord ++ tailWord_2584383) baseStart_2584383 baseEnd_2584383 := by
    simpa [prefixWord, tailWord_2584383, baseEnd_2584383] using wordTrace_append hprefix tailTrace_2584383
  have hstable : (prefixWord ++ tailWord_2584383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584383).length < 2 ^ (prefixWord ++ tailWord_2584383).sum := by decide
  have hdescent : baseEnd_2584383 < baseStart_2584383 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584393 : List Nat := [1, 2, 1, 1, 2, 4, 4, 2, 1, 2, 3]
def baseStart_2584393 : Nat := 118140960795 + 2584393 * 2 ^ 59
def prefixEnd_2584393 : Nat := 4983230072969 + 3 ^ 40 * 2584393 * 2
def baseEnd_2584393 : Nat := 1327035809115212284202099

theorem tailTrace_2584393 : CollatzResearch.WordTrace tailWord_2584393 prefixEnd_2584393 1327035809115212284202099 := by
  unfold tailWord_2584393
  simp only [CollatzResearch.WordTrace]
  refine ⟨94260556526193015029517833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62840371017462010019678555 94260556526193015029517833)
  ·
    refine ⟨70695417394644761272138375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94260556526193015029517833 70695417394644761272138375)
    ·
      refine ⟨106043126091967141908207563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70695417394644761272138375 106043126091967141908207563)
      ·
        refine ⟨159064689137950712862311345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106043126091967141908207563 159064689137950712862311345)
        ·
          refine ⟨119298516853463034646733509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159064689137950712862311345 119298516853463034646733509)
          ·
            refine ⟨22368471910024318996262533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 119298516853463034646733509 22368471910024318996262533)
            ·
              refine ⟨4194088483129559811799225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22368471910024318996262533 4194088483129559811799225)
              ·
                refine ⟨3145566362347169858849419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4194088483129559811799225 3145566362347169858849419)
                ·
                  refine ⟨4718349543520754788274129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3145566362347169858849419 4718349543520754788274129)
                  ·
                    refine ⟨3538762157640566091205597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4718349543520754788274129 3538762157640566091205597)
                    ·
                      refine ⟨1327035809115212284202099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3538762157640566091205597 1327035809115212284202099)
                      ·
                        rfl

theorem cell23_2584393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 2, 1, 2, 3].length) (baseStart_2584393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2584393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2584393 prefixEnd_2584393 := by exact prefixLift 2584393
  have htrace : WordTrace (prefixWord ++ tailWord_2584393) baseStart_2584393 baseEnd_2584393 := by
    simpa [prefixWord, tailWord_2584393, baseEnd_2584393] using wordTrace_append hprefix tailTrace_2584393
  have hstable : (prefixWord ++ tailWord_2584393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584393).length < 2 ^ (prefixWord ++ tailWord_2584393).sum := by decide
  have hdescent : baseEnd_2584393 < baseStart_2584393 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584396 : List Nat := [2, 2, 1, 3, 4, 1, 1, 9]
def baseStart_2584396 : Nat := 118140960795 + 2584396 * 2 ^ 59
def prefixEnd_2584396 : Nat := 4983230072969 + 3 ^ 40 * 2584396 * 2
def baseEnd_2584396 : Nat := 49149531465080584165355

theorem tailTrace_2584396 : CollatzResearch.WordTrace tailWord_2584396 prefixEnd_2584396 49149531465080584165355 := by
  unfold tailWord_2584396
  simp only [CollatzResearch.WordTrace]
  refine ⟨47130332972591073270938521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62840443963454764361251361 47130332972591073270938521)
  ·
    refine ⟨35347749729443304953203891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47130332972591073270938521 35347749729443304953203891)
    ·
      refine ⟨53021624594164957429805837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35347749729443304953203891 53021624594164957429805837)
      ·
        refine ⟨19883109222811859036177189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53021624594164957429805837 19883109222811859036177189)
        ·
          refine ⟨3728082979277223569283223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19883109222811859036177189 3728082979277223569283223)
          ·
            refine ⟨5592124468915835353924835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3728082979277223569283223 5592124468915835353924835)
            ·
              refine ⟨8388186703373753030887253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5592124468915835353924835 8388186703373753030887253)
              ·
                refine ⟨49149531465080584165355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8388186703373753030887253 49149531465080584165355)
                ·
                  rfl

theorem cell23_2584396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 9].length) (baseStart_2584396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2584396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2584396 prefixEnd_2584396 := by exact prefixLift 2584396
  have htrace : WordTrace (prefixWord ++ tailWord_2584396) baseStart_2584396 baseEnd_2584396 := by
    simpa [prefixWord, tailWord_2584396, baseEnd_2584396] using wordTrace_append hprefix tailTrace_2584396
  have hstable : (prefixWord ++ tailWord_2584396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584396).length < 2 ^ (prefixWord ++ tailWord_2584396).sum := by decide
  have hdescent : baseEnd_2584396 < baseStart_2584396 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584423 : List Nat := [1, 1, 5, 1, 2, 1, 1, 3, 4, 1, 3]
def baseStart_2584423 : Nat := 118140960795 + 2584423 * 2 ^ 59
def prefixEnd_2584423 : Nat := 4983230072969 + 3 ^ 40 * 2584423 * 2
def baseEnd_2584423 : Nat := 1327051213534847166826961

theorem tailTrace_2584423 : CollatzResearch.WordTrace tailWord_2584423 prefixEnd_2584423 1327051213534847166826961 := by
  unfold tailWord_2584423
  simp only [CollatzResearch.WordTrace]
  refine ⟨94261650716084330153109923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62841100477389553435406615 94261650716084330153109923)
  ·
    refine ⟨141392476074126495229664885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94261650716084330153109923 141392476074126495229664885)
    ·
      refine ⟨13255544631949358927781083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 141392476074126495229664885 13255544631949358927781083)
      ·
        refine ⟨19883316947924038391671625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13255544631949358927781083 19883316947924038391671625)
        ·
          refine ⟨14912487710943028793753719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19883316947924038391671625 14912487710943028793753719)
          ·
            refine ⟨22368731566414543190630579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14912487710943028793753719 22368731566414543190630579)
            ·
              refine ⟨33553097349621814785945869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22368731566414543190630579 33553097349621814785945869)
              ·
                refine ⟨12582411506108180544729701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33553097349621814785945869 12582411506108180544729701)
                ·
                  refine ⟨2359202157395283852136819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12582411506108180544729701 2359202157395283852136819)
                  ·
                    refine ⟨3538803236092925778205229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2359202157395283852136819 3538803236092925778205229)
                    ·
                      refine ⟨1327051213534847166826961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3538803236092925778205229 1327051213534847166826961)
                      ·
                        rfl

theorem cell23_2584423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 3, 4, 1, 3].length) (baseStart_2584423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2584423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2584423 prefixEnd_2584423 := by exact prefixLift 2584423
  have htrace : WordTrace (prefixWord ++ tailWord_2584423) baseStart_2584423 baseEnd_2584423 := by
    simpa [prefixWord, tailWord_2584423, baseEnd_2584423] using wordTrace_append hprefix tailTrace_2584423
  have hstable : (prefixWord ++ tailWord_2584423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584423).length < 2 ^ (prefixWord ++ tailWord_2584423).sum := by decide
  have hdescent : baseEnd_2584423 < baseStart_2584423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584424 : List Nat := [2, 1, 4, 2, 1, 1, 5, 2, 1, 2, 2]
def baseStart_2584424 : Nat := 118140960795 + 2584424 * 2 ^ 59
def prefixEnd_2584424 : Nat := 4983230072969 + 3 ^ 40 * 2584424 * 2
def baseEnd_2584424 : Nat := 1327051727015501662914457

theorem tailTrace_2584424 : CollatzResearch.WordTrace tailWord_2584424 prefixEnd_2584424 1327051727015501662914457 := by
  unfold tailWord_2584424
  simp only [CollatzResearch.WordTrace]
  refine ⟨47130843594540353661948163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62841124792720471549264217 47130843594540353661948163)
  ·
    refine ⟨70696265391810530492922245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47130843594540353661948163 70696265391810530492922245)
    ·
      refine ⟨13255549760964474467422921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70696265391810530492922245 13255549760964474467422921)
      ·
        refine ⟨9941662320723355850567191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13255549760964474467422921 9941662320723355850567191)
        ·
          refine ⟨14912493481085033775850787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9941662320723355850567191 14912493481085033775850787)
          ·
            refine ⟨22368740221627550663776181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14912493481085033775850787 22368740221627550663776181)
            ·
              refine ⟨2097069395777582874729017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22368740221627550663776181 2097069395777582874729017)
              ·
                refine ⟨1572802046833187156046763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2097069395777582874729017 1572802046833187156046763)
                ·
                  refine ⟨2359203070249780734070145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1572802046833187156046763 2359203070249780734070145)
                  ·
                    refine ⟨1769402302687335550552609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2359203070249780734070145 1769402302687335550552609)
                    ·
                      refine ⟨1327051727015501662914457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1769402302687335550552609 1327051727015501662914457)
                      ·
                        rfl

theorem cell23_2584424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 5, 2, 1, 2, 2].length) (baseStart_2584424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2584424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2584424 prefixEnd_2584424 := by exact prefixLift 2584424
  have htrace : WordTrace (prefixWord ++ tailWord_2584424) baseStart_2584424 baseEnd_2584424 := by
    simpa [prefixWord, tailWord_2584424, baseEnd_2584424] using wordTrace_append hprefix tailTrace_2584424
  have hstable : (prefixWord ++ tailWord_2584424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584424).length < 2 ^ (prefixWord ++ tailWord_2584424).sum := by decide
  have hdescent : baseEnd_2584424 < baseStart_2584424 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584433 : List Nat := [1, 2, 2, 2, 1, 3, 2, 2, 3, 3, 2]
def baseStart_2584433 : Nat := 118140960795 + 2584433 * 2 ^ 59
def prefixEnd_2584433 : Nat := 4983230072969 + 3 ^ 40 * 2584433 * 2
def baseEnd_2584433 : Nat := 1327056348341392127701915

theorem tailTrace_2584433 : CollatzResearch.WordTrace tailWord_2584433 prefixEnd_2584433 1327056348341392127701915 := by
  unfold tailWord_2584433
  simp only [CollatzResearch.WordTrace]
  refine ⟨94262015446048101860973953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62841343630698734573982635 94262015446048101860973953)
  ·
    refine ⟨70696511584536076395730465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94262015446048101860973953 70696511584536076395730465)
    ·
      refine ⟨53022383688402057296797849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70696511584536076395730465 53022383688402057296797849)
      ·
        refine ⟨39766787766301542972598387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53022383688402057296797849 39766787766301542972598387)
        ·
          refine ⟨59650181649452314458897581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39766787766301542972598387 59650181649452314458897581)
          ·
            refine ⟨22368818118544617922086593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59650181649452314458897581 22368818118544617922086593)
            ·
              refine ⟨16776613588908463441564945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22368818118544617922086593 16776613588908463441564945)
              ·
                refine ⟨12582460191681347581173709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16776613588908463441564945 12582460191681347581173709)
                ·
                  refine ⟨4718422571880505342940141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12582460191681347581173709 4718422571880505342940141)
                  ·
                    refine ⟨1769408464455189503602553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4718422571880505342940141 1769408464455189503602553)
                    ·
                      refine ⟨1327056348341392127701915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1769408464455189503602553 1327056348341392127701915)
                      ·
                        rfl

theorem cell23_2584433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 2, 3, 3, 2].length) (baseStart_2584433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2584433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2584433 prefixEnd_2584433 := by exact prefixLift 2584433
  have htrace : WordTrace (prefixWord ++ tailWord_2584433) baseStart_2584433 baseEnd_2584433 := by
    simpa [prefixWord, tailWord_2584433, baseEnd_2584433] using wordTrace_append hprefix tailTrace_2584433
  have hstable : (prefixWord ++ tailWord_2584433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584433).length < 2 ^ (prefixWord ++ tailWord_2584433).sum := by decide
  have hdescent : baseEnd_2584433 < baseStart_2584433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584497 : List Nat := [1, 2, 2, 4, 2, 1, 2, 3, 2, 2, 2]
def baseStart_2584497 : Nat := 118140960795 + 2584497 * 2 ^ 59
def prefixEnd_2584497 : Nat := 4983230072969 + 3 ^ 40 * 2584497 * 2
def baseEnd_2584497 : Nat := 1327089211103279877301621

theorem tailTrace_2584497 : CollatzResearch.WordTrace tailWord_2584497 prefixEnd_2584497 1327089211103279877301621 := by
  unfold tailWord_2584497
  simp only [CollatzResearch.WordTrace]
  refine ⟨94264349717816240791303745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62842899811877493860869163 94264349717816240791303745)
  ·
    refine ⟨70698262288362180593477809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94264349717816240791303745 70698262288362180593477809)
    ·
      refine ⟨53023696716271635445108357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70698262288362180593477809 53023696716271635445108357)
      ·
        refine ⟨9941943134300931645957817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53023696716271635445108357 9941943134300931645957817)
        ·
          refine ⟨7456457350725698734468363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9941943134300931645957817 7456457350725698734468363)
          ·
            refine ⟨11184686026088548101702545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7456457350725698734468363 11184686026088548101702545)
            ·
              refine ⟨8388514519566411076276909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11184686026088548101702545 8388514519566411076276909)
              ·
                refine ⟨3145692944837404153603841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8388514519566411076276909 3145692944837404153603841)
                ·
                  refine ⟨2359269708628053115202881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3145692944837404153603841 2359269708628053115202881)
                  ·
                    refine ⟨1769452281471039836402161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2359269708628053115202881 1769452281471039836402161)
                    ·
                      refine ⟨1327089211103279877301621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1769452281471039836402161 1327089211103279877301621)
                      ·
                        rfl

theorem cell23_2584497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 3, 2, 2, 2].length) (baseStart_2584497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2584497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2584497 prefixEnd_2584497 := by exact prefixLift 2584497
  have htrace : WordTrace (prefixWord ++ tailWord_2584497) baseStart_2584497 baseEnd_2584497 := by
    simpa [prefixWord, tailWord_2584497, baseEnd_2584497] using wordTrace_append hprefix tailTrace_2584497
  have hstable : (prefixWord ++ tailWord_2584497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584497).length < 2 ^ (prefixWord ++ tailWord_2584497).sum := by decide
  have hdescent : baseEnd_2584497 < baseStart_2584497 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584520 : List Nat := [2, 1, 3, 1, 4, 2, 2, 3, 5]
def baseStart_2584520 : Nat := 118140960795 + 2584520 * 2 ^ 59
def prefixEnd_2584520 : Nat := 4983230072969 + 3 ^ 40 * 2584520 * 2
def baseEnd_2584520 : Nat := 147455669017592587479335

theorem tailTrace_2584520 : CollatzResearch.WordTrace tailWord_2584520 prefixEnd_2584520 147455669017592587479335 := by
  unfold tailWord_2584520
  simp only [CollatzResearch.WordTrace]
  refine ⟨47132594298366457859695507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62843459064488610479594009 47132594298366457859695507)
  ·
    refine ⟨70698891447549686789543261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47132594298366457859695507 70698891447549686789543261)
    ·
      refine ⟨26512084292831132546078723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70698891447549686789543261 26512084292831132546078723)
      ·
        refine ⟨39768126439246698819118085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26512084292831132546078723 39768126439246698819118085)
        ·
          refine ⟨7456523707358756028584641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39768126439246698819118085 7456523707358756028584641)
          ·
            refine ⟨5592392780519067021438481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7456523707358756028584641 5592392780519067021438481)
            ·
              refine ⟨4194294585389300266078861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5592392780519067021438481 4194294585389300266078861)
              ·
                refine ⟨1572860469520987599779573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4194294585389300266078861 1572860469520987599779573)
                ·
                  refine ⟨147455669017592587479335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1572860469520987599779573 147455669017592587479335)
                  ·
                    rfl

theorem cell23_2584520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 3, 5].length) (baseStart_2584520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2584520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2584520 prefixEnd_2584520 := by exact prefixLift 2584520
  have htrace : WordTrace (prefixWord ++ tailWord_2584520) baseStart_2584520 baseEnd_2584520 := by
    simpa [prefixWord, tailWord_2584520, baseEnd_2584520] using wordTrace_append hprefix tailTrace_2584520
  have hstable : (prefixWord ++ tailWord_2584520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584520).length < 2 ^ (prefixWord ++ tailWord_2584520).sum := by decide
  have hdescent : baseEnd_2584520 < baseStart_2584520 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584573 : List Nat := [1, 4, 1, 1, 1, 2, 4, 1, 1, 4, 3]
def baseStart_2584573 : Nat := 118140960795 + 2584573 * 2 ^ 59
def prefixEnd_2584573 : Nat := 4983230072969 + 3 ^ 40 * 2584573 * 2
def baseEnd_2584573 : Nat := 1327128235633021579951271

theorem tailTrace_2584573 : CollatzResearch.WordTrace tailWord_2584573 prefixEnd_2584573 1327128235633021579951271 := by
  unfold tailWord_2584573
  simp only [CollatzResearch.WordTrace]
  refine ⟨94267121665540905771070373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62844747777027270514046915 94267121665540905771070373)
  ·
    refine ⟨17675085312288919832075695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94267121665540905771070373 17675085312288919832075695)
    ·
      refine ⟨26512627968433379748113543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17675085312288919832075695 26512627968433379748113543)
      ·
        refine ⟨39768941952650069622170315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26512627968433379748113543 39768941952650069622170315)
        ·
          refine ⟨59653412928975104433255473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39768941952650069622170315 59653412928975104433255473)
          ·
            refine ⟨44740059696731328324941605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59653412928975104433255473 44740059696731328324941605)
            ·
              refine ⟨8388761193137124060926551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44740059696731328324941605 8388761193137124060926551)
              ·
                refine ⟨12583141789705686091389827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8388761193137124060926551 12583141789705686091389827)
                ·
                  refine ⟨18874712684558529137084741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12583141789705686091389827 18874712684558529137084741)
                  ·
                    refine ⟨3539008628354724213203389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18874712684558529137084741 3539008628354724213203389)
                    ·
                      refine ⟨1327128235633021579951271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3539008628354724213203389 1327128235633021579951271)
                      ·
                        rfl

theorem cell23_2584573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 1, 1, 4, 3].length) (baseStart_2584573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2584573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2584573 prefixEnd_2584573 := by exact prefixLift 2584573
  have htrace : WordTrace (prefixWord ++ tailWord_2584573) baseStart_2584573 baseEnd_2584573 := by
    simpa [prefixWord, tailWord_2584573, baseEnd_2584573] using wordTrace_append hprefix tailTrace_2584573
  have hstable : (prefixWord ++ tailWord_2584573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584573).length < 2 ^ (prefixWord ++ tailWord_2584573).sum := by decide
  have hdescent : baseEnd_2584573 < baseStart_2584573 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584590 : List Nat := [4, 1, 1, 2, 2, 1, 3, 2, 2, 2, 3]
def baseStart_2584590 : Nat := 118140960795 + 2584590 * 2 ^ 59
def prefixEnd_2584590 : Nat := 4983230072969 + 3 ^ 40 * 2584590 * 2
def baseEnd_2584590 : Nat := 1327136964804148013438693

theorem tailTrace_2584590 : CollatzResearch.WordTrace tailWord_2584590 prefixEnd_2584590 1327136964804148013438693 := by
  unfold tailWord_2584590
  simp only [CollatzResearch.WordTrace]
  refine ⟨11783467713309914709304903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62845161137652878449626149 11783467713309914709304903)
  ·
    refine ⟨17675201569964872063957355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11783467713309914709304903 17675201569964872063957355)
    ·
      refine ⟨26512802354947308095936033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17675201569964872063957355 26512802354947308095936033)
      ·
        refine ⟨19884601766210481071952025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26512802354947308095936033 19884601766210481071952025)
        ·
          refine ⟨14913451324657860803964019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19884601766210481071952025 14913451324657860803964019)
          ·
            refine ⟨22370176986986791205946029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14913451324657860803964019 22370176986986791205946029)
            ·
              refine ⟨8388816370120046702229761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22370176986986791205946029 8388816370120046702229761)
              ·
                refine ⟨6291612277590035026672321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8388816370120046702229761 6291612277590035026672321)
                ·
                  refine ⟨4718709208192526270004241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6291612277590035026672321 4718709208192526270004241)
                  ·
                    refine ⟨3539031906144394702503181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4718709208192526270004241 3539031906144394702503181)
                    ·
                      refine ⟨1327136964804148013438693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3539031906144394702503181 1327136964804148013438693)
                      ·
                        rfl

theorem cell23_2584590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 2, 2, 2, 3].length) (baseStart_2584590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2584590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2584590 prefixEnd_2584590 := by exact prefixLift 2584590
  have htrace : WordTrace (prefixWord ++ tailWord_2584590) baseStart_2584590 baseEnd_2584590 := by
    simpa [prefixWord, tailWord_2584590, baseEnd_2584590] using wordTrace_append hprefix tailTrace_2584590
  have hstable : (prefixWord ++ tailWord_2584590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584590).length < 2 ^ (prefixWord ++ tailWord_2584590).sum := by decide
  have hdescent : baseEnd_2584590 < baseStart_2584590 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584597 : List Nat := [1, 3, 2, 1, 5, 2, 1, 1, 3, 4]
def baseStart_2584597 : Nat := 118140960795 + 2584597 * 2 ^ 59
def prefixEnd_2584597 : Nat := 4983230072969 + 3 ^ 40 * 2584597 * 2
def baseEnd_2584597 : Nat := 442380186389576495350387

theorem tailTrace_2584597 : CollatzResearch.WordTrace tailWord_2584597 prefixEnd_2584597 442380186389576495350387 := by
  unfold tailWord_2584597
  simp only [CollatzResearch.WordTrace]
  refine ⟨94267997017453957869944045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62845331344969305246629363 94267997017453957869944045)
  ·
    refine ⟨35350498881545234201229017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94267997017453957869944045 35350498881545234201229017)
    ·
      refine ⟨26512874161158925650921763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35350498881545234201229017 26512874161158925650921763)
      ·
        refine ⟨39769311241738388476382645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26512874161158925650921763 39769311241738388476382645)
        ·
          refine ⟨3728372928912973919660873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39769311241738388476382645 3728372928912973919660873)
          ·
            refine ⟨2796279696684730439745655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3728372928912973919660873 2796279696684730439745655)
            ·
              refine ⟨4194419545027095659618483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2796279696684730439745655 4194419545027095659618483)
              ·
                refine ⟨6291629317540643489427725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4194419545027095659618483 6291629317540643489427725)
                ·
                  refine ⟨2359360994077741308535397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6291629317540643489427725 2359360994077741308535397)
                  ·
                    refine ⟨442380186389576495350387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2359360994077741308535397 442380186389576495350387)
                    ·
                      rfl

theorem cell23_2584597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 1, 3, 4].length) (baseStart_2584597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2584597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2584597 prefixEnd_2584597 := by exact prefixLift 2584597
  have htrace : WordTrace (prefixWord ++ tailWord_2584597) baseStart_2584597 baseEnd_2584597 := by
    simpa [prefixWord, tailWord_2584597, baseEnd_2584597] using wordTrace_append hprefix tailTrace_2584597
  have hstable : (prefixWord ++ tailWord_2584597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584597).length < 2 ^ (prefixWord ++ tailWord_2584597).sum := by decide
  have hdescent : baseEnd_2584597 < baseStart_2584597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584623 : List Nat := [1, 1, 2, 1, 2, 1, 1, 8, 1, 5]
def baseStart_2584623 : Nat := 118140960795 + 2584623 * 2 ^ 59
def prefixEnd_2584623 : Nat := 4983230072969 + 3 ^ 40 * 2584623 * 2
def baseEnd_2584623 : Nat := 442384636555248794775347

theorem tailTrace_2584623 : CollatzResearch.WordTrace tailWord_2584623 prefixEnd_2584623 442384636555248794775347 := by
  unfold tailWord_2584623
  simp only [CollatzResearch.WordTrace]
  refine ⟨94268945315359764310390523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62845963543573176206927015 94268945315359764310390523)
  ·
    refine ⟨141403417973039646465585785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94268945315359764310390523 141403417973039646465585785)
    ·
      refine ⟨106052563479779734849189339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141403417973039646465585785 106052563479779734849189339)
      ·
        refine ⟨159078845219669602273784009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106052563479779734849189339 159078845219669602273784009)
        ·
          refine ⟨119309133914752201705338007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159078845219669602273784009 119309133914752201705338007)
          ·
            refine ⟨178963700872128302558007011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119309133914752201705338007 178963700872128302558007011)
            ·
              refine ⟨268445551308192453837010517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 178963700872128302558007011 268445551308192453837010517)
              ·
                refine ⟨3145846304392880318402467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 268445551308192453837010517 3145846304392880318402467)
                ·
                  refine ⟨4718769456589320477603701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3145846304392880318402467 4718769456589320477603701)
                  ·
                    refine ⟨442384636555248794775347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4718769456589320477603701 442384636555248794775347)
                    ·
                      rfl

theorem cell23_2584623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 8, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 8, 1, 5].length) (baseStart_2584623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2584623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2584623 prefixEnd_2584623 := by exact prefixLift 2584623
  have htrace : WordTrace (prefixWord ++ tailWord_2584623) baseStart_2584623 baseEnd_2584623 := by
    simpa [prefixWord, tailWord_2584623, baseEnd_2584623] using wordTrace_append hprefix tailTrace_2584623
  have hstable : (prefixWord ++ tailWord_2584623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584623).length < 2 ^ (prefixWord ++ tailWord_2584623).sum := by decide
  have hdescent : baseEnd_2584623 < baseStart_2584623 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584654 : List Nat := [4, 1, 1, 1, 1, 5, 1, 4, 1, 1, 3]
def baseStart_2584654 : Nat := 118140960795 + 2584654 * 2 ^ 59
def prefixEnd_2584654 : Nat := 4983230072969 + 3 ^ 40 * 2584654 * 2
def baseEnd_2584654 : Nat := 1327169827566035763038399

theorem tailTrace_2584654 : CollatzResearch.WordTrace tailWord_2584654 prefixEnd_2584654 1327169827566035763038399 := by
  unfold tailWord_2584654
  simp only [CollatzResearch.WordTrace]
  refine ⟨11783759497280932075596127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62846717318831637736512677 11783759497280932075596127)
  ·
    refine ⟨17675639245921398113394191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11783759497280932075596127 17675639245921398113394191)
    ·
      refine ⟨26513458868882097170091287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17675639245921398113394191 26513458868882097170091287)
      ·
        refine ⟨39770188303323145755136931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26513458868882097170091287 39770188303323145755136931)
        ·
          refine ⟨59655282454984718632705397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39770188303323145755136931 59655282454984718632705397)
          ·
            refine ⟨5592682730154817371816131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 59655282454984718632705397 5592682730154817371816131)
            ·
              refine ⟨8389024095232226057724197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5592682730154817371816131 8389024095232226057724197)
              ·
                refine ⟨1572942017856042385823287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8389024095232226057724197 1572942017856042385823287)
                ·
                  refine ⟨2359413026784063578734931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1572942017856042385823287 2359413026784063578734931)
                  ·
                    refine ⟨3539119540176095368102397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2359413026784063578734931 3539119540176095368102397)
                    ·
                      refine ⟨1327169827566035763038399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3539119540176095368102397 1327169827566035763038399)
                      ·
                        rfl

theorem cell23_2584654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 4, 1, 1, 3].length) (baseStart_2584654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2584654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2584654 prefixEnd_2584654 := by exact prefixLift 2584654
  have htrace : WordTrace (prefixWord ++ tailWord_2584654) baseStart_2584654 baseEnd_2584654 := by
    simpa [prefixWord, tailWord_2584654, baseEnd_2584654] using wordTrace_append hprefix tailTrace_2584654
  have hstable : (prefixWord ++ tailWord_2584654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584654).length < 2 ^ (prefixWord ++ tailWord_2584654).sum := by decide
  have hdescent : baseEnd_2584654 < baseStart_2584654 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584660 : List Nat := [2, 4, 1, 1, 1, 1, 1, 2, 2, 6, 2]
def baseStart_2584660 : Nat := 118140960795 + 2584660 * 2 ^ 59
def prefixEnd_2584660 : Nat := 4983230072969 + 3 ^ 40 * 2584660 * 2
def baseEnd_2584660 : Nat := 1327172908449962739563371

theorem tailTrace_2584660 : CollatzResearch.WordTrace tailWord_2584660 prefixEnd_2584660 1327172908449962739563371 := by
  unfold tailWord_2584660
  simp only [CollatzResearch.WordTrace]
  refine ⟨47135147408112859814743717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62846863210817146419658289 47135147408112859814743717)
  ·
    refine ⟨8837840139021161215264447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47135147408112859814743717 8837840139021161215264447)
    ·
      refine ⟨13256760208531741822896671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8837840139021161215264447 13256760208531741822896671)
      ·
        refine ⟨19885140312797612734345007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13256760208531741822896671 19885140312797612734345007)
        ·
          refine ⟨29827710469196419101517511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19885140312797612734345007 29827710469196419101517511)
          ·
            refine ⟨44741565703794628652276267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29827710469196419101517511 44741565703794628652276267)
            ·
              refine ⟨67112348555691942978414401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44741565703794628652276267 67112348555691942978414401)
              ·
                refine ⟨50334261416768957233810801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67112348555691942978414401 50334261416768957233810801)
                ·
                  refine ⟨37750696062576717925358101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50334261416768957233810801 37750696062576717925358101)
                  ·
                    refine ⟨1769563877933283652751161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 37750696062576717925358101 1769563877933283652751161)
                    ·
                      refine ⟨1327172908449962739563371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1769563877933283652751161 1327172908449962739563371)
                      ·
                        rfl

theorem cell23_2584660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 2, 6, 2].length) (baseStart_2584660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2584660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2584660 prefixEnd_2584660 := by exact prefixLift 2584660
  have htrace : WordTrace (prefixWord ++ tailWord_2584660) baseStart_2584660 baseEnd_2584660 := by
    simpa [prefixWord, tailWord_2584660, baseEnd_2584660] using wordTrace_append hprefix tailTrace_2584660
  have hstable : (prefixWord ++ tailWord_2584660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584660).length < 2 ^ (prefixWord ++ tailWord_2584660).sum := by decide
  have hdescent : baseEnd_2584660 < baseStart_2584660 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584663 : List Nat := [1, 1, 3, 2, 2, 1, 2, 4, 1, 1, 5]
def baseStart_2584663 : Nat := 118140960795 + 2584663 * 2 ^ 59
def prefixEnd_2584663 : Nat := 4983230072969 + 3 ^ 40 * 2584663 * 2
def baseEnd_2584663 : Nat := 1327174448891926227825857

theorem tailTrace_2584663 : CollatzResearch.WordTrace tailWord_2584663 prefixEnd_2584663 1327174448891926227825857 := by
  unfold tailWord_2584663
  simp only [CollatzResearch.WordTrace]
  refine ⟨94270404235214851141846643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62846936156809900761231095 94270404235214851141846643)
  ·
    refine ⟨141405606352822276712769965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94270404235214851141846643 141405606352822276712769965)
    ·
      refine ⟨53027102382308353767288737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141405606352822276712769965 53027102382308353767288737)
      ·
        refine ⟨39770326786731265325466553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53027102382308353767288737 39770326786731265325466553)
        ·
          refine ⟨29827745090048448994099915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39770326786731265325466553 29827745090048448994099915)
          ·
            refine ⟨44741617635072673491149873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29827745090048448994099915 44741617635072673491149873)
            ·
              refine ⟨33556213226304505118362405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44741617635072673491149873 33556213226304505118362405)
              ·
                refine ⟨6291789979932094709692951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33556213226304505118362405 6291789979932094709692951)
                ·
                  refine ⟨9437684969898142064539427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6291789979932094709692951 9437684969898142064539427)
                  ·
                    refine ⟨14156527454847213096809141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9437684969898142064539427 14156527454847213096809141)
                    ·
                      refine ⟨1327174448891926227825857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14156527454847213096809141 1327174448891926227825857)
                      ·
                        rfl

theorem cell23_2584663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 4, 1, 1, 5].length) (baseStart_2584663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2584663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2584663 prefixEnd_2584663 := by exact prefixLift 2584663
  have htrace : WordTrace (prefixWord ++ tailWord_2584663) baseStart_2584663 baseEnd_2584663 := by
    simpa [prefixWord, tailWord_2584663, baseEnd_2584663] using wordTrace_append hprefix tailTrace_2584663
  have hstable : (prefixWord ++ tailWord_2584663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584663).length < 2 ^ (prefixWord ++ tailWord_2584663).sum := by decide
  have hdescent : baseEnd_2584663 < baseStart_2584663 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584677 : List Nat := [1, 3, 1, 3, 2, 2, 1, 1, 5, 2, 2]
def baseStart_2584677 : Nat := 118140960795 + 2584677 * 2 ^ 59
def prefixEnd_2584677 : Nat := 4983230072969 + 3 ^ 40 * 2584677 * 2
def baseEnd_2584677 : Nat := 1327181637621089173050793

theorem tailTrace_2584677 : CollatzResearch.WordTrace tailWord_2584677 prefixEnd_2584677 1327181637621089173050793 := by
  unfold tailWord_2584677
  simp only [CollatzResearch.WordTrace]
  refine ⟨94270914857164131532856285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62847276571442754355237523 94270914857164131532856285)
  ·
    refine ⟨35351593071436549324821107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94270914857164131532856285 35351593071436549324821107)
    ·
      refine ⟨53027389607154823987231661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35351593071436549324821107 53027389607154823987231661)
      ·
        refine ⟨19885271102683058995211873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53027389607154823987231661 19885271102683058995211873)
        ·
          refine ⟨14913953327012294246408905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19885271102683058995211873 14913953327012294246408905)
          ·
            refine ⟨11185464995259220684806679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14913953327012294246408905 11185464995259220684806679)
            ·
              refine ⟨16778197492888831027210019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11185464995259220684806679 16778197492888831027210019)
              ·
                refine ⟨25167296239333246540815029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16778197492888831027210019 25167296239333246540815029)
                ·
                  refine ⟨2359434022437491863201409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25167296239333246540815029 2359434022437491863201409)
                  ·
                    refine ⟨1769575516828118897401057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2359434022437491863201409 1769575516828118897401057)
                    ·
                      refine ⟨1327181637621089173050793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1769575516828118897401057 1327181637621089173050793)
                      ·
                        rfl

theorem cell23_2584677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 5, 2, 2].length) (baseStart_2584677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2584677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2584677 prefixEnd_2584677 := by exact prefixLift 2584677
  have htrace : WordTrace (prefixWord ++ tailWord_2584677) baseStart_2584677 baseEnd_2584677 := by
    simpa [prefixWord, tailWord_2584677, baseEnd_2584677] using wordTrace_append hprefix tailTrace_2584677
  have hstable : (prefixWord ++ tailWord_2584677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584677).length < 2 ^ (prefixWord ++ tailWord_2584677).sum := by decide
  have hdescent : baseEnd_2584677 < baseStart_2584677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584690 : List Nat := [3, 2, 1, 2, 2, 2, 2, 2, 1, 2, 4]
def baseStart_2584690 : Nat := 118140960795 + 2584690 * 2 ^ 59
def prefixEnd_2584690 : Nat := 4983230072969 + 3 ^ 40 * 2584690 * 2
def baseEnd_2584690 : Nat := 1327188312869597622188233

theorem tailTrace_2584690 : CollatzResearch.WordTrace tailWord_2584690 prefixEnd_2584690 1327188312869597622188233 := by
  unfold tailWord_2584690
  simp only [CollatzResearch.WordTrace]
  refine ⟨23567847251529258688269881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62847592670744689835386349 23567847251529258688269881)
  ·
    refine ⟨17675885438646944016202411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23567847251529258688269881 17675885438646944016202411)
    ·
      refine ⟨26513828157970416024303617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17675885438646944016202411 26513828157970416024303617)
      ·
        refine ⟨19885371118477812018227713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26513828157970416024303617 19885371118477812018227713)
        ·
          refine ⟨14914028338858359013670785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19885371118477812018227713 14914028338858359013670785)
          ·
            refine ⟨11185521254143769260253089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14914028338858359013670785 11185521254143769260253089)
            ·
              refine ⟨8389140940607826945189817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11185521254143769260253089 8389140940607826945189817)
              ·
                refine ⟨6291855705455870208892363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8389140940607826945189817 6291855705455870208892363)
                ·
                  refine ⟨9437783558183805313338545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6291855705455870208892363 9437783558183805313338545)
                  ·
                    refine ⟨7078337668637853985003909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9437783558183805313338545 7078337668637853985003909)
                    ·
                      refine ⟨1327188312869597622188233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7078337668637853985003909 1327188312869597622188233)
                      ·
                        rfl

theorem cell23_2584690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 2, 1, 2, 4].length) (baseStart_2584690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2584690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2584690 prefixEnd_2584690 := by exact prefixLift 2584690
  have htrace : WordTrace (prefixWord ++ tailWord_2584690) baseStart_2584690 baseEnd_2584690 := by
    simpa [prefixWord, tailWord_2584690, baseEnd_2584690] using wordTrace_append hprefix tailTrace_2584690
  have hstable : (prefixWord ++ tailWord_2584690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584690).length < 2 ^ (prefixWord ++ tailWord_2584690).sum := by decide
  have hdescent : baseEnd_2584690 < baseStart_2584690 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584694 : List Nat := [5, 1, 1, 2, 1, 2, 4, 1, 1, 1, 4]
def baseStart_2584694 : Nat := 118140960795 + 2584694 * 2 ^ 59
def prefixEnd_2584694 : Nat := 4983230072969 + 3 ^ 40 * 2584694 * 2
def baseEnd_2584694 : Nat := 1327190366792215606538215

theorem tailTrace_2584694 : CollatzResearch.WordTrace tailWord_2584694 prefixEnd_2584694 1327190366792215606538215 := by
  unfold tailWord_2584694
  simp only [CollatzResearch.WordTrace]
  refine ⟨5891970931131408964764071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 62847689932068362290816757 5891970931131408964764071)
  ·
    refine ⟨8837956396697113447146107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5891970931131408964764071 8837956396697113447146107)
    ·
      refine ⟨13256934595045670170719161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8837956396697113447146107 13256934595045670170719161)
      ·
        refine ⟨9942700946284252628039371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13256934595045670170719161 9942700946284252628039371)
        ·
          refine ⟨14914051419426378942059057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9942700946284252628039371 14914051419426378942059057)
          ·
            refine ⟨11185538564569784206544293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14914051419426378942059057 11185538564569784206544293)
            ·
              refine ⟨2097288480856834538727055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11185538564569784206544293 2097288480856834538727055)
              ·
                refine ⟨3145932721285251808090583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2097288480856834538727055 3145932721285251808090583)
                ·
                  refine ⟨4718899081927877712135875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3145932721285251808090583 4718899081927877712135875)
                  ·
                    refine ⟨7078348622891816568203813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4718899081927877712135875 7078348622891816568203813)
                    ·
                      refine ⟨1327190366792215606538215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7078348622891816568203813 1327190366792215606538215)
                      ·
                        rfl

theorem cell23_2584694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 4, 1, 1, 1, 4].length) (baseStart_2584694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2584694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2584694 prefixEnd_2584694 := by exact prefixLift 2584694
  have htrace : WordTrace (prefixWord ++ tailWord_2584694) baseStart_2584694 baseEnd_2584694 := by
    simpa [prefixWord, tailWord_2584694, baseEnd_2584694] using wordTrace_append hprefix tailTrace_2584694
  have hstable : (prefixWord ++ tailWord_2584694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584694).length < 2 ^ (prefixWord ++ tailWord_2584694).sum := by decide
  have hdescent : baseEnd_2584694 < baseStart_2584694 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584697 : List Nat := [1, 2, 1, 3, 4, 2, 1, 3, 1, 2, 3]
def baseStart_2584697 : Nat := 118140960795 + 2584697 * 2 ^ 59
def prefixEnd_2584697 : Nat := 4983230072969 + 3 ^ 40 * 2584697 * 2
def baseEnd_2584697 : Nat := 1327191907234179094800701

theorem tailTrace_2584697 : CollatzResearch.WordTrace tailWord_2584697 prefixEnd_2584697 1327191907234179094800701 := by
  unfold tailWord_2584697
  simp only [CollatzResearch.WordTrace]
  refine ⟨94271644317091674948584345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62847762878061116632389563 94271644317091674948584345)
  ·
    refine ⟨70703733237818756211438259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94271644317091674948584345 70703733237818756211438259)
    ·
      refine ⟨106055599856728134317157389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70703733237818756211438259 106055599856728134317157389)
      ·
        refine ⟨39770849946273050368934021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106055599856728134317157389 39770849946273050368934021)
        ·
          refine ⟨7457034364926196944175129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39770849946273050368934021 7457034364926196944175129)
          ·
            refine ⟨5592775773694647708131347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7457034364926196944175129 5592775773694647708131347)
            ·
              refine ⟨8389163660541971562197021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5592775773694647708131347 8389163660541971562197021)
              ·
                refine ⟨3145936372703239335823883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8389163660541971562197021 3145936372703239335823883)
                ·
                  refine ⟨4718904559054859003735825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3145936372703239335823883 4718904559054859003735825)
                  ·
                    refine ⟨3539178419291144252801869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4718904559054859003735825 3539178419291144252801869)
                    ·
                      refine ⟨1327191907234179094800701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3539178419291144252801869 1327191907234179094800701)
                      ·
                        rfl

theorem cell23_2584697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 3, 1, 2, 3].length) (baseStart_2584697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2584697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2584697 prefixEnd_2584697 := by exact prefixLift 2584697
  have htrace : WordTrace (prefixWord ++ tailWord_2584697) baseStart_2584697 baseEnd_2584697 := by
    simpa [prefixWord, tailWord_2584697, baseEnd_2584697] using wordTrace_append hprefix tailTrace_2584697
  have hstable : (prefixWord ++ tailWord_2584697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584697).length < 2 ^ (prefixWord ++ tailWord_2584697).sum := by decide
  have hdescent : baseEnd_2584697 < baseStart_2584697 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584734 : List Nat := [4, 3, 1, 1, 3, 2, 2, 7]
def baseStart_2584734 : Nat := 118140960795 + 2584734 * 2 ^ 59
def prefixEnd_2584734 : Nat := 4983230072969 + 3 ^ 40 * 2584734 * 2
def baseEnd_2584734 : Nat := 49155959482162794445853

theorem tailTrace_2584734 : CollatzResearch.WordTrace tailWord_2584734 prefixEnd_2584734 49155959482162794445853 := by
  unfold tailWord_2584734
  simp only [CollatzResearch.WordTrace]
  refine ⟨11784124227244703783460157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62848662545305086845120837 11784124227244703783460157)
  ·
    refine ⟨4419046585216763918797559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11784124227244703783460157 4419046585216763918797559)
    ·
      refine ⟨6628569877825145878196339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4419046585216763918797559 6628569877825145878196339)
      ·
        refine ⟨9942854816737718817294509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6628569877825145878196339 9942854816737718817294509)
        ·
          refine ⟨3728570556276644556485441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9942854816737718817294509 3728570556276644556485441)
          ·
            refine ⟨2796427917207483417364081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3728570556276644556485441 2796427917207483417364081)
            ·
              refine ⟨2097320937905612563023061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2796427917207483417364081 2097320937905612563023061)
              ·
                refine ⟨49155959482162794445853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2097320937905612563023061 49155959482162794445853)
                ·
                  rfl

theorem cell23_2584734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 2, 7].length) (baseStart_2584734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2584734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2584734 prefixEnd_2584734 := by exact prefixLift 2584734
  have htrace : WordTrace (prefixWord ++ tailWord_2584734) baseStart_2584734 baseEnd_2584734 := by
    simpa [prefixWord, tailWord_2584734, baseEnd_2584734] using wordTrace_append hprefix tailTrace_2584734
  have hstable : (prefixWord ++ tailWord_2584734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584734).length < 2 ^ (prefixWord ++ tailWord_2584734).sum := by decide
  have hdescent : baseEnd_2584734 < baseStart_2584734 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584823 : List Nat := [1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 8]
def baseStart_2584823 : Nat := 118140960795 + 2584823 * 2 ^ 59
def prefixEnd_2584823 : Nat := 4983230072969 + 3 ^ 40 * 2584823 * 2
def baseEnd_2584823 : Nat := 1327256605796645601825121

theorem tailTrace_2584823 : CollatzResearch.WordTrace tailWord_2584823 prefixEnd_2584823 1327256605796645601825121 := by
  unfold tailWord_2584823
  simp only [CollatzResearch.WordTrace]
  refine ⟨94276239914635198467671123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62850826609756798978447415 94276239914635198467671123)
  ·
    refine ⟨141414359871952797701506685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94276239914635198467671123 141414359871952797701506685)
    ·
      refine ⟨53030384951982299138065007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141414359871952797701506685 53030384951982299138065007)
      ·
        refine ⟨79545577427973448707097511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53030384951982299138065007 79545577427973448707097511)
        ·
          refine ⟨119318366141960173060646267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79545577427973448707097511 119318366141960173060646267)
          ·
            refine ⟨178977549212940259590969401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119318366141960173060646267 178977549212940259590969401)
            ·
              refine ⟨134233161909705194693227051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 178977549212940259590969401 134233161909705194693227051)
              ·
                refine ⟨201349742864557792039840577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 134233161909705194693227051 201349742864557792039840577)
                ·
                  refine ⟨151012307148418344029880433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 201349742864557792039840577 151012307148418344029880433)
                  ·
                    refine ⟨113259230361313758022410325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 151012307148418344029880433 113259230361313758022410325)
                    ·
                      refine ⟨1327256605796645601825121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 113259230361313758022410325 1327256605796645601825121)
                      ·
                        rfl

theorem cell23_2584823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 8].length) (baseStart_2584823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2584823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2584823 prefixEnd_2584823 := by exact prefixLift 2584823
  have htrace : WordTrace (prefixWord ++ tailWord_2584823) baseStart_2584823 baseEnd_2584823 := by
    simpa [prefixWord, tailWord_2584823, baseEnd_2584823] using wordTrace_append hprefix tailTrace_2584823
  have hstable : (prefixWord ++ tailWord_2584823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584823).length < 2 ^ (prefixWord ++ tailWord_2584823).sum := by decide
  have hdescent : baseEnd_2584823 < baseStart_2584823 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584834 : List Nat := [3, 4, 1, 1, 2, 2, 1, 1, 2, 3, 3]
def baseStart_2584834 : Nat := 118140960795 + 2584834 * 2 ^ 59
def prefixEnd_2584834 : Nat := 4983230072969 + 3 ^ 40 * 2584834 * 2
def baseEnd_2584834 : Nat := 1327262254083845058787571

theorem tailTrace_2584834 : CollatzResearch.WordTrace tailWord_2584834 prefixEnd_2584834 1327262254083845058787571 := by
  unfold tailWord_2584834
  simp only [CollatzResearch.WordTrace]
  refine ⟨23569160279398836836580389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62851094078396898230881037 23569160279398836836580389)
  ·
    refine ⟨4419217552387281906858823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23569160279398836836580389 4419217552387281906858823)
    ·
      refine ⟨6628826328580922860288235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4419217552387281906858823 6628826328580922860288235)
      ·
        refine ⟨9943239492871384290432353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6628826328580922860288235 9943239492871384290432353)
        ·
          refine ⟨7457429619653538217824265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9943239492871384290432353 7457429619653538217824265)
          ·
            refine ⟨5593072214740153663368199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7457429619653538217824265 5593072214740153663368199)
            ·
              refine ⟨8389608322110230495052299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5593072214740153663368199 8389608322110230495052299)
              ·
                refine ⟨12584412483165345742578449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8389608322110230495052299 12584412483165345742578449)
                ·
                  refine ⟨9438309362374009306933837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12584412483165345742578449 9438309362374009306933837)
                  ·
                    refine ⟨3539366010890253490100189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9438309362374009306933837 3539366010890253490100189)
                    ·
                      refine ⟨1327262254083845058787571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3539366010890253490100189 1327262254083845058787571)
                      ·
                        rfl

theorem cell23_2584834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_2584834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2584834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2584834 prefixEnd_2584834 := by exact prefixLift 2584834
  have htrace : WordTrace (prefixWord ++ tailWord_2584834) baseStart_2584834 baseEnd_2584834 := by
    simpa [prefixWord, tailWord_2584834, baseEnd_2584834] using wordTrace_append hprefix tailTrace_2584834
  have hstable : (prefixWord ++ tailWord_2584834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584834).length < 2 ^ (prefixWord ++ tailWord_2584834).sum := by decide
  have hdescent : baseEnd_2584834 < baseStart_2584834 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584880 : List Nat := [2, 1, 1, 1, 2, 2, 2, 6, 6]
def baseStart_2584880 : Nat := 118140960795 + 2584880 * 2 ^ 59
def prefixEnd_2584880 : Nat := 4983230072969 + 3 ^ 40 * 2584880 * 2
def baseEnd_2584880 : Nat := 147476208243772430979151

theorem tailTrace_2584880 : CollatzResearch.WordTrace tailWord_2584880 prefixEnd_2584880 147476208243772430979151 := by
  unfold tailWord_2584880
  simp only [CollatzResearch.WordTrace]
  refine ⟨47139159437714348601248047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62852212583619131468330729 47139159437714348601248047)
  ·
    refine ⟨70708739156571522901872071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47139159437714348601248047 70708739156571522901872071)
    ·
      refine ⟨106063108734857284352808107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70708739156571522901872071 106063108734857284352808107)
      ·
        refine ⟨159094663102285926529212161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106063108734857284352808107 159094663102285926529212161)
        ·
          refine ⟨119320997326714444896909121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159094663102285926529212161 119320997326714444896909121)
          ·
            refine ⟨89490747995035833672681841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119320997326714444896909121 89490747995035833672681841)
            ·
              refine ⟨67118060996276875254511381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89490747995035833672681841 67118060996276875254511381)
              ·
                refine ⟨3146159109200478527555221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 67118060996276875254511381 3146159109200478527555221)
                ·
                  refine ⟨147476208243772430979151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3146159109200478527555221 147476208243772430979151)
                  ·
                    rfl

theorem cell23_2584880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 6, 6].length) (baseStart_2584880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2584880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2584880 prefixEnd_2584880 := by exact prefixLift 2584880
  have htrace : WordTrace (prefixWord ++ tailWord_2584880) baseStart_2584880 baseEnd_2584880 := by
    simpa [prefixWord, tailWord_2584880, baseEnd_2584880] using wordTrace_append hprefix tailTrace_2584880
  have hstable : (prefixWord ++ tailWord_2584880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584880).length < 2 ^ (prefixWord ++ tailWord_2584880).sum := by decide
  have hdescent : baseEnd_2584880 < baseStart_2584880 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584884 : List Nat := [2, 5, 1, 1, 1, 2, 1, 3, 3, 4]
def baseStart_2584884 : Nat := 118140960795 + 2584884 * 2 ^ 59
def prefixEnd_2584884 : Nat := 4983230072969 + 3 ^ 40 * 2584884 * 2
def baseEnd_2584884 : Nat := 442429309372189954387447

theorem tailTrace_2584884 : CollatzResearch.WordTrace tailWord_2584884 prefixEnd_2584884 442429309372189954387447 := by
  unfold tailWord_2584884
  simp only [CollatzResearch.WordTrace]
  refine ⟨47139232383707102942820853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62852309844942803923761137 47139232383707102942820853)
  ·
    refine ⟨4419303035972540900889455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 47139232383707102942820853 4419303035972540900889455)
    ·
      refine ⟨6628954553958811351334183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4419303035972540900889455 6628954553958811351334183)
      ·
        refine ⟨9943431830938217027001275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6628954553958811351334183 9943431830938217027001275)
        ·
          refine ⟨14915147746407325540501913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9943431830938217027001275 14915147746407325540501913)
          ·
            refine ⟨11186360809805494155376435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14915147746407325540501913 11186360809805494155376435)
            ·
              refine ⟨16779541214708241233064653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11186360809805494155376435 16779541214708241233064653)
              ·
                refine ⟨6292327955515590462399245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16779541214708241233064653 6292327955515590462399245)
                ·
                  refine ⟨2359622983318346423399717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6292327955515590462399245 2359622983318346423399717)
                  ·
                    refine ⟨442429309372189954387447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2359622983318346423399717 442429309372189954387447)
                    ·
                      rfl

theorem cell23_2584884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_2584884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2584884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2584884 prefixEnd_2584884 := by exact prefixLift 2584884
  have htrace : WordTrace (prefixWord ++ tailWord_2584884) baseStart_2584884 baseEnd_2584884 := by
    simpa [prefixWord, tailWord_2584884, baseEnd_2584884] using wordTrace_append hprefix tailTrace_2584884
  have hstable : (prefixWord ++ tailWord_2584884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584884).length < 2 ^ (prefixWord ++ tailWord_2584884).sum := by decide
  have hdescent : baseEnd_2584884 < baseStart_2584884 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584907 : List Nat := [1, 1, 1, 1, 3, 1, 1, 5, 5, 1, 3]
def baseStart_2584907 : Nat := 118140960795 + 2584907 * 2 ^ 59
def prefixEnd_2584907 : Nat := 4983230072969 + 3 ^ 40 * 2584907 * 2
def baseEnd_2584907 : Nat := 1327299738171623273174735

theorem tailTrace_2584907 : CollatzResearch.WordTrace tailWord_2584907 prefixEnd_2584907 1327299738171623273174735 := by
  unfold tailWord_2584907
  simp only [CollatzResearch.WordTrace]
  refine ⟨94279303646330880813728975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62852869097553920542485983 94279303646330880813728975)
  ·
    refine ⟨141418955469496321220593463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94279303646330880813728975 141418955469496321220593463)
    ·
      refine ⟨212128433204244481830890195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141418955469496321220593463 212128433204244481830890195)
      ·
        refine ⟨318192649806366722746335293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212128433204244481830890195 318192649806366722746335293)
        ·
          refine ⟨119322243677387521029875735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 318192649806366722746335293 119322243677387521029875735)
          ·
            refine ⟨178983365516081281544813603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119322243677387521029875735 178983365516081281544813603)
            ·
              refine ⟨268475048274121922317220405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 178983365516081281544813603 268475048274121922317220405)
              ·
                refine ⟨25169535775698930217239413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 268475048274121922317220405 25169535775698930217239413)
                ·
                  refine ⟨2359643978971774707866195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25169535775698930217239413 2359643978971774707866195)
                  ·
                    refine ⟨3539465968457662061799293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2359643978971774707866195 3539465968457662061799293)
                    ·
                      refine ⟨1327299738171623273174735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3539465968457662061799293 1327299738171623273174735)
                      ·
                        rfl

theorem cell23_2584907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 5, 1, 3].length) (baseStart_2584907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2584907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2584907 prefixEnd_2584907 := by exact prefixLift 2584907
  have htrace : WordTrace (prefixWord ++ tailWord_2584907) baseStart_2584907 baseEnd_2584907 := by
    simpa [prefixWord, tailWord_2584907, baseEnd_2584907] using wordTrace_append hprefix tailTrace_2584907
  have hstable : (prefixWord ++ tailWord_2584907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584907).length < 2 ^ (prefixWord ++ tailWord_2584907).sum := by decide
  have hdescent : baseEnd_2584907 < baseStart_2584907 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584927 : List Nat := [1, 1, 2, 3, 1, 2, 4, 3, 1, 5]
def baseStart_2584927 : Nat := 118140960795 + 2584927 * 2 ^ 59
def prefixEnd_2584927 : Nat := 4983230072969 + 3 ^ 40 * 2584927 * 2
def baseEnd_2584927 : Nat := 442436669261571064974881

theorem tailTrace_2584927 : CollatzResearch.WordTrace tailWord_2584927 prefixEnd_2584927 442436669261571064974881 := by
  unfold tailWord_2584927
  simp only [CollatzResearch.WordTrace]
  refine ⟨94280033106258424229457035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62853355404172282819638023 94280033106258424229457035)
  ·
    refine ⟨141420049659387636344185553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94280033106258424229457035 141420049659387636344185553)
    ·
      refine ⟨106065037244540727258139165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141420049659387636344185553 106065037244540727258139165)
      ·
        refine ⟨39774388966702772721802187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106065037244540727258139165 39774388966702772721802187)
        ·
          refine ⟨59661583450054159082703281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39774388966702772721802187 59661583450054159082703281)
          ·
            refine ⟨44746187587540619312027461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59661583450054159082703281 44746187587540619312027461)
            ·
              refine ⟨8389910172663866121005149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44746187587540619312027461 8389910172663866121005149)
              ·
                refine ⟨3146216314748949795376931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8389910172663866121005149 3146216314748949795376931)
                ·
                  refine ⟨4719324472123424693065397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3146216314748949795376931 4719324472123424693065397)
                  ·
                    refine ⟨442436669261571064974881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4719324472123424693065397 442436669261571064974881)
                    ·
                      rfl

theorem cell23_2584927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 3, 1, 5].length) (baseStart_2584927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2584927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2584927 prefixEnd_2584927 := by exact prefixLift 2584927
  have htrace : WordTrace (prefixWord ++ tailWord_2584927) baseStart_2584927 baseEnd_2584927 := by
    simpa [prefixWord, tailWord_2584927, baseEnd_2584927] using wordTrace_append hprefix tailTrace_2584927
  have hstable : (prefixWord ++ tailWord_2584927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584927).length < 2 ^ (prefixWord ++ tailWord_2584927).sum := by decide
  have hdescent : baseEnd_2584927 < baseStart_2584927 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584961 : List Nat := [1, 2, 4, 3, 1, 3, 1, 2, 1, 5]
def baseStart_2584961 : Nat := 118140960795 + 2584961 * 2 ^ 59
def prefixEnd_2584961 : Nat := 4983230072969 + 3 ^ 40 * 2584961 * 2
def baseEnd_2584961 : Nat := 442442488708988687299829

theorem tailTrace_2584961 : CollatzResearch.WordTrace tailWord_2584961 prefixEnd_2584961 442442488708988687299829 := by
  unfold tailWord_2584961
  simp only [CollatzResearch.WordTrace]
  refine ⟨94281273188135248036194737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62854182125423498690796491 94281273188135248036194737)
  ·
    refine ⟨70710954891101436027146053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94281273188135248036194737 70710954891101436027146053)
    ·
      refine ⟨13258304042081519255089885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70710954891101436027146053 13258304042081519255089885)
      ·
        refine ⟨4971864015780569720658707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13258304042081519255089885 4971864015780569720658707)
        ·
          refine ⟨7457796023670854580988061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4971864015780569720658707 7457796023670854580988061)
          ·
            refine ⟨2796673508876570467870523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7457796023670854580988061 2796673508876570467870523)
            ·
              refine ⟨4195010263314855701805785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2796673508876570467870523 4195010263314855701805785)
              ·
                refine ⟨3146257697486141776354339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4195010263314855701805785 3146257697486141776354339)
                ·
                  refine ⟨4719386546229212664531509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3146257697486141776354339 4719386546229212664531509)
                  ·
                    refine ⟨442442488708988687299829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4719386546229212664531509 442442488708988687299829)
                    ·
                      rfl

theorem cell23_2584961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 2, 1, 5].length) (baseStart_2584961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2584961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2584961 prefixEnd_2584961 := by exact prefixLift 2584961
  have htrace : WordTrace (prefixWord ++ tailWord_2584961) baseStart_2584961 baseEnd_2584961 := by
    simpa [prefixWord, tailWord_2584961, baseEnd_2584961] using wordTrace_append hprefix tailTrace_2584961
  have hstable : (prefixWord ++ tailWord_2584961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584961).length < 2 ^ (prefixWord ++ tailWord_2584961).sum := by decide
  have hdescent : baseEnd_2584961 < baseStart_2584961 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584974 : List Nat := [4, 1, 1, 4, 1, 2, 1, 2, 1, 6]
def baseStart_2584974 : Nat := 118140960795 + 2584974 * 2 ^ 59
def prefixEnd_2584974 : Nat := 4983230072969 + 3 ^ 40 * 2584974 * 2
def baseEnd_2584974 : Nat := 442444713791824837012309

theorem tailTrace_2584974 : CollatzResearch.WordTrace tailWord_2584974 prefixEnd_2584974 442444713791824837012309 := by
  unfold tailWord_2584974
  simp only [CollatzResearch.WordTrace]
  refine ⟨11785218417136018907052247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62854498224725434170945317 11785218417136018907052247)
  ·
    refine ⟨17677827625704028360578371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11785218417136018907052247 17677827625704028360578371)
    ·
      refine ⟨26516741438556042540867557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17677827625704028360578371 26516741438556042540867557)
      ·
        refine ⟨4971889019729257976412667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26516741438556042540867557 4971889019729257976412667)
        ·
          refine ⟨7457833529593886964619001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4971889019729257976412667 7457833529593886964619001)
          ·
            refine ⟨5593375147195415223464251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7457833529593886964619001 5593375147195415223464251)
            ·
              refine ⟨8390062720793122835196377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5593375147195415223464251 8390062720793122835196377)
              ·
                refine ⟨6292547040594842126397283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8390062720793122835196377 6292547040594842126397283)
                ·
                  refine ⟨9438820560892263189595925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6292547040594842126397283 9438820560892263189595925)
                  ·
                    refine ⟨442444713791824837012309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9438820560892263189595925 442444713791824837012309)
                    ·
                      rfl

theorem cell23_2584974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 2, 1, 6].length) (baseStart_2584974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2584974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2584974 prefixEnd_2584974 := by exact prefixLift 2584974
  have htrace : WordTrace (prefixWord ++ tailWord_2584974) baseStart_2584974 baseEnd_2584974 := by
    simpa [prefixWord, tailWord_2584974, baseEnd_2584974] using wordTrace_append hprefix tailTrace_2584974
  have hstable : (prefixWord ++ tailWord_2584974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584974).length < 2 ^ (prefixWord ++ tailWord_2584974).sum := by decide
  have hdescent : baseEnd_2584974 < baseStart_2584974 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584984 : List Nat := [2, 1, 2, 5, 1, 1, 3, 1, 1, 1, 5]
def baseStart_2584984 : Nat := 118140960795 + 2584984 * 2 ^ 59
def prefixEnd_2584984 : Nat := 4983230072969 + 3 ^ 40 * 2584984 * 2
def baseEnd_2584984 : Nat := 1327339276182019471911881

theorem tailTrace_2584984 : CollatzResearch.WordTrace tailWord_2584984 prefixEnd_2584984 1327339276182019471911881 := by
  unfold tailWord_2584984
  simp only [CollatzResearch.WordTrace]
  refine ⟨47141056033525961482141003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62854741378034615309521337 47141056033525961482141003)
  ·
    refine ⟨70711584050288942223211505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47141056033525961482141003 70711584050288942223211505)
    ·
      refine ⟨53033688037716706667408629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70711584050288942223211505 53033688037716706667408629)
      ·
        refine ⟨4971908253535941250069559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 53033688037716706667408629 4971908253535941250069559)
        ·
          refine ⟨7457862380303911875104339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4971908253535941250069559 7457862380303911875104339)
          ·
            refine ⟨11186793570455867812656509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7457862380303911875104339 11186793570455867812656509)
            ·
              refine ⟨4195047588920950429746191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11186793570455867812656509 4195047588920950429746191)
              ·
                refine ⟨6292571383381425644619287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4195047588920950429746191 6292571383381425644619287)
                ·
                  refine ⟨9438857075072138466928931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6292571383381425644619287 9438857075072138466928931)
                  ·
                    refine ⟨14158285612608207700393397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9438857075072138466928931 14158285612608207700393397)
                    ·
                      refine ⟨1327339276182019471911881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14158285612608207700393397 1327339276182019471911881)
                      ·
                        rfl

theorem cell23_2584984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_2584984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2584984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2584984 prefixEnd_2584984 := by exact prefixLift 2584984
  have htrace : WordTrace (prefixWord ++ tailWord_2584984) baseStart_2584984 baseEnd_2584984 := by
    simpa [prefixWord, tailWord_2584984, baseEnd_2584984] using wordTrace_append hprefix tailTrace_2584984
  have hstable : (prefixWord ++ tailWord_2584984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584984).length < 2 ^ (prefixWord ++ tailWord_2584984).sum := by decide
  have hdescent : baseEnd_2584984 < baseStart_2584984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2584997 : List Nat := [1, 3, 1, 2, 1, 1, 3, 2, 3, 3, 3]
def baseStart_2584997 : Nat := 118140960795 + 2584997 * 2 ^ 59
def prefixEnd_2584997 : Nat := 4983230072969 + 3 ^ 40 * 2584997 * 2
def baseEnd_2584997 : Nat := 1327345951430527921049321

theorem tailTrace_2584997 : CollatzResearch.WordTrace tailWord_2584997 prefixEnd_2584997 1327345951430527921049321 := by
  unfold tailWord_2584997
  simp only [CollatzResearch.WordTrace]
  refine ⟨94282586216004826184505245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62855057477336550789670163 94282586216004826184505245)
  ·
    refine ⟨35355969831001809819189467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94282586216004826184505245 35355969831001809819189467)
    ·
      refine ⟨53033954746502714728784201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35355969831001809819189467 53033954746502714728784201)
      ·
        refine ⟨39775466059877036046588151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53033954746502714728784201 39775466059877036046588151)
        ·
          refine ⟨59663199089815554069882227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39775466059877036046588151 59663199089815554069882227)
          ·
            refine ⟨89494798634723331104823341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59663199089815554069882227 89494798634723331104823341)
            ·
              refine ⟨33560549488021249164308753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89494798634723331104823341 33560549488021249164308753)
              ·
                refine ⟨25170412116015936873231565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33560549488021249164308753 25170412116015936873231565)
                ·
                  refine ⟨9438904543505976327461837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25170412116015936873231565 9438904543505976327461837)
                  ·
                    refine ⟨3539589203814741122798189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9438904543505976327461837 3539589203814741122798189)
                    ·
                      refine ⟨1327345951430527921049321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3539589203814741122798189 1327345951430527921049321)
                      ·
                        rfl

theorem cell23_2584997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 3, 3, 3].length) (baseStart_2584997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2584997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2584997 prefixEnd_2584997 := by exact prefixLift 2584997
  have htrace : WordTrace (prefixWord ++ tailWord_2584997) baseStart_2584997 baseEnd_2584997 := by
    simpa [prefixWord, tailWord_2584997, baseEnd_2584997] using wordTrace_append hprefix tailTrace_2584997
  have hstable : (prefixWord ++ tailWord_2584997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2584997).length < 2 ^ (prefixWord ++ tailWord_2584997).sum := by decide
  have hdescent : baseEnd_2584997 < baseStart_2584997 := by decide
  rcases family_descends (prefixWord ++ tailWord_2584997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2585067 : List Nat := [1, 1, 1, 1, 2, 3, 3, 3, 2, 2, 4]
def baseStart_2585067 : Nat := 118140960795 + 2585067 * 2 ^ 59
def prefixEnd_2585067 : Nat := 4983230072969 + 3 ^ 40 * 2585067 * 2
def baseEnd_2585067 : Nat := 1327381895076342647173999

theorem tailTrace_2585067 : CollatzResearch.WordTrace tailWord_2585067 prefixEnd_2585067 1327381895076342647173999 := by
  unfold tailWord_2585067
  simp only [CollatzResearch.WordTrace]
  refine ⟨94285139325751228139553455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62856759550500818759702303 94285139325751228139553455)
  ·
    refine ⟨141427708988626842209330183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94285139325751228139553455 141427708988626842209330183)
    ·
      refine ⟨212141563482940263313995275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141427708988626842209330183 212141563482940263313995275)
      ·
        refine ⟨318212345224410394970992913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212141563482940263313995275 318212345224410394970992913)
        ·
          refine ⟨238659258918307796228244685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 318212345224410394970992913 238659258918307796228244685)
          ·
            refine ⟨89497222094365423585591757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 238659258918307796228244685 89497222094365423585591757)
            ·
              refine ⟨33561458285387033844596909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89497222094365423585591757 33561458285387033844596909)
              ·
                refine ⟨12585546857020137691723841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33561458285387033844596909 12585546857020137691723841)
                ·
                  refine ⟨9439160142765103268792881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12585546857020137691723841 9439160142765103268792881)
                  ·
                    refine ⟨7079370107073827451594661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9439160142765103268792881 7079370107073827451594661)
                    ·
                      refine ⟨1327381895076342647173999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7079370107073827451594661 1327381895076342647173999)
                      ·
                        rfl

theorem cell23_2585067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 3, 2, 2, 4].length) (baseStart_2585067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2585067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2585067 prefixEnd_2585067 := by exact prefixLift 2585067
  have htrace : WordTrace (prefixWord ++ tailWord_2585067) baseStart_2585067 baseEnd_2585067 := by
    simpa [prefixWord, tailWord_2585067, baseEnd_2585067] using wordTrace_append hprefix tailTrace_2585067
  have hstable : (prefixWord ++ tailWord_2585067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2585067).length < 2 ^ (prefixWord ++ tailWord_2585067).sum := by decide
  have hdescent : baseEnd_2585067 < baseStart_2585067 := by decide
  rcases family_descends (prefixWord ++ tailWord_2585067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2585137 : List Nat := [1, 2, 2, 3, 1, 1, 2, 1, 2, 8]
def baseStart_2585137 : Nat := 118140960795 + 2585137 * 2 ^ 59
def prefixEnd_2585137 : Nat := 4983230072969 + 3 ^ 40 * 2585137 * 2
def baseEnd_2585137 : Nat := 442472612907385791099559

theorem tailTrace_2585137 : CollatzResearch.WordTrace tailWord_2585137 prefixEnd_2585137 442472612907385791099559 := by
  unfold tailWord_2585137
  simp only [CollatzResearch.WordTrace]
  refine ⟨94287692435497630094601665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62858461623665086729734443 94287692435497630094601665)
  ·
    refine ⟨70715769326623222570951249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94287692435497630094601665 70715769326623222570951249)
    ·
      refine ⟨53036826994967416928213437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70715769326623222570951249 53036826994967416928213437)
      ·
        refine ⟨19888810123112781348080039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53036826994967416928213437 19888810123112781348080039)
        ·
          refine ⟨29833215184669172022120059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19888810123112781348080039 29833215184669172022120059)
          ·
            refine ⟨44749822777003758033180089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29833215184669172022120059 44749822777003758033180089)
            ·
              refine ⟨33562367082752818524885067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44749822777003758033180089 33562367082752818524885067)
              ·
                refine ⟨50343550624129227787327601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33562367082752818524885067 50343550624129227787327601)
                ·
                  refine ⟨37757662968096920840495701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50343550624129227787327601 37757662968096920840495701)
                  ·
                    refine ⟨442472612907385791099559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 37757662968096920840495701 442472612907385791099559)
                    ·
                      rfl

theorem cell23_2585137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 8].length) (baseStart_2585137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2585137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2585137 prefixEnd_2585137 := by exact prefixLift 2585137
  have htrace : WordTrace (prefixWord ++ tailWord_2585137) baseStart_2585137 baseEnd_2585137 := by
    simpa [prefixWord, tailWord_2585137, baseEnd_2585137] using wordTrace_append hprefix tailTrace_2585137
  have hstable : (prefixWord ++ tailWord_2585137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2585137).length < 2 ^ (prefixWord ++ tailWord_2585137).sum := by decide
  have hdescent : baseEnd_2585137 < baseStart_2585137 := by decide
  rcases family_descends (prefixWord ++ tailWord_2585137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2585158 : List Nat := [6, 1, 1, 1, 2, 1, 2, 2, 2, 5]
def baseStart_2585158 : Nat := 118140960795 + 2585158 * 2 ^ 59
def prefixEnd_2585158 : Nat := 4983230072969 + 3 ^ 40 * 2585158 * 2
def baseEnd_2585158 : Nat := 442476207271967263712027

theorem tailTrace_2585158 : CollatzResearch.WordTrace tailWord_2585158 prefixEnd_2585158 442476207271967263712027 := by
  unfold tailWord_2585158
  simp only [CollatzResearch.WordTrace]
  refine ⟨2946514324013173458784879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 62858972245614367120744085 2946514324013173458784879)
  ·
    refine ⟨4419771486019760188177319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2946514324013173458784879 4419771486019760188177319)
    ·
      refine ⟨6629657229029640282265979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4419771486019760188177319 6629657229029640282265979)
      ·
        refine ⟨9944485843544460423398969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6629657229029640282265979 9944485843544460423398969)
        ·
          refine ⟨7458364382658345317549227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9944485843544460423398969 7458364382658345317549227)
          ·
            refine ⟨11187546573987517976323841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7458364382658345317549227 11187546573987517976323841)
            ·
              refine ⟨8390659930490638482242881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11187546573987517976323841 8390659930490638482242881)
              ·
                refine ⟨6292994947867978861682161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8390659930490638482242881 6292994947867978861682161)
                ·
                  refine ⟨4719746210900984146261621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6292994947867978861682161 4719746210900984146261621)
                  ·
                    refine ⟨442476207271967263712027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4719746210900984146261621 442476207271967263712027)
                    ·
                      rfl

theorem cell23_2585158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_2585158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2585158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2585158 prefixEnd_2585158 := by exact prefixLift 2585158
  have htrace : WordTrace (prefixWord ++ tailWord_2585158) baseStart_2585158 baseEnd_2585158 := by
    simpa [prefixWord, tailWord_2585158, baseEnd_2585158] using wordTrace_append hprefix tailTrace_2585158
  have hstable : (prefixWord ++ tailWord_2585158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2585158).length < 2 ^ (prefixWord ++ tailWord_2585158).sum := by decide
  have hdescent : baseEnd_2585158 < baseStart_2585158 := by decide
  rcases family_descends (prefixWord ++ tailWord_2585158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2585167 : List Nat := [1, 1, 2, 1, 1, 2, 4, 3, 8]
def baseStart_2585167 : Nat := 118140960795 + 2585167 * 2 ^ 59
def prefixEnd_2585167 : Nat := 4983230072969 + 3 ^ 40 * 2585167 * 2
def baseEnd_2585167 : Nat := 147492582571310250658171

theorem tailTrace_2585167 : CollatzResearch.WordTrace tailWord_2585167 prefixEnd_2585167 147492582571310250658171 := by
  unfold tailWord_2585167
  simp only [CollatzResearch.WordTrace]
  refine ⟨94288786625388945218193755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62859191083592630145462503 94288786625388945218193755)
  ·
    refine ⟨141433179938083417827290633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94288786625388945218193755 141433179938083417827290633)
    ·
      refine ⟨106074884953562563370467975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141433179938083417827290633 106074884953562563370467975)
      ·
        refine ⟨159112327430343845055701963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106074884953562563370467975 159112327430343845055701963)
        ·
          refine ⟨238668491145515767583552945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159112327430343845055701963 238668491145515767583552945)
          ·
            refine ⟨179001368359136825687664709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 238668491145515767583552945 179001368359136825687664709)
            ·
              refine ⟨33562756567338154816437133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 179001368359136825687664709 33562756567338154816437133)
              ·
                refine ⟨12586033712751808056163925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33562756567338154816437133 12586033712751808056163925)
                ·
                  refine ⟨147492582571310250658171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12586033712751808056163925 147492582571310250658171)
                  ·
                    rfl

theorem cell23_2585167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 3, 8].length) (baseStart_2585167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2585167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2585167 prefixEnd_2585167 := by exact prefixLift 2585167
  have htrace : WordTrace (prefixWord ++ tailWord_2585167) baseStart_2585167 baseEnd_2585167 := by
    simpa [prefixWord, tailWord_2585167, baseEnd_2585167] using wordTrace_append hprefix tailTrace_2585167
  have hstable : (prefixWord ++ tailWord_2585167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2585167).length < 2 ^ (prefixWord ++ tailWord_2585167).sum := by decide
  have hdescent : baseEnd_2585167 < baseStart_2585167 := by decide
  rcases family_descends (prefixWord ++ tailWord_2585167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2585184 : List Nat := [2, 1, 1, 3, 2, 1, 4, 3, 6]
def baseStart_2585184 : Nat := 118140960795 + 2585184 * 2 ^ 59
def prefixEnd_2585184 : Nat := 4983230072969 + 3 ^ 40 * 2585184 * 2
def baseEnd_2585184 : Nat := 147493552479213187712329

theorem tailTrace_2585184 : CollatzResearch.WordTrace tailWord_2585184 prefixEnd_2585184 147493552479213187712329 := by
  unfold tailWord_2585184
  simp only [CollatzResearch.WordTrace]
  refine ⟨47144703333163678560781303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62859604444218238081041737 47144703333163678560781303)
  ·
    refine ⟨70717054999745517841171955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47144703333163678560781303 70717054999745517841171955)
    ·
      refine ⟨106075582499618276761757933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70717054999745517841171955 106075582499618276761757933)
      ·
        refine ⟨39778343437356853785659225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106075582499618276761757933 39778343437356853785659225)
        ·
          refine ⟨29833757578017640339244419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39778343437356853785659225 29833757578017640339244419)
          ·
            refine ⟨44750636367026460508866629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29833757578017640339244419 44750636367026460508866629)
            ·
              refine ⟨8390744318817461345412493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44750636367026460508866629 8390744318817461345412493)
              ·
                refine ⟨3146529119556548004529685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8390744318817461345412493 3146529119556548004529685)
                ·
                  refine ⟨147493552479213187712329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3146529119556548004529685 147493552479213187712329)
                  ·
                    rfl

theorem cell23_2585184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 3, 6].length) (baseStart_2585184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2585184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2585184 prefixEnd_2585184 := by exact prefixLift 2585184
  have htrace : WordTrace (prefixWord ++ tailWord_2585184) baseStart_2585184 baseEnd_2585184 := by
    simpa [prefixWord, tailWord_2585184, baseEnd_2585184] using wordTrace_append hprefix tailTrace_2585184
  have hstable : (prefixWord ++ tailWord_2585184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2585184).length < 2 ^ (prefixWord ++ tailWord_2585184).sum := by decide
  have hdescent : baseEnd_2585184 < baseStart_2585184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2585184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2585198 : List Nat := [4, 1, 2, 2, 2, 1, 3, 1, 2, 2, 3]
def baseStart_2585198 : Nat := 118140960795 + 2585198 * 2 ^ 59
def prefixEnd_2585198 : Nat := 4983230072969 + 3 ^ 40 * 2585198 * 2
def baseEnd_2585198 : Nat := 1327449161042081634635897

theorem tailTrace_2585198 : CollatzResearch.WordTrace tailWord_2585198 prefixEnd_2585198 1327449161042081634635897 := by
  unfold tailWord_2585198
  simp only [CollatzResearch.WordTrace]
  refine ⟨11786239661034579689071531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62859944858851091675048165 11786239661034579689071531)
  ·
    refine ⟨17679359491551869533607297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11786239661034579689071531 17679359491551869533607297)
    ·
      refine ⟨13259519618663902150205473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17679359491551869533607297 13259519618663902150205473)
      ·
        refine ⟨9944639713997926612654105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13259519618663902150205473 9944639713997926612654105)
        ·
          refine ⟨7458479785498444959490579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9944639713997926612654105 7458479785498444959490579)
          ·
            refine ⟨11187719678247667439235869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7458479785498444959490579 11187719678247667439235869)
            ·
              refine ⟨4195394879342875289713451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11187719678247667439235869 4195394879342875289713451)
              ·
                refine ⟨6293092319014312934570177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4195394879342875289713451 6293092319014312934570177)
                ·
                  refine ⟨4719819239260734700927633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6293092319014312934570177 4719819239260734700927633)
                  ·
                    refine ⟨3539864429445551025695725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4719819239260734700927633 3539864429445551025695725)
                    ·
                      refine ⟨1327449161042081634635897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3539864429445551025695725 1327449161042081634635897)
                      ·
                        rfl

theorem cell23_2585198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_2585198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2585198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2585198 prefixEnd_2585198 := by exact prefixLift 2585198
  have htrace : WordTrace (prefixWord ++ tailWord_2585198) baseStart_2585198 baseEnd_2585198 := by
    simpa [prefixWord, tailWord_2585198, baseEnd_2585198] using wordTrace_append hprefix tailTrace_2585198
  have hstable : (prefixWord ++ tailWord_2585198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2585198).length < 2 ^ (prefixWord ++ tailWord_2585198).sum := by decide
  have hdescent : baseEnd_2585198 < baseStart_2585198 := by decide
  rcases family_descends (prefixWord ++ tailWord_2585198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2585248 : List Nat := [2, 1, 1, 4, 4, 1, 2, 2, 1, 5]
def baseStart_2585248 : Nat := 118140960795 + 2585248 * 2 ^ 59
def prefixEnd_2585248 : Nat := 4983230072969 + 3 ^ 40 * 2585248 * 2
def baseEnd_2585248 : Nat := 442491611691602146336889

theorem tailTrace_2585248 : CollatzResearch.WordTrace tailWord_2585248 prefixEnd_2585248 442491611691602146336889 := by
  unfold tailWord_2585248
  simp only [CollatzResearch.WordTrace]
  refine ⟨47145870469047748025946199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62861160625396997367928265 47145870469047748025946199)
  ·
    refine ⟨70718805703571622038919299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47145870469047748025946199 70718805703571622038919299)
    ·
      refine ⟨106078208555357433058378949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70718805703571622038919299 106078208555357433058378949)
      ·
        refine ⟨19889664104129518698446053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106078208555357433058378949 19889664104129518698446053)
        ·
          refine ⟨3729312019524284755958635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19889664104129518698446053 3729312019524284755958635)
          ·
            refine ⟨5593968029286427133937953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3729312019524284755958635 5593968029286427133937953)
            ·
              refine ⟨4195476021964820350453465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5593968029286427133937953 4195476021964820350453465)
              ·
                refine ⟨3146607016473615262840099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4195476021964820350453465 3146607016473615262840099)
                ·
                  refine ⟨4719910524710422894260149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3146607016473615262840099 4719910524710422894260149)
                  ·
                    refine ⟨442491611691602146336889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4719910524710422894260149 442491611691602146336889)
                    ·
                      rfl

theorem cell23_2585248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 2, 1, 5].length) (baseStart_2585248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2585248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2585248 prefixEnd_2585248 := by exact prefixLift 2585248
  have htrace : WordTrace (prefixWord ++ tailWord_2585248) baseStart_2585248 baseEnd_2585248 := by
    simpa [prefixWord, tailWord_2585248, baseEnd_2585248] using wordTrace_append hprefix tailTrace_2585248
  have hstable : (prefixWord ++ tailWord_2585248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2585248).length < 2 ^ (prefixWord ++ tailWord_2585248).sum := by decide
  have hdescent : baseEnd_2585248 < baseStart_2585248 := by decide
  rcases family_descends (prefixWord ++ tailWord_2585248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2585264 : List Nat := [2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 4]
def baseStart_2585264 : Nat := 118140960795 + 2585264 * 2 ^ 59
def prefixEnd_2585264 : Nat := 4983230072969 + 3 ^ 40 * 2585264 * 2
def baseEnd_2585264 : Nat := 1327483050765278376410593

theorem tailTrace_2585264 : CollatzResearch.WordTrace tailWord_2585264 prefixEnd_2585264 1327483050765278376410593 := by
  unfold tailWord_2585264
  simp only [CollatzResearch.WordTrace]
  refine ⟨47146162253018765392237423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62861549670691687189649897 47146162253018765392237423)
  ·
    refine ⟨70719243379528148088356135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47146162253018765392237423 70719243379528148088356135)
    ·
      refine ⟨106078865069292222132534203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70719243379528148088356135 106078865069292222132534203)
      ·
        refine ⟨159118297603938333198801305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106078865069292222132534203 159118297603938333198801305)
        ·
          refine ⟨119338723202953749899100979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159118297603938333198801305 119338723202953749899100979)
          ·
            refine ⟨179008084804430624848651469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119338723202953749899100979 179008084804430624848651469)
            ·
              refine ⟨67128031801661484318244301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 179008084804430624848651469 67128031801661484318244301)
              ·
                refine ⟨25173011925623056619341613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67128031801661484318244301 25173011925623056619341613)
                ·
                  refine ⟨9439879472108646232253105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25173011925623056619341613 9439879472108646232253105)
                  ·
                    refine ⟨7079909604081484674189829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9439879472108646232253105 7079909604081484674189829)
                    ·
                      refine ⟨1327483050765278376410593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7079909604081484674189829 1327483050765278376410593)
                      ·
                        rfl

theorem cell23_2585264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 4].length) (baseStart_2585264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2585264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2585264 prefixEnd_2585264 := by exact prefixLift 2585264
  have htrace : WordTrace (prefixWord ++ tailWord_2585264) baseStart_2585264 baseEnd_2585264 := by
    simpa [prefixWord, tailWord_2585264, baseEnd_2585264] using wordTrace_append hprefix tailTrace_2585264
  have hstable : (prefixWord ++ tailWord_2585264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2585264).length < 2 ^ (prefixWord ++ tailWord_2585264).sum := by decide
  have hdescent : baseEnd_2585264 < baseStart_2585264 := by decide
  rcases family_descends (prefixWord ++ tailWord_2585264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2585278 : List Nat := [4, 2, 1, 1, 2, 1, 2, 4, 2, 4]
def baseStart_2585278 : Nat := 118140960795 + 2585278 * 2 ^ 59
def prefixEnd_2585278 : Nat := 4983230072969 + 3 ^ 40 * 2585278 * 2
def baseEnd_2585278 : Nat := 442496746498147107211843

theorem tailTrace_2585278 : CollatzResearch.WordTrace tailWord_2585278 prefixEnd_2585278 442496746498147107211843 := by
  unfold tailWord_2585278
  simp only [CollatzResearch.WordTrace]
  refine ⟨11786604390998351396935561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62861890085324540783656325 11786604390998351396935561)
  ·
    refine ⟨8839953293248763547701671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11786604390998351396935561 8839953293248763547701671)
    ·
      refine ⟨13259929939873145321552507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8839953293248763547701671 13259929939873145321552507)
      ·
        refine ⟨19889894909809717982328761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13259929939873145321552507 19889894909809717982328761)
        ·
          refine ⟨14917421182357288486746571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19889894909809717982328761 14917421182357288486746571)
          ·
            refine ⟨22376131773535932730119857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14917421182357288486746571 22376131773535932730119857)
            ·
              refine ⟨16782098830151949547589893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22376131773535932730119857 16782098830151949547589893)
              ·
                refine ⟨3146643530653490540173105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16782098830151949547589893 3146643530653490540173105)
                ·
                  refine ⟨2359982647990117905129829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3146643530653490540173105 2359982647990117905129829)
                  ·
                    refine ⟨442496746498147107211843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2359982647990117905129829 442496746498147107211843)
                    ·
                      rfl

theorem cell23_2585278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 4, 2, 4].length) (baseStart_2585278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2585278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2585278 prefixEnd_2585278 := by exact prefixLift 2585278
  have htrace : WordTrace (prefixWord ++ tailWord_2585278) baseStart_2585278 baseEnd_2585278 := by
    simpa [prefixWord, tailWord_2585278, baseEnd_2585278] using wordTrace_append hprefix tailTrace_2585278
  have hstable : (prefixWord ++ tailWord_2585278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2585278).length < 2 ^ (prefixWord ++ tailWord_2585278).sum := by decide
  have hdescent : baseEnd_2585278 < baseStart_2585278 := by decide
  rcases family_descends (prefixWord ++ tailWord_2585278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2585351 : List Nat := [1, 1, 4, 4, 1, 1, 1, 1, 1, 8]
def baseStart_2585351 : Nat := 118140960795 + 2585351 * 2 ^ 59
def prefixEnd_2585351 : Nat := 4983230072969 + 3 ^ 40 * 2585351 * 2
def baseEnd_2585351 : Nat := 442509241194073178674231

theorem tailTrace_2585351 : CollatzResearch.WordTrace tailWord_2585351 prefixEnd_2585351 442509241194073178674231 := by
  unfold tailWord_2585351
  simp only [CollatzResearch.WordTrace]
  refine ⟨94295497656722344642891907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62863665104481563095261271 94295497656722344642891907)
  ·
    refine ⟨141443246485083516964337861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94295497656722344642891907 141443246485083516964337861)
    ·
      refine ⟨26520608715953159430813349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 141443246485083516964337861 26520608715953159430813349)
      ·
        refine ⟨4972614134241217393277503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26520608715953159430813349 4972614134241217393277503)
        ·
          refine ⟨7458921201361826089916255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4972614134241217393277503 7458921201361826089916255)
          ·
            refine ⟨11188381802042739134874383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7458921201361826089916255 11188381802042739134874383)
            ·
              refine ⟨16782572703064108702311575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11188381802042739134874383 16782572703064108702311575)
              ·
                refine ⟨25173859054596163053467363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16782572703064108702311575 25173859054596163053467363)
                ·
                  refine ⟨37760788581894244580201045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25173859054596163053467363 37760788581894244580201045)
                  ·
                    refine ⟨442509241194073178674231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 37760788581894244580201045 442509241194073178674231)
                    ·
                      rfl

theorem cell23_2585351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 8].length) (baseStart_2585351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2585351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2585351 prefixEnd_2585351 := by exact prefixLift 2585351
  have htrace : WordTrace (prefixWord ++ tailWord_2585351) baseStart_2585351 baseEnd_2585351 := by
    simpa [prefixWord, tailWord_2585351, baseEnd_2585351] using wordTrace_append hprefix tailTrace_2585351
  have hstable : (prefixWord ++ tailWord_2585351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2585351).length < 2 ^ (prefixWord ++ tailWord_2585351).sum := by decide
  have hdescent : baseEnd_2585351 < baseStart_2585351 := by decide
  rcases family_descends (prefixWord ++ tailWord_2585351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2585386 : List Nat := [3, 1, 4, 3, 2, 1, 1, 2, 2, 1, 3]
def baseStart_2585386 : Nat := 118140960795 + 2585386 * 2 ^ 59
def prefixEnd_2585386 : Nat := 4983230072969 + 3 ^ 40 * 2585386 * 2
def baseEnd_2585386 : Nat := 1327545695405126899085033

theorem tailTrace_2585386 : CollatzResearch.WordTrace tailWord_2585386 prefixEnd_2585386 1327545695405126899085033 := by
  unfold tailWord_2585386
  simp only [CollatzResearch.WordTrace]
  refine ⟨23574193552898886405104003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62864516141063697080277341 23574193552898886405104003)
  ·
    refine ⟨35361290329348329607656005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23574193552898886405104003 35361290329348329607656005)
    ·
      refine ⟨6630241936752811801435501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35361290329348329607656005 6630241936752811801435501)
      ·
        refine ⟨2486340726282304425538313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6630241936752811801435501 2486340726282304425538313)
        ·
          refine ⟨1864755544711728319153735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2486340726282304425538313 1864755544711728319153735)
          ·
            refine ⟨2797133317067592478730603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1864755544711728319153735 2797133317067592478730603)
            ·
              refine ⟨4195699975601388718095905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2797133317067592478730603 4195699975601388718095905)
              ·
                refine ⟨3146774981701041538571929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4195699975601388718095905 3146774981701041538571929)
                ·
                  refine ⟨2360081236275781153928947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3146774981701041538571929 2360081236275781153928947)
                  ·
                    refine ⟨3540121854413671730893421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2360081236275781153928947 3540121854413671730893421)
                    ·
                      refine ⟨1327545695405126899085033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3540121854413671730893421 1327545695405126899085033)
                      ·
                        rfl

theorem cell23_2585386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_2585386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2585386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2585386 prefixEnd_2585386 := by exact prefixLift 2585386
  have htrace : WordTrace (prefixWord ++ tailWord_2585386) baseStart_2585386 baseEnd_2585386 := by
    simpa [prefixWord, tailWord_2585386, baseEnd_2585386] using wordTrace_append hprefix tailTrace_2585386
  have hstable : (prefixWord ++ tailWord_2585386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2585386).length < 2 ^ (prefixWord ++ tailWord_2585386).sum := by decide
  have hdescent : baseEnd_2585386 < baseStart_2585386 := by decide
  rcases family_descends (prefixWord ++ tailWord_2585386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2585409 : List Nat := [1, 2, 5, 3, 1, 2, 1, 1, 1, 4, 2]
def baseStart_2585409 : Nat := 118140960795 + 2585409 * 2 ^ 59
def prefixEnd_2585409 : Nat := 4983230072969 + 3 ^ 40 * 2585409 * 2
def baseEnd_2585409 : Nat := 1327557505460180309097427

theorem tailTrace_2585409 : CollatzResearch.WordTrace tailWord_2585409 prefixEnd_2585409 1327557505460180309097427 := by
  unfold tailWord_2585409
  simp only [CollatzResearch.WordTrace]
  refine ⟨94297613090512220548503281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62865075393674813699002187 94297613090512220548503281)
  ·
    refine ⟨70723209817884165411377461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94297613090512220548503281 70723209817884165411377461)
    ·
      refine ⟨6630300920426640507316637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 70723209817884165411377461 6630300920426640507316637)
      ·
        refine ⟨2486362845159990190243739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6630300920426640507316637 2486362845159990190243739)
        ·
          refine ⟨3729544267739985285365609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2486362845159990190243739 3729544267739985285365609)
          ·
            refine ⟨2797158200804988964024207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3729544267739985285365609 2797158200804988964024207)
            ·
              refine ⟨4195737301207483446036311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2797158200804988964024207 4195737301207483446036311)
              ·
                refine ⟨6293605951811225169054467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4195737301207483446036311 6293605951811225169054467)
                ·
                  refine ⟨9440408927716837753581701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6293605951811225169054467 9440408927716837753581701)
                  ·
                    refine ⟨1770076673946907078796569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9440408927716837753581701 1770076673946907078796569)
                    ·
                      refine ⟨1327557505460180309097427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1770076673946907078796569 1327557505460180309097427)
                      ·
                        rfl

theorem cell23_2585409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_2585409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2585409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2585409 prefixEnd_2585409 := by exact prefixLift 2585409
  have htrace : WordTrace (prefixWord ++ tailWord_2585409) baseStart_2585409 baseEnd_2585409 := by
    simpa [prefixWord, tailWord_2585409, baseEnd_2585409] using wordTrace_append hprefix tailTrace_2585409
  have hstable : (prefixWord ++ tailWord_2585409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2585409).length < 2 ^ (prefixWord ++ tailWord_2585409).sum := by decide
  have hdescent : baseEnd_2585409 < baseStart_2585409 := by decide
  rcases family_descends (prefixWord ++ tailWord_2585409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2585448 : List Nat := [2, 1, 4, 2, 1, 2, 1, 1, 4, 1, 4]
def baseStart_2585448 : Nat := 118140960795 + 2585448 * 2 ^ 59
def prefixEnd_2585448 : Nat := 4983230072969 + 3 ^ 40 * 2585448 * 2
def baseEnd_2585448 : Nat := 1327577531205705656509747

theorem tailTrace_2585448 : CollatzResearch.WordTrace tailWord_2585448 prefixEnd_2585448 1327577531205705656509747 := by
  unfold tailWord_2585448
  simp only [CollatzResearch.WordTrace]
  refine ⟨47149517768685465104586499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62866023691580620139448665 47149517768685465104586499)
  ·
    refine ⟨70724276653028197656879749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47149517768685465104586499 70724276653028197656879749)
    ·
      refine ⟨13260801872442787060664953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70724276653028197656879749 13260801872442787060664953)
      ·
        refine ⟨9945601404332090295498715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13260801872442787060664953 9945601404332090295498715)
        ·
          refine ⟨14918402106498135443248073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9945601404332090295498715 14918402106498135443248073)
          ·
            refine ⟨11188801579873601582436055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14918402106498135443248073 11188801579873601582436055)
            ·
              refine ⟨16783202369810402373654083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11188801579873601582436055 16783202369810402373654083)
              ·
                refine ⟨25174803554715603560481125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16783202369810402373654083 25174803554715603560481125)
                ·
                  refine ⟨4720275666509175667590211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25174803554715603560481125 4720275666509175667590211)
                  ·
                    refine ⟨7080413499763763501385317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4720275666509175667590211 7080413499763763501385317)
                    ·
                      refine ⟨1327577531205705656509747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7080413499763763501385317 1327577531205705656509747)
                      ·
                        rfl

theorem cell23_2585448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_2585448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2585448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2585448 prefixEnd_2585448 := by exact prefixLift 2585448
  have htrace : WordTrace (prefixWord ++ tailWord_2585448) baseStart_2585448 baseEnd_2585448 := by
    simpa [prefixWord, tailWord_2585448, baseEnd_2585448] using wordTrace_append hprefix tailTrace_2585448
  have hstable : (prefixWord ++ tailWord_2585448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2585448).length < 2 ^ (prefixWord ++ tailWord_2585448).sum := by decide
  have hdescent : baseEnd_2585448 < baseStart_2585448 := by decide
  rcases family_descends (prefixWord ++ tailWord_2585448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2585492 : List Nat := [2, 4, 2, 1, 1, 1, 2, 5, 1, 4]
def baseStart_2585492 : Nat := 118140960795 + 2585492 * 2 ^ 59
def prefixEnd_2585492 : Nat := 4983230072969 + 3 ^ 40 * 2585492 * 2
def baseEnd_2585492 : Nat := 442533374784834494786515

theorem tailTrace_2585492 : CollatzResearch.WordTrace tailWord_2585492 prefixEnd_2585492 442533374784834494786515 := by
  unfold tailWord_2585492
  simp only [CollatzResearch.WordTrace]
  refine ⟨47150320174605762861887365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62867093566141017149183153 47150320174605762861887365)
  ·
    refine ⟨8840685032738580536603881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47150320174605762861887365 8840685032738580536603881)
    ·
      refine ⟨6630513774553935402452911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8840685032738580536603881 6630513774553935402452911)
      ·
        refine ⟨9945770661830903103679367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6630513774553935402452911 9945770661830903103679367)
        ·
          refine ⟨14918655992746354655519051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9945770661830903103679367 14918655992746354655519051)
          ·
            refine ⟨22377983989119531983278577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14918655992746354655519051 22377983989119531983278577)
            ·
              refine ⟨16783487991839648987458933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22377983989119531983278577 16783487991839648987458933)
              ·
                refine ⟨1573451999234967092574275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16783487991839648987458933 1573451999234967092574275)
                ·
                  refine ⟨2360177998852450638861413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1573451999234967092574275 2360177998852450638861413)
                  ·
                    refine ⟨442533374784834494786515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2360177998852450638861413 442533374784834494786515)
                    ·
                      rfl

theorem cell23_2585492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 5, 1, 4].length) (baseStart_2585492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2585492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2585492 prefixEnd_2585492 := by exact prefixLift 2585492
  have htrace : WordTrace (prefixWord ++ tailWord_2585492) baseStart_2585492 baseEnd_2585492 := by
    simpa [prefixWord, tailWord_2585492, baseEnd_2585492] using wordTrace_append hprefix tailTrace_2585492
  have hstable : (prefixWord ++ tailWord_2585492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2585492).length < 2 ^ (prefixWord ++ tailWord_2585492).sum := by decide
  have hdescent : baseEnd_2585492 < baseStart_2585492 := by decide
  rcases family_descends (prefixWord ++ tailWord_2585492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2585505 : List Nat := [1, 2, 3, 4, 1, 2, 2, 2, 6]
def baseStart_2585505 : Nat := 118140960795 + 2585505 * 2 ^ 59
def prefixEnd_2585505 : Nat := 4983230072969 + 3 ^ 40 * 2585505 * 2
def baseEnd_2585505 : Nat := 147511866622556881499665

theorem tailTrace_2585505 : CollatzResearch.WordTrace tailWord_2585505 prefixEnd_2585505 147511866622556881499665 := by
  unfold tailWord_2585505
  simp only [CollatzResearch.WordTrace]
  refine ⟨94301114498164428943997969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62867409665442952629331979 94301114498164428943997969)
  ·
    refine ⟨70725835873623321707998477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94301114498164428943997969 70725835873623321707998477)
    ·
      refine ⟨26522188452608745640499429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70725835873623321707998477 26522188452608745640499429)
      ·
        refine ⟨4972910334864139807593643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26522188452608745640499429 4972910334864139807593643)
        ·
          refine ⟨7459365502296209711390465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4972910334864139807593643 7459365502296209711390465)
          ·
            refine ⟨5594524126722157283542849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7459365502296209711390465 5594524126722157283542849)
            ·
              refine ⟨4195893095041617962657137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5594524126722157283542849 4195893095041617962657137)
              ·
                refine ⟨3146919821281213471992853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4195893095041617962657137 3146919821281213471992853)
                ·
                  refine ⟨147511866622556881499665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3146919821281213471992853 147511866622556881499665)
                  ·
                    rfl

theorem cell23_2585505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 2, 6].length) (baseStart_2585505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2585505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2585505 prefixEnd_2585505 := by exact prefixLift 2585505
  have htrace : WordTrace (prefixWord ++ tailWord_2585505) baseStart_2585505 baseEnd_2585505 := by
    simpa [prefixWord, tailWord_2585505, baseEnd_2585505] using wordTrace_append hprefix tailTrace_2585505
  have hstable : (prefixWord ++ tailWord_2585505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2585505).length < 2 ^ (prefixWord ++ tailWord_2585505).sum := by decide
  have hdescent : baseEnd_2585505 < baseStart_2585505 := by decide
  rcases family_descends (prefixWord ++ tailWord_2585505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2585525 : List Nat := [1, 3, 3, 2, 1, 1, 2, 2, 1, 5, 2]
def baseStart_2585525 : Nat := 118140960795 + 2585525 * 2 ^ 59
def prefixEnd_2585525 : Nat := 4983230072969 + 3 ^ 40 * 2585525 * 2
def baseEnd_2585525 : Nat := 1327617069216101855246893

theorem tailTrace_2585525 : CollatzResearch.WordTrace tailWord_2585525 prefixEnd_2585525 1327617069216101855246893 := by
  unfold tailWord_2585525
  simp only [CollatzResearch.WordTrace]
  refine ⟨94301843958091972359726029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62867895972061314906484019 94301843958091972359726029)
  ·
    refine ⟨35363191484284489634897261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94301843958091972359726029 35363191484284489634897261)
    ·
      refine ⟨13261196806606683613086473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35363191484284489634897261 13261196806606683613086473)
      ·
        refine ⟨9945897604955012709814855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13261196806606683613086473 9945897604955012709814855)
        ·
          refine ⟨14918846407432519064722283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9945897604955012709814855 14918846407432519064722283)
          ·
            refine ⟨22378269611148778597083425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14918846407432519064722283 22378269611148778597083425)
            ·
              refine ⟨16783702208361583947812569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22378269611148778597083425 16783702208361583947812569)
              ·
                refine ⟨12587776656271187960859427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16783702208361583947812569 12587776656271187960859427)
                ·
                  refine ⟨18881664984406781941289141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12587776656271187960859427 18881664984406781941289141)
                  ·
                    refine ⟨1770156092288135806995857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18881664984406781941289141 1770156092288135806995857)
                    ·
                      refine ⟨1327617069216101855246893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1770156092288135806995857 1327617069216101855246893)
                      ·
                        rfl

theorem cell23_2585525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 2, 1, 5, 2].length) (baseStart_2585525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2585525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2585525 prefixEnd_2585525 := by exact prefixLift 2585525
  have htrace : WordTrace (prefixWord ++ tailWord_2585525) baseStart_2585525 baseEnd_2585525 := by
    simpa [prefixWord, tailWord_2585525, baseEnd_2585525] using wordTrace_append hprefix tailTrace_2585525
  have hstable : (prefixWord ++ tailWord_2585525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2585525).length < 2 ^ (prefixWord ++ tailWord_2585525).sum := by decide
  have hdescent : baseEnd_2585525 < baseStart_2585525 := by decide
  rcases family_descends (prefixWord ++ tailWord_2585525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2585526 : List Nat := [5, 1, 4, 1, 1, 1, 1, 2, 3, 4]
def baseStart_2585526 : Nat := 118140960795 + 2585526 * 2 ^ 59
def prefixEnd_2585526 : Nat := 4983230072969 + 3 ^ 40 * 2585526 * 2
def baseEnd_2585526 : Nat := 442539194232252117111463

theorem tailTrace_2585526 : CollatzResearch.WordTrace tailWord_2585526 prefixEnd_2585526 442539194232252117111463 := by
  unfold tailWord_2585526
  simp only [CollatzResearch.WordTrace]
  refine ⟨5893867526943021845657027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 62867920287392233020341621 5893867526943021845657027)
  ·
    refine ⟨8840801290414532768485541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5893867526943021845657027 8840801290414532768485541)
    ·
      refine ⟨1657650241952724894091039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8840801290414532768485541 1657650241952724894091039)
      ·
        refine ⟨2486475362929087341136559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1657650241952724894091039 2486475362929087341136559)
        ·
          refine ⟨3729713044393631011704839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2486475362929087341136559 3729713044393631011704839)
          ·
            refine ⟨5594569566590446517557259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3729713044393631011704839 5594569566590446517557259)
            ·
              refine ⟨8391854349885669776335889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5594569566590446517557259 8391854349885669776335889)
              ·
                refine ⟨6293890762414252332251917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8391854349885669776335889 6293890762414252332251917)
                ·
                  refine ⟨2360209035905344624594469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6293890762414252332251917 2360209035905344624594469)
                  ·
                    refine ⟨442539194232252117111463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2360209035905344624594469 442539194232252117111463)
                    ·
                      rfl

theorem cell23_2585526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_2585526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2585526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2585526 prefixEnd_2585526 := by exact prefixLift 2585526
  have htrace : WordTrace (prefixWord ++ tailWord_2585526) baseStart_2585526 baseEnd_2585526 := by
    simpa [prefixWord, tailWord_2585526, baseEnd_2585526] using wordTrace_append hprefix tailTrace_2585526
  have hstable : (prefixWord ++ tailWord_2585526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2585526).length < 2 ^ (prefixWord ++ tailWord_2585526).sum := by decide
  have hdescent : baseEnd_2585526 < baseStart_2585526 := by decide
  rcases family_descends (prefixWord ++ tailWord_2585526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2585548 : List Nat := [2, 2, 1, 4, 1, 1, 1, 4, 1, 6]
def baseStart_2585548 : Nat := 118140960795 + 2585548 * 2 ^ 59
def prefixEnd_2585548 : Nat := 4983230072969 + 3 ^ 40 * 2585548 * 2
def baseEnd_2585548 : Nat := 442542959757051755086429

theorem tailTrace_2585548 : CollatzResearch.WordTrace tailWord_2585548 prefixEnd_2585548 442542959757051755086429 := by
  unfold tailWord_2585548
  simp only [CollatzResearch.WordTrace]
  refine ⟨47151341418504323643906649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62868455224672431525208865 47151341418504323643906649)
  ·
    refine ⟨35363506063878242732929987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47151341418504323643906649 35363506063878242732929987)
    ·
      refine ⟨53045259095817364099394981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35363506063878242732929987 53045259095817364099394981)
      ·
        refine ⟨9945986080465755768636559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53045259095817364099394981 9945986080465755768636559)
        ·
          refine ⟨14918979120698633652954839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9945986080465755768636559 14918979120698633652954839)
          ·
            refine ⟨22378468681047950479432259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14918979120698633652954839 22378468681047950479432259)
            ·
              refine ⟨33567703021571925719148389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22378468681047950479432259 33567703021571925719148389)
              ·
                refine ⟨6293944316544736072340323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33567703021571925719148389 6293944316544736072340323)
                ·
                  refine ⟨9440916474817104108510485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6293944316544736072340323 9440916474817104108510485)
                  ·
                    refine ⟨442542959757051755086429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9440916474817104108510485 442542959757051755086429)
                    ·
                      rfl

theorem cell23_2585548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 4, 1, 6].length) (baseStart_2585548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2585548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2585548 prefixEnd_2585548 := by exact prefixLift 2585548
  have htrace : WordTrace (prefixWord ++ tailWord_2585548) baseStart_2585548 baseEnd_2585548 := by
    simpa [prefixWord, tailWord_2585548, baseEnd_2585548] using wordTrace_append hprefix tailTrace_2585548
  have hstable : (prefixWord ++ tailWord_2585548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2585548).length < 2 ^ (prefixWord ++ tailWord_2585548).sum := by decide
  have hdescent : baseEnd_2585548 < baseStart_2585548 := by decide
  rcases family_descends (prefixWord ++ tailWord_2585548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2585575 : List Nat := [1, 1, 5, 2, 2, 2, 1, 2, 1, 1, 5]
def baseStart_2585575 : Nat := 118140960795 + 2585575 * 2 ^ 59
def prefixEnd_2585575 : Nat := 4983230072969 + 3 ^ 40 * 2585575 * 2
def baseEnd_2585575 : Nat := 1327642743248826659621663

theorem tailTrace_2585575 : CollatzResearch.WordTrace tailWord_2585575 prefixEnd_2585575 1327642743248826659621663 := by
  unfold tailWord_2585575
  simp only [CollatzResearch.WordTrace]
  refine ⟨94303667607910830899046179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62869111738607220599364119 94303667607910830899046179)
  ·
    refine ⟨141455501411866246348569269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94303667607910830899046179 141455501411866246348569269)
    ·
      refine ⟨13261453257362460595178369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 141455501411866246348569269 13261453257362460595178369)
      ·
        refine ⟨9946089943021845446383777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13261453257362460595178369 9946089943021845446383777)
        ·
          refine ⟨7459567457266384084787833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9946089943021845446383777 7459567457266384084787833)
          ·
            refine ⟨5594675592949788063590875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7459567457266384084787833 5594675592949788063590875)
            ·
              refine ⟨8392013389424682095386313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5594675592949788063590875 8392013389424682095386313)
              ·
                refine ⟨6294010042068511571539735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8392013389424682095386313 6294010042068511571539735)
                ·
                  refine ⟨9441015063102767357309603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6294010042068511571539735 9441015063102767357309603)
                  ·
                    refine ⟨14161522594654151035964405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9441015063102767357309603 14161522594654151035964405)
                    ·
                      refine ⟨1327642743248826659621663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14161522594654151035964405 1327642743248826659621663)
                      ·
                        rfl

theorem cell23_2585575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_2585575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2585575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2585575 prefixEnd_2585575 := by exact prefixLift 2585575
  have htrace : WordTrace (prefixWord ++ tailWord_2585575) baseStart_2585575 baseEnd_2585575 := by
    simpa [prefixWord, tailWord_2585575, baseEnd_2585575] using wordTrace_append hprefix tailTrace_2585575
  have hstable : (prefixWord ++ tailWord_2585575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2585575).length < 2 ^ (prefixWord ++ tailWord_2585575).sum := by decide
  have hdescent : baseEnd_2585575 < baseStart_2585575 := by decide
  rcases family_descends (prefixWord ++ tailWord_2585575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2585582 : List Nat := [4, 1, 2, 1, 4, 2, 1, 1, 1, 6]
def baseStart_2585582 : Nat := 118140960795 + 2585582 * 2 ^ 59
def prefixEnd_2585582 : Nat := 4983230072969 + 3 ^ 40 * 2585582 * 2
def baseEnd_2585582 : Nat := 442548779204469377411377

theorem tailTrace_2585582 : CollatzResearch.WordTrace tailWord_2585582 prefixEnd_2585582 442548779204469377411377 := by
  unfold tailWord_2585582
  simp only [CollatzResearch.WordTrace]
  refine ⟨11787990364860683886818875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62869281945923647396367333 11787990364860683886818875)
  ·
    refine ⟨17681985547291025830228313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11787990364860683886818875 17681985547291025830228313)
    ·
      refine ⟨13261489160468269372671235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17681985547291025830228313 13261489160468269372671235)
      ·
        refine ⟨19892233740702404059006853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13261489160468269372671235 19892233740702404059006853)
        ·
          refine ⟨3729793826381700761063785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19892233740702404059006853 3729793826381700761063785)
          ·
            refine ⟨2797345369786275570797839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3729793826381700761063785 2797345369786275570797839)
            ·
              refine ⟨4196018054679413356196759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2797345369786275570797839 4196018054679413356196759)
              ·
                refine ⟨6294027082019120034295139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4196018054679413356196759 6294027082019120034295139)
                ·
                  refine ⟨9441040623028680051442709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6294027082019120034295139 9441040623028680051442709)
                  ·
                    refine ⟨442548779204469377411377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9441040623028680051442709 442548779204469377411377)
                    ·
                      rfl

theorem cell23_2585582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 1, 1, 6].length) (baseStart_2585582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2585582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2585582 prefixEnd_2585582 := by exact prefixLift 2585582
  have htrace : WordTrace (prefixWord ++ tailWord_2585582) baseStart_2585582 baseEnd_2585582 := by
    simpa [prefixWord, tailWord_2585582, baseEnd_2585582] using wordTrace_append hprefix tailTrace_2585582
  have hstable : (prefixWord ++ tailWord_2585582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2585582).length < 2 ^ (prefixWord ++ tailWord_2585582).sum := by decide
  have hdescent : baseEnd_2585582 < baseStart_2585582 := by decide
  rcases family_descends (prefixWord ++ tailWord_2585582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2585585 : List Nat := [1, 2, 2, 2, 4, 1, 3, 1, 1, 2, 4]
def baseStart_2585585 : Nat := 118140960795 + 2585585 * 2 ^ 59
def prefixEnd_2585585 : Nat := 4983230072969 + 3 ^ 40 * 2585585 * 2
def baseEnd_2585585 : Nat := 1327647878055371620496617

theorem tailTrace_2585585 : CollatzResearch.WordTrace tailWord_2585585 prefixEnd_2585585 1327647878055371620496617 := by
  unfold tailWord_2585585
  simp only [CollatzResearch.WordTrace]
  refine ⟨94304032337874602606910209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62869354891916401737940139 94304032337874602606910209)
  ·
    refine ⟨70728024253405951955182657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94304032337874602606910209 70728024253405951955182657)
    ·
      refine ⟨53046018190054463966386993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70728024253405951955182657 53046018190054463966386993)
      ·
        refine ⟨39784513642540847974790245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53046018190054463966386993 39784513642540847974790245)
        ·
          refine ⟨7459596307976408995273171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39784513642540847974790245 7459596307976408995273171)
          ·
            refine ⟨11189394461964613492909757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7459596307976408995273171 11189394461964613492909757)
            ·
              refine ⟨4196022923236730059841159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11189394461964613492909757 4196022923236730059841159)
              ·
                refine ⟨6294034384855095089761739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4196022923236730059841159 6294034384855095089761739)
                ·
                  refine ⟨9441051577282642634642609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6294034384855095089761739 9441051577282642634642609)
                  ·
                    refine ⟨7080788682961981975981957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9441051577282642634642609 7080788682961981975981957)
                    ·
                      refine ⟨1327647878055371620496617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7080788682961981975981957 1327647878055371620496617)
                      ·
                        rfl

theorem cell23_2585585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 1, 1, 2, 4].length) (baseStart_2585585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2585585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2585585 prefixEnd_2585585 := by exact prefixLift 2585585
  have htrace : WordTrace (prefixWord ++ tailWord_2585585) baseStart_2585585 baseEnd_2585585 := by
    simpa [prefixWord, tailWord_2585585, baseEnd_2585585] using wordTrace_append hprefix tailTrace_2585585
  have hstable : (prefixWord ++ tailWord_2585585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2585585).length < 2 ^ (prefixWord ++ tailWord_2585585).sum := by decide
  have hdescent : baseEnd_2585585 < baseStart_2585585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2585585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2585605 : List Nat := [1, 3, 1, 1, 2, 3, 1, 1, 6, 1, 3]
def baseStart_2585605 : Nat := 118140960795 + 2585605 * 2 ^ 59
def prefixEnd_2585605 : Nat := 4983230072969 + 3 ^ 40 * 2585605 * 2
def baseEnd_2585605 : Nat := 1327658147668461542246525

theorem tailTrace_2585605 : CollatzResearch.WordTrace tailWord_2585605 prefixEnd_2585605 1327658147668461542246525 := by
  unfold tailWord_2585605
  simp only [CollatzResearch.WordTrace]
  refine ⟨94304761797802146022638269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62869841198534764015092179 94304761797802146022638269)
  ·
    refine ⟨35364285674175804758489351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94304761797802146022638269 35364285674175804758489351)
    ·
      refine ⟨53046428511263707137734027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35364285674175804758489351 53046428511263707137734027)
      ·
        refine ⟨79569642766895560706601041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53046428511263707137734027 79569642766895560706601041)
        ·
          refine ⟨59677232075171670529950781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79569642766895560706601041 59677232075171670529950781)
          ·
            refine ⟨22378962028189376448731543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59677232075171670529950781 22378962028189376448731543)
            ·
              refine ⟨33568443042284064673097315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22378962028189376448731543 33568443042284064673097315)
              ·
                refine ⟨50352664563426097009645973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33568443042284064673097315 50352664563426097009645973)
                ·
                  refine ⟨2360281151410598297327155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 50352664563426097009645973 2360281151410598297327155)
                  ·
                    refine ⟨3540421727115897445990733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2360281151410598297327155 3540421727115897445990733)
                    ·
                      refine ⟨1327658147668461542246525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3540421727115897445990733 1327658147668461542246525)
                      ·
                        rfl

theorem cell23_2585605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 6, 1, 3].length) (baseStart_2585605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2585605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2585605 prefixEnd_2585605 := by exact prefixLift 2585605
  have htrace : WordTrace (prefixWord ++ tailWord_2585605) baseStart_2585605 baseEnd_2585605 := by
    simpa [prefixWord, tailWord_2585605, baseEnd_2585605] using wordTrace_append hprefix tailTrace_2585605
  have hstable : (prefixWord ++ tailWord_2585605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2585605).length < 2 ^ (prefixWord ++ tailWord_2585605).sum := by decide
  have hdescent : baseEnd_2585605 < baseStart_2585605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2585605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2585623 : List Nat := [1, 1, 3, 5, 1, 2, 3, 2, 1, 2, 2]
def baseStart_2585623 : Nat := 118140960795 + 2585623 * 2 ^ 59
def prefixEnd_2585623 : Nat := 4983230072969 + 3 ^ 40 * 2585623 * 2
def baseEnd_2585623 : Nat := 1327667390320242471821443

theorem tailTrace_2585623 : CollatzResearch.WordTrace tailWord_2585623 prefixEnd_2585623 1327667390320242471821443 := by
  unfold tailWord_2585623
  simp only [CollatzResearch.WordTrace]
  refine ⟨94305418311736935096793523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62870278874491290064529015 94305418311736935096793523)
  ·
    refine ⟨141458127467605402645190285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94305418311736935096793523 141458127467605402645190285)
    ·
      refine ⟨53046797800352025991946357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141458127467605402645190285 53046797800352025991946357)
      ·
        refine ⟨4973137293783002436744971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 53046797800352025991946357 4973137293783002436744971)
        ·
          refine ⟨7459705940674503655117457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4973137293783002436744971 7459705940674503655117457)
          ·
            refine ⟨5594779455505877741338093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7459705940674503655117457 5594779455505877741338093)
            ·
              refine ⟨2098042295814704153001785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5594779455505877741338093 2098042295814704153001785)
              ·
                refine ⟨1573531721861028114751339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2098042295814704153001785 1573531721861028114751339)
                ·
                  refine ⟨2360297582791542172127009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1573531721861028114751339 2360297582791542172127009)
                  ·
                    refine ⟨1770223187093656629095257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2360297582791542172127009 1770223187093656629095257)
                    ·
                      refine ⟨1327667390320242471821443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1770223187093656629095257 1327667390320242471821443)
                      ·
                        rfl

theorem cell23_2585623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 3, 2, 1, 2, 2].length) (baseStart_2585623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2585623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2585623 prefixEnd_2585623 := by exact prefixLift 2585623
  have htrace : WordTrace (prefixWord ++ tailWord_2585623) baseStart_2585623 baseEnd_2585623 := by
    simpa [prefixWord, tailWord_2585623, baseEnd_2585623] using wordTrace_append hprefix tailTrace_2585623
  have hstable : (prefixWord ++ tailWord_2585623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2585623).length < 2 ^ (prefixWord ++ tailWord_2585623).sum := by decide
  have hdescent : baseEnd_2585623 < baseStart_2585623 := by decide
  rcases family_descends (prefixWord ++ tailWord_2585623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2585648 : List Nat := [2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 5]
def baseStart_2585648 : Nat := 118140960795 + 2585648 * 2 ^ 59
def prefixEnd_2585648 : Nat := 4983230072969 + 3 ^ 40 * 2585648 * 2
def baseEnd_2585648 : Nat := 1327680227336604874008827

theorem tailTrace_2585648 : CollatzResearch.WordTrace tailWord_2585648 prefixEnd_2585648 1327680227336604874008827 := by
  unfold tailWord_2585648
  simp only [CollatzResearch.WordTrace]
  refine ⟨47153165068323182183226799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62870886757764242910969065 47153165068323182183226799)
  ·
    refine ⟨70729747602484773274840199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47153165068323182183226799 70729747602484773274840199)
    ·
      refine ⟨106094621403727159912260299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70729747602484773274840199 106094621403727159912260299)
      ·
        refine ⟨159141932105590739868390449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106094621403727159912260299 159141932105590739868390449)
        ·
          refine ⟨119356449079193054901292837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159141932105590739868390449 119356449079193054901292837)
          ·
            refine ⟨22379334202348697793992407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 119356449079193054901292837 22379334202348697793992407)
            ·
              refine ⟨33569001303523046690988611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22379334202348697793992407 33569001303523046690988611)
              ·
                refine ⟨50353501955284570036482917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33569001303523046690988611 50353501955284570036482917)
                ·
                  refine ⟨9441281616615856881840547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50353501955284570036482917 9441281616615856881840547)
                  ·
                    refine ⟨14161922424923785322760821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9441281616615856881840547 14161922424923785322760821)
                    ·
                      refine ⟨1327680227336604874008827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14161922424923785322760821 1327680227336604874008827)
                      ·
                        rfl

theorem cell23_2585648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 5].length) (baseStart_2585648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2585648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2585648 prefixEnd_2585648 := by exact prefixLift 2585648
  have htrace : WordTrace (prefixWord ++ tailWord_2585648) baseStart_2585648 baseEnd_2585648 := by
    simpa [prefixWord, tailWord_2585648, baseEnd_2585648] using wordTrace_append hprefix tailTrace_2585648
  have hstable : (prefixWord ++ tailWord_2585648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2585648).length < 2 ^ (prefixWord ++ tailWord_2585648).sum := by decide
  have hdescent : baseEnd_2585648 < baseStart_2585648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2585648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2585695 : List Nat := [1, 1, 2, 3, 1, 1, 5, 1, 2, 3, 3]
def baseStart_2585695 : Nat := 118140960795 + 2585695 * 2 ^ 59
def prefixEnd_2585695 : Nat := 4983230072969 + 3 ^ 40 * 2585695 * 2
def baseEnd_2585695 : Nat := 1327704360927366190121111

theorem tailTrace_2585695 : CollatzResearch.WordTrace tailWord_2585695 prefixEnd_2585695 1327704360927366190121111 := by
  unfold tailWord_2585695
  simp only [CollatzResearch.WordTrace]
  refine ⟨94308044367476091393414539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62872029578317394262276359 94308044367476091393414539)
  ·
    refine ⟨141462066551214137090121809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94308044367476091393414539 141462066551214137090121809)
    ·
      refine ⟨106096549913410602817591357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141462066551214137090121809 106096549913410602817591357)
      ·
        refine ⟨39786206217528976056596759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106096549913410602817591357 39786206217528976056596759)
        ·
          refine ⟨59679309326293464084895139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39786206217528976056596759 59679309326293464084895139)
          ·
            refine ⟨89518963989440196127342709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59679309326293464084895139 89518963989440196127342709)
            ·
              refine ⟨8392402874010018386938379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 89518963989440196127342709 8392402874010018386938379)
              ·
                refine ⟨12588604311015027580407569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8392402874010018386938379 12588604311015027580407569)
                ·
                  refine ⟨9441453233261270685305677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12588604311015027580407569 9441453233261270685305677)
                  ·
                    refine ⟨3540544962472976506989629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9441453233261270685305677 3540544962472976506989629)
                    ·
                      refine ⟨1327704360927366190121111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3540544962472976506989629 1327704360927366190121111)
                      ·
                        rfl

theorem cell23_2585695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 1, 2, 3, 3].length) (baseStart_2585695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2585695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2585695 prefixEnd_2585695 := by exact prefixLift 2585695
  have htrace : WordTrace (prefixWord ++ tailWord_2585695) baseStart_2585695 baseEnd_2585695 := by
    simpa [prefixWord, tailWord_2585695, baseEnd_2585695] using wordTrace_append hprefix tailTrace_2585695
  have hstable : (prefixWord ++ tailWord_2585695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2585695).length < 2 ^ (prefixWord ++ tailWord_2585695).sum := by decide
  have hdescent : baseEnd_2585695 < baseStart_2585695 := by decide
  rcases family_descends (prefixWord ++ tailWord_2585695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2585735 : List Nat := [1, 1, 4, 2, 1, 1, 1, 3, 4, 1, 4]
def baseStart_2585735 : Nat := 118140960795 + 2585735 * 2 ^ 59
def prefixEnd_2585735 : Nat := 4983230072969 + 3 ^ 40 * 2585735 * 2
def baseEnd_2585735 : Nat := 1327724900153546033620927

theorem tailTrace_2585735 : CollatzResearch.WordTrace tailWord_2585735 prefixEnd_2585735 1327724900153546033620927 := by
  unfold tailWord_2585735
  simp only [CollatzResearch.WordTrace]
  refine ⟨94309503287331178224870659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62873002191554118816580439 94309503287331178224870659)
  ·
    refine ⟨141464254930996767337305989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94309503287331178224870659 141464254930996767337305989)
    ·
      refine ⟨26524547799561893875744873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 141464254930996767337305989 26524547799561893875744873)
      ·
        refine ⟨19893410849671420406808655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26524547799561893875744873 19893410849671420406808655)
        ·
          refine ⟨29840116274507130610212983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19893410849671420406808655 29840116274507130610212983)
          ·
            refine ⟨44760174411760695915319475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29840116274507130610212983 44760174411760695915319475)
            ·
              refine ⟨67140261617641043872979213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44760174411760695915319475 67140261617641043872979213)
              ·
                refine ⟨25177598106615391452367205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67140261617641043872979213 25177598106615391452367205)
                ·
                  refine ⟨4720799644990385897318851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25177598106615391452367205 4720799644990385897318851)
                  ·
                    refine ⟨7081199467485578845978277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4720799644990385897318851 7081199467485578845978277)
                    ·
                      refine ⟨1327724900153546033620927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7081199467485578845978277 1327724900153546033620927)
                      ·
                        rfl

theorem cell23_2585735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 4, 1, 4].length) (baseStart_2585735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2585735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2585735 prefixEnd_2585735 := by exact prefixLift 2585735
  have htrace : WordTrace (prefixWord ++ tailWord_2585735) baseStart_2585735 baseEnd_2585735 := by
    simpa [prefixWord, tailWord_2585735, baseEnd_2585735] using wordTrace_append hprefix tailTrace_2585735
  have hstable : (prefixWord ++ tailWord_2585735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2585735).length < 2 ^ (prefixWord ++ tailWord_2585735).sum := by decide
  have hdescent : baseEnd_2585735 < baseStart_2585735 := by decide
  rcases family_descends (prefixWord ++ tailWord_2585735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2585779 : List Nat := [1, 1, 1, 2, 3, 2, 5, 3, 1, 4]
def baseStart_2585779 : Nat := 118140960795 + 2585779 * 2 ^ 59
def prefixEnd_2585779 : Nat := 4983230072969 + 3 ^ 40 * 2585779 * 2
def baseEnd_2585779 : Nat := 442582497767447953823575

theorem tailTrace_2585779 : CollatzResearch.WordTrace tailWord_2585779 prefixEnd_2585779 442582497767447953823575 := by
  unfold tailWord_2585779
  simp only [CollatzResearch.WordTrace]
  refine ⟨94311108099171773739472391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62874072066114515826314927 94311108099171773739472391)
  ·
    refine ⟨141466662148757660609208587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94311108099171773739472391 141466662148757660609208587)
    ·
      refine ⟨212199993223136490913812881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141466662148757660609208587 212199993223136490913812881)
      ·
        refine ⟨159149994917352368185359661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212199993223136490913812881 159149994917352368185359661)
        ·
          refine ⟨59681248094007138069509873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 159149994917352368185359661 59681248094007138069509873)
          ·
            refine ⟨44760936070505353552132405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59681248094007138069509873 44760936070505353552132405)
            ·
              refine ⟨4196337756609876895512413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44760936070505353552132405 4196337756609876895512413)
              ·
                refine ⟨1573626658728703835817155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4196337756609876895512413 1573626658728703835817155)
                ·
                  refine ⟨2360439988093055753725733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1573626658728703835817155 2360439988093055753725733)
                  ·
                    refine ⟨442582497767447953823575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2360439988093055753725733 442582497767447953823575)
                    ·
                      rfl

theorem cell23_2585779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 3, 1, 4].length) (baseStart_2585779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2585779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2585779 prefixEnd_2585779 := by exact prefixLift 2585779
  have htrace : WordTrace (prefixWord ++ tailWord_2585779) baseStart_2585779 baseEnd_2585779 := by
    simpa [prefixWord, tailWord_2585779, baseEnd_2585779] using wordTrace_append hprefix tailTrace_2585779
  have hstable : (prefixWord ++ tailWord_2585779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2585779).length < 2 ^ (prefixWord ++ tailWord_2585779).sum := by decide
  have hdescent : baseEnd_2585779 < baseStart_2585779 := by decide
  rcases family_descends (prefixWord ++ tailWord_2585779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2585796 : List Nat := [2, 3, 3, 1, 3, 2, 1, 1, 3, 4]
def baseStart_2585796 : Nat := 118140960795 + 2585796 * 2 ^ 59
def prefixEnd_2585796 : Nat := 4983230072969 + 3 ^ 40 * 2585796 * 2
def baseEnd_2585796 : Nat := 442585407491156764986049

theorem tailTrace_2585796 : CollatzResearch.WordTrace tailWord_2585796 prefixEnd_2585796 442585407491156764986049 := by
  unfold tailWord_2585796
  simp only [CollatzResearch.WordTrace]
  refine ⟨47155864070055092821420621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62874485426740123761894161 47155864070055092821420621)
  ·
    refine ⟨17683449026270659808032733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47155864070055092821420621 17683449026270659808032733)
    ·
      refine ⟨6631293384851497428012275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17683449026270659808032733 6631293384851497428012275)
      ·
        refine ⟨9946940077277246142018413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6631293384851497428012275 9946940077277246142018413)
        ·
          refine ⟨3730102528978967303256905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9946940077277246142018413 3730102528978967303256905)
          ·
            refine ⟨2797576896734225477442679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3730102528978967303256905 2797576896734225477442679)
            ·
              refine ⟨4196365345101338216164019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2797576896734225477442679 4196365345101338216164019)
              ·
                refine ⟨6294548017652007324246029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4196365345101338216164019 6294548017652007324246029)
                ·
                  refine ⟨2360455506619502746592261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6294548017652007324246029 2360455506619502746592261)
                  ·
                    refine ⟨442585407491156764986049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2360455506619502746592261 442585407491156764986049)
                    ·
                      rfl

theorem cell23_2585796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_2585796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2585796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2585796 prefixEnd_2585796 := by exact prefixLift 2585796
  have htrace : WordTrace (prefixWord ++ tailWord_2585796) baseStart_2585796 baseEnd_2585796 := by
    simpa [prefixWord, tailWord_2585796, baseEnd_2585796] using wordTrace_append hprefix tailTrace_2585796
  have hstable : (prefixWord ++ tailWord_2585796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2585796).length < 2 ^ (prefixWord ++ tailWord_2585796).sum := by decide
  have hdescent : baseEnd_2585796 < baseStart_2585796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2585796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2585835 : List Nat := [1, 1, 1, 1, 2, 6, 1, 1, 3, 6]
def baseStart_2585835 : Nat := 118140960795 + 2585835 * 2 ^ 59
def prefixEnd_2585835 : Nat := 4983230072969 + 3 ^ 40 * 2585835 * 2
def baseEnd_2585835 : Nat := 442592082739665214123489

theorem tailTrace_2585835 : CollatzResearch.WordTrace tailWord_2585835 prefixEnd_2585835 442592082739665214123489 := by
  unfold tailWord_2585835
  simp only [CollatzResearch.WordTrace]
  refine ⟨94313150586968895303510959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62875433724645930202340639 94313150586968895303510959)
  ·
    refine ⟨141469725880453342955266439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94313150586968895303510959 141469725880453342955266439)
    ·
      refine ⟨212204588820680014432899659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141469725880453342955266439 212204588820680014432899659)
      ·
        refine ⟨318306883231020021649349489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212204588820680014432899659 318306883231020021649349489)
        ·
          refine ⟨238730162423265016237012117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 318306883231020021649349489 238730162423265016237012117)
          ·
            refine ⟨11190476363590547636109943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 238730162423265016237012117 11190476363590547636109943)
            ·
              refine ⟨16785714545385821454164915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11190476363590547636109943 16785714545385821454164915)
              ·
                refine ⟨25178571818078732181247373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16785714545385821454164915 25178571818078732181247373)
                ·
                  refine ⟨9441964431779524567967765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25178571818078732181247373 9441964431779524567967765)
                  ·
                    refine ⟨442592082739665214123489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9441964431779524567967765 442592082739665214123489)
                    ·
                      rfl

theorem cell23_2585835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 3, 6].length) (baseStart_2585835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2585835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2585835 prefixEnd_2585835 := by exact prefixLift 2585835
  have htrace : WordTrace (prefixWord ++ tailWord_2585835) baseStart_2585835 baseEnd_2585835 := by
    simpa [prefixWord, tailWord_2585835, baseEnd_2585835] using wordTrace_append hprefix tailTrace_2585835
  have hstable : (prefixWord ++ tailWord_2585835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2585835).length < 2 ^ (prefixWord ++ tailWord_2585835).sum := by decide
  have hdescent : baseEnd_2585835 < baseStart_2585835 := by decide
  rcases family_descends (prefixWord ++ tailWord_2585835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2585879 : List Nat := [1, 1, 3, 4, 1, 1, 2, 4, 1, 2, 3]
def baseStart_2585879 : Nat := 118140960795 + 2585879 * 2 ^ 59
def prefixEnd_2585879 : Nat := 4983230072969 + 3 ^ 40 * 2585879 * 2
def baseEnd_2585879 : Nat := 1327798841367793470220265

theorem tailTrace_2585879 : CollatzResearch.WordTrace tailWord_2585879 prefixEnd_2585879 1327798841367793470220265 := by
  unfold tailWord_2585879
  simp only [CollatzResearch.WordTrace]
  refine ⟨94314755398809490818112691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62876503599206327212075127 94314755398809490818112691)
  ·
    refine ⟨141472133098214236227169037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94314755398809490818112691 141472133098214236227169037)
    ·
      refine ⟨53052049911830338585188389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141472133098214236227169037 53052049911830338585188389)
      ·
        refine ⟨9947259358468188484722823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53052049911830338585188389 9947259358468188484722823)
        ·
          refine ⟨14920889037702282727084235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9947259358468188484722823 14920889037702282727084235)
          ·
            refine ⟨22381333556553424090626353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14920889037702282727084235 22381333556553424090626353)
            ·
              refine ⟨16786000167415068067969765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22381333556553424090626353 16786000167415068067969765)
              ·
                refine ⟨3147375031390325262744331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16786000167415068067969765 3147375031390325262744331)
                ·
                  refine ⟨4721062547085487894116497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3147375031390325262744331 4721062547085487894116497)
                  ·
                    refine ⟨3540796910314115920587373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4721062547085487894116497 3540796910314115920587373)
                    ·
                      refine ⟨1327798841367793470220265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3540796910314115920587373 1327798841367793470220265)
                      ·
                        rfl

theorem cell23_2585879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 4, 1, 2, 3].length) (baseStart_2585879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2585879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2585879 prefixEnd_2585879 := by exact prefixLift 2585879
  have htrace : WordTrace (prefixWord ++ tailWord_2585879) baseStart_2585879 baseEnd_2585879 := by
    simpa [prefixWord, tailWord_2585879, baseEnd_2585879] using wordTrace_append hprefix tailTrace_2585879
  have hstable : (prefixWord ++ tailWord_2585879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2585879).length < 2 ^ (prefixWord ++ tailWord_2585879).sum := by decide
  have hdescent : baseEnd_2585879 < baseStart_2585879 := by decide
  rcases family_descends (prefixWord ++ tailWord_2585879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2585893 : List Nat := [1, 3, 1, 2, 4, 1, 1, 5, 1, 2, 2]
def baseStart_2585893 : Nat := 118140960795 + 2585893 * 2 ^ 59
def prefixEnd_2585893 : Nat := 4983230072969 + 3 ^ 40 * 2585893 * 2
def baseEnd_2585893 : Nat := 1327806030096956415445201

theorem tailTrace_2585893 : CollatzResearch.WordTrace tailWord_2585893 prefixEnd_2585893 1327806030096956415445201 := by
  unfold tailWord_2585893
  simp only [CollatzResearch.WordTrace]
  refine ⟨94315266020758771209122333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62876844013839180806081555 94315266020758771209122333)
  ·
    refine ⟨35368224757784539203420875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94315266020758771209122333 35368224757784539203420875)
    ·
      refine ⟨53052337136676808805131313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35368224757784539203420875 53052337136676808805131313)
      ·
        refine ⟨39789252852507606603848485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53052337136676808805131313 39789252852507606603848485)
        ·
          refine ⟨7460484909845176238221591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39789252852507606603848485 7460484909845176238221591)
          ·
            refine ⟨11190727364767764357332387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7460484909845176238221591 11190727364767764357332387)
            ·
              refine ⟨16786091047151646535998581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11190727364767764357332387 16786091047151646535998581)
              ·
                refine ⟨1573696035670466862749867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16786091047151646535998581 1573696035670466862749867)
                ·
                  refine ⟨2360544053505700294124801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1573696035670466862749867 2360544053505700294124801)
                  ·
                    refine ⟨1770408040129275220593601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2360544053505700294124801 1770408040129275220593601)
                    ·
                      refine ⟨1327806030096956415445201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1770408040129275220593601 1327806030096956415445201)
                      ·
                        rfl

theorem cell23_2585893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 5, 1, 2, 2].length) (baseStart_2585893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2585893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2585893 prefixEnd_2585893 := by exact prefixLift 2585893
  have htrace : WordTrace (prefixWord ++ tailWord_2585893) baseStart_2585893 baseEnd_2585893 := by
    simpa [prefixWord, tailWord_2585893, baseEnd_2585893] using wordTrace_append hprefix tailTrace_2585893
  have hstable : (prefixWord ++ tailWord_2585893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2585893).length < 2 ^ (prefixWord ++ tailWord_2585893).sum := by decide
  have hdescent : baseEnd_2585893 < baseStart_2585893 := by decide
  rcases family_descends (prefixWord ++ tailWord_2585893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2585896 : List Nat := [2, 1, 5, 1, 2, 2, 1, 3, 1, 2, 3]
def baseStart_2585896 : Nat := 118140960795 + 2585896 * 2 ^ 59
def prefixEnd_2585896 : Nat := 4983230072969 + 3 ^ 40 * 2585896 * 2
def baseEnd_2585896 : Nat := 1327807570538919903707687

theorem tailTrace_2585896 : CollatzResearch.WordTrace tailWord_2585896 prefixEnd_2585896 1327807570538919903707687 := by
  unfold tailWord_2585896
  simp only [CollatzResearch.WordTrace]
  refine ⟨47157687719873951360740771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62876916959831935147654361 47157687719873951360740771)
  ·
    refine ⟨70736531579810927041111157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47157687719873951360740771 70736531579810927041111157)
    ·
      refine ⟨6631549835607274410104171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 70736531579810927041111157 6631549835607274410104171)
      ·
        refine ⟨9947324753410911615156257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6631549835607274410104171 9947324753410911615156257)
        ·
          refine ⟨7460493565058183711367193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9947324753410911615156257 7460493565058183711367193)
          ·
            refine ⟨5595370173793637783525395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7460493565058183711367193 5595370173793637783525395)
            ·
              refine ⟨8393055260690456675288093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5595370173793637783525395 8393055260690456675288093)
              ·
                refine ⟨3147395722758921253233035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8393055260690456675288093 3147395722758921253233035)
                ·
                  refine ⟨4721093584138381879849553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3147395722758921253233035 4721093584138381879849553)
                  ·
                    refine ⟨3540820188103786409887165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4721093584138381879849553 3540820188103786409887165)
                    ·
                      refine ⟨1327807570538919903707687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3540820188103786409887165 1327807570538919903707687)
                      ·
                        rfl

theorem cell23_2585896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 3, 1, 2, 3].length) (baseStart_2585896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2585896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2585896 prefixEnd_2585896 := by exact prefixLift 2585896
  have htrace : WordTrace (prefixWord ++ tailWord_2585896) baseStart_2585896 baseEnd_2585896 := by
    simpa [prefixWord, tailWord_2585896, baseEnd_2585896] using wordTrace_append hprefix tailTrace_2585896
  have hstable : (prefixWord ++ tailWord_2585896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2585896).length < 2 ^ (prefixWord ++ tailWord_2585896).sum := by decide
  have hdescent : baseEnd_2585896 < baseStart_2585896 := by decide
  rcases family_descends (prefixWord ++ tailWord_2585896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2585933 : List Nat := [1, 6, 1, 3, 1, 2, 2, 7]
def baseStart_2585933 : Nat := 118140960795 + 2585933 * 2 ^ 59
def prefixEnd_2585933 : Nat := 4983230072969 + 3 ^ 40 * 2585933 * 2
def baseEnd_2585933 : Nat := 49178761826782824405371

theorem tailTrace_2585933 : CollatzResearch.WordTrace tailWord_2585933 prefixEnd_2585933 49178761826782824405371 := by
  unfold tailWord_2585933
  simp only [CollatzResearch.WordTrace]
  refine ⟨94316724940613858040578453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62877816627075905360385635 94316724940613858040578453)
  ·
    refine ⟨4421096481591274595652115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 94316724940613858040578453 4421096481591274595652115)
    ·
      refine ⟨6631644722386911893478173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4421096481591274595652115 6631644722386911893478173)
      ·
        refine ⟨2486866770895091960054315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6631644722386911893478173 2486866770895091960054315)
        ·
          refine ⟨3730300156342637940081473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2486866770895091960054315 3730300156342637940081473)
          ·
            refine ⟨2797725117256978455061105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3730300156342637940081473 2797725117256978455061105)
            ·
              refine ⟨2098293837942733841295829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2797725117256978455061105 2098293837942733841295829)
              ·
                refine ⟨49178761826782824405371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2098293837942733841295829 49178761826782824405371)
                ·
                  rfl

theorem cell23_2585933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 2, 7].length) (baseStart_2585933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2585933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2585933 prefixEnd_2585933 := by exact prefixLift 2585933
  have htrace : WordTrace (prefixWord ++ tailWord_2585933) baseStart_2585933 baseEnd_2585933 := by
    simpa [prefixWord, tailWord_2585933, baseEnd_2585933] using wordTrace_append hprefix tailTrace_2585933
  have hstable : (prefixWord ++ tailWord_2585933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2585933).length < 2 ^ (prefixWord ++ tailWord_2585933).sum := by decide
  have hdescent : baseEnd_2585933 < baseStart_2585933 := by decide
  rcases family_descends (prefixWord ++ tailWord_2585933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2585936 : List Nat := [2, 1, 1, 1, 1, 5, 4, 2, 1, 3, 2]
def baseStart_2585936 : Nat := 118140960795 + 2585936 * 2 ^ 59
def prefixEnd_2585936 : Nat := 4983230072969 + 3 ^ 40 * 2585936 * 2
def baseEnd_2585936 : Nat := 1327828109765099747207503

theorem tailTrace_2585936 : CollatzResearch.WordTrace tailWord_2585936 prefixEnd_2585936 1327828109765099747207503 := by
  unfold tailWord_2585936
  simp only [CollatzResearch.WordTrace]
  refine ⟨47158417179801494776468831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62877889573068659701958441 47158417179801494776468831)
  ·
    refine ⟨70737625769702242164703247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47158417179801494776468831 70737625769702242164703247)
    ·
      refine ⟨106106438654553363247054871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70737625769702242164703247 106106438654553363247054871)
      ·
        refine ⟨159159657981830044870582307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106106438654553363247054871 159159657981830044870582307)
        ·
          refine ⟨238739486972745067305873461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159159657981830044870582307 238739486972745067305873461)
          ·
            refine ⟨22381826903694850059925637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 238739486972745067305873461 22381826903694850059925637)
            ·
              refine ⟨4196592544442784386236057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22381826903694850059925637 4196592544442784386236057)
              ·
                refine ⟨3147444408332088289677043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4196592544442784386236057 3147444408332088289677043)
                ·
                  refine ⟨4721166612498132434515565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3147444408332088289677043 4721166612498132434515565)
                  ·
                    refine ⟨1770437479686799662943337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4721166612498132434515565 1770437479686799662943337)
                    ·
                      refine ⟨1327828109765099747207503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1770437479686799662943337 1327828109765099747207503)
                      ·
                        rfl

theorem cell23_2585936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 2, 1, 3, 2].length) (baseStart_2585936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2585936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2585936 prefixEnd_2585936 := by exact prefixLift 2585936
  have htrace : WordTrace (prefixWord ++ tailWord_2585936) baseStart_2585936 baseEnd_2585936 := by
    simpa [prefixWord, tailWord_2585936, baseEnd_2585936] using wordTrace_append hprefix tailTrace_2585936
  have hstable : (prefixWord ++ tailWord_2585936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2585936).length < 2 ^ (prefixWord ++ tailWord_2585936).sum := by decide
  have hdescent : baseEnd_2585936 < baseStart_2585936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2585936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2585952 : List Nat := [2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 5]
def baseStart_2585952 : Nat := 118140960795 + 2585952 * 2 ^ 59
def prefixEnd_2585952 : Nat := 4983230072969 + 3 ^ 40 * 2585952 * 2
def baseEnd_2585952 : Nat := 1327836325455571684607429

theorem tailTrace_2585952 : CollatzResearch.WordTrace tailWord_2585952 prefixEnd_2585952 1327836325455571684607429 := by
  unfold tailWord_2585952
  simp only [CollatzResearch.WordTrace]
  refine ⟨47158708963772512142760055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62878278618363349523680073 47158708963772512142760055)
  ·
    refine ⟨70738063445658768214140083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47158708963772512142760055 70738063445658768214140083)
    ·
      refine ⟨106107095168488152321210125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70738063445658768214140083 106107095168488152321210125)
      ·
        refine ⟨39790160688183057120453797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106107095168488152321210125 39790160688183057120453797)
        ·
          refine ⟨7460655129034323210085087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39790160688183057120453797 7460655129034323210085087)
          ·
            refine ⟨11190982693551484815127631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7460655129034323210085087 11190982693551484815127631)
            ·
              refine ⟨16786474040327227222691447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11190982693551484815127631 16786474040327227222691447)
              ·
                refine ⟨25179711060490840834037171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16786474040327227222691447 25179711060490840834037171)
                ·
                  refine ⟨37769566590736261251055757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25179711060490840834037171 37769566590736261251055757)
                  ·
                    refine ⟨14163587471526097969145909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37769566590736261251055757 14163587471526097969145909)
                    ·
                      refine ⟨1327836325455571684607429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14163587471526097969145909 1327836325455571684607429)
                      ·
                        rfl

theorem cell23_2585952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 5].length) (baseStart_2585952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2585952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2585952 prefixEnd_2585952 := by exact prefixLift 2585952
  have htrace : WordTrace (prefixWord ++ tailWord_2585952) baseStart_2585952 baseEnd_2585952 := by
    simpa [prefixWord, tailWord_2585952, baseEnd_2585952] using wordTrace_append hprefix tailTrace_2585952
  have hstable : (prefixWord ++ tailWord_2585952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2585952).length < 2 ^ (prefixWord ++ tailWord_2585952).sum := by decide
  have hdescent : baseEnd_2585952 < baseStart_2585952 := by decide
  rcases family_descends (prefixWord ++ tailWord_2585952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2585986 : List Nat := [3, 4, 2, 1, 1, 1, 1, 2, 2, 1, 5]
def baseStart_2585986 : Nat := 118140960795 + 2585986 * 2 ^ 59
def prefixEnd_2585986 : Nat := 4983230072969 + 3 ^ 40 * 2585986 * 2
def baseEnd_2585986 : Nat := 1327853783797824551582273

theorem tailTrace_2585986 : CollatzResearch.WordTrace tailWord_2585986 prefixEnd_2585986 1327853783797824551582273 := by
  unfold tailWord_2585986
  simp only [CollatzResearch.WordTrace]
  refine ⟨23579664502355462023064453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62879105339614565394838541 23579664502355462023064453)
  ·
    refine ⟨4421187094191649129324585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23579664502355462023064453 4421187094191649129324585)
    ·
      refine ⟨3315890320643736846993439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4421187094191649129324585 3315890320643736846993439)
      ·
        refine ⟨4973835480965605270490159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3315890320643736846993439 4973835480965605270490159)
        ·
          refine ⟨7460753221448407905735239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4973835480965605270490159 7460753221448407905735239)
          ·
            refine ⟨11191129832172611858602859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7460753221448407905735239 11191129832172611858602859)
            ·
              refine ⟨16786694748258917787904289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11191129832172611858602859 16786694748258917787904289)
              ·
                refine ⟨12590021061194188340928217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16786694748258917787904289 12590021061194188340928217)
                ·
                  refine ⟨9442515795895641255696163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12590021061194188340928217 9442515795895641255696163)
                  ·
                    refine ⟨14163773693843461883544245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9442515795895641255696163 14163773693843461883544245)
                    ·
                      refine ⟨1327853783797824551582273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14163773693843461883544245 1327853783797824551582273)
                      ·
                        rfl

theorem cell23_2585986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_2585986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2585986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2585986 prefixEnd_2585986 := by exact prefixLift 2585986
  have htrace : WordTrace (prefixWord ++ tailWord_2585986) baseStart_2585986 baseEnd_2585986 := by
    simpa [prefixWord, tailWord_2585986, baseEnd_2585986] using wordTrace_append hprefix tailTrace_2585986
  have hstable : (prefixWord ++ tailWord_2585986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2585986).length < 2 ^ (prefixWord ++ tailWord_2585986).sum := by decide
  have hdescent : baseEnd_2585986 < baseStart_2585986 := by decide
  rcases family_descends (prefixWord ++ tailWord_2585986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2586083 : List Nat := [1, 1, 1, 6, 2, 1, 2, 4, 1, 4]
def baseStart_2586083 : Nat := 118140960795 + 2586083 * 2 ^ 59
def prefixEnd_2586083 : Nat := 4983230072969 + 3 ^ 40 * 2586083 * 2
def baseEnd_2586083 : Nat := 442634530473770224023109

theorem tailTrace_2586083 : CollatzResearch.WordTrace tailWord_2586083 prefixEnd_2586083 442634530473770224023109 := by
  unfold tailWord_2586083
  simp only [CollatzResearch.WordTrace]
  refine ⟨94322195890070433658538903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62881463926713622439025935 94322195890070433658538903)
  ·
    refine ⟨141483293835105650487808355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94322195890070433658538903 141483293835105650487808355)
    ·
      refine ⟨212224940752658475731712533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141483293835105650487808355 212224940752658475731712533)
      ·
        refine ⟨9948044097780866049924025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 212224940752658475731712533 9948044097780866049924025)
        ·
          refine ⟨7461033073335649537443019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9948044097780866049924025 7461033073335649537443019)
          ·
            refine ⟨11191549610003474306164529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7461033073335649537443019 11191549610003474306164529)
            ·
              refine ⟨8393662207502605729623397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11191549610003474306164529 8393662207502605729623397)
              ·
                refine ⟨1573811663906738574304387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8393662207502605729623397 1573811663906738574304387)
                ·
                  refine ⟨2360717495860107861456581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1573811663906738574304387 2360717495860107861456581)
                  ·
                    refine ⟨442634530473770224023109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2360717495860107861456581 442634530473770224023109)
                    ·
                      rfl

theorem cell23_2586083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 4, 1, 4].length) (baseStart_2586083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2586083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2586083 prefixEnd_2586083 := by exact prefixLift 2586083
  have htrace : WordTrace (prefixWord ++ tailWord_2586083) baseStart_2586083 baseEnd_2586083 := by
    simpa [prefixWord, tailWord_2586083, baseEnd_2586083] using wordTrace_append hprefix tailTrace_2586083
  have hstable : (prefixWord ++ tailWord_2586083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2586083).length < 2 ^ (prefixWord ++ tailWord_2586083).sum := by decide
  have hdescent : baseEnd_2586083 < baseStart_2586083 := by decide
  rcases family_descends (prefixWord ++ tailWord_2586083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2586092 : List Nat := [2, 2, 1, 1, 2, 1, 2, 1, 2, 9]
def baseStart_2586092 : Nat := 118140960795 + 2586092 * 2 ^ 59
def prefixEnd_2586092 : Nat := 4983230072969 + 3 ^ 40 * 2586092 * 2
def baseEnd_2586092 : Nat := 442636070915733712285595

theorem tailTrace_2586092 : CollatzResearch.WordTrace tailWord_2586092 prefixEnd_2586092 442636070915733712285595 := by
  unfold tailWord_2586092
  simp only [CollatzResearch.WordTrace]
  refine ⟨47161262073518914097808265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62881682764691885463744353 47161262073518914097808265)
  ·
    refine ⟨35370946555139185573356199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47161262073518914097808265 35370946555139185573356199)
    ·
      refine ⟨53056419832708778360034299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35370946555139185573356199 53056419832708778360034299)
      ·
        refine ⟨79584629749063167540051449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53056419832708778360034299 79584629749063167540051449)
        ·
          refine ⟨59688472311797375655038587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79584629749063167540051449 59688472311797375655038587)
          ·
            refine ⟨89532708467696063482557881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59688472311797375655038587 89532708467696063482557881)
            ·
              refine ⟨67149531350772047611918411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89532708467696063482557881 67149531350772047611918411)
              ·
                refine ⟨100724297026158071417877617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67149531350772047611918411 100724297026158071417877617)
                ·
                  refine ⟨75543222769618553563408213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 100724297026158071417877617 75543222769618553563408213)
                  ·
                    refine ⟨442636070915733712285595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 75543222769618553563408213 442636070915733712285595)
                    ·
                      rfl

theorem cell23_2586092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 9].length) (baseStart_2586092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2586092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2586092 prefixEnd_2586092 := by exact prefixLift 2586092
  have htrace : WordTrace (prefixWord ++ tailWord_2586092) baseStart_2586092 baseEnd_2586092 := by
    simpa [prefixWord, tailWord_2586092, baseEnd_2586092] using wordTrace_append hprefix tailTrace_2586092
  have hstable : (prefixWord ++ tailWord_2586092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2586092).length < 2 ^ (prefixWord ++ tailWord_2586092).sum := by decide
  have hdescent : baseEnd_2586092 < baseStart_2586092 := by decide
  rcases family_descends (prefixWord ++ tailWord_2586092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2586096 : List Nat := [2, 1, 1, 1, 3, 5, 3, 1, 6]
def baseStart_2586096 : Nat := 118140960795 + 2586096 * 2 ^ 59
def prefixEnd_2586096 : Nat := 4983230072969 + 3 ^ 40 * 2586096 * 2
def baseEnd_2586096 : Nat := 147545585185535457911863

theorem tailTrace_2586096 : CollatzResearch.WordTrace tailWord_2586096 prefixEnd_2586096 147545585185535457911863 := by
  unfold tailWord_2586096
  simp only [CollatzResearch.WordTrace]
  refine ⟨47161335019511668439381071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62881780026015557919174761 47161335019511668439381071)
  ·
    refine ⟨70742002529267502659071607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47161335019511668439381071 70742002529267502659071607)
    ·
      refine ⟨106113003793901253988607411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70742002529267502659071607 106113003793901253988607411)
      ·
        refine ⟨159169505690851880982911117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106113003793901253988607411 159169505690851880982911117)
        ·
          refine ⟨59688564634069455368591669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 159169505690851880982911117 59688564634069455368591669)
          ·
            refine ⟨5595802934444011440805469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 59688564634069455368591669 5595802934444011440805469)
            ·
              refine ⟨2098426100416504290302051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5595802934444011440805469 2098426100416504290302051)
              ·
                refine ⟨3147639150624756435453077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2098426100416504290302051 3147639150624756435453077)
                ·
                  refine ⟨147545585185535457911863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3147639150624756435453077 147545585185535457911863)
                  ·
                    rfl

theorem cell23_2586096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 3, 1, 6].length) (baseStart_2586096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2586096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2586096 prefixEnd_2586096 := by exact prefixLift 2586096
  have htrace : WordTrace (prefixWord ++ tailWord_2586096) baseStart_2586096 baseEnd_2586096 := by
    simpa [prefixWord, tailWord_2586096, baseEnd_2586096] using wordTrace_append hprefix tailTrace_2586096
  have hstable : (prefixWord ++ tailWord_2586096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2586096).length < 2 ^ (prefixWord ++ tailWord_2586096).sum := by decide
  have hdescent : baseEnd_2586096 < baseStart_2586096 := by decide
  rcases family_descends (prefixWord ++ tailWord_2586096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2586106 : List Nat := [3, 1, 1, 1, 1, 2, 3, 4, 3, 1, 3]
def baseStart_2586106 : Nat := 118140960795 + 2586106 * 2 ^ 59
def prefixEnd_2586106 : Nat := 4983230072969 + 3 ^ 40 * 2586106 * 2
def baseEnd_2586106 : Nat := 1327915401476364082081721

theorem tailTrace_2586106 : CollatzResearch.WordTrace tailWord_2586106 prefixEnd_2586106 1327915401476364082081721 := by
  unfold tailWord_2586106
  simp only [CollatzResearch.WordTrace]
  refine ⟨23580758692246777146656543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62882023179324739057750781 23580758692246777146656543)
  ·
    refine ⟨35371138038370165719984815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23580758692246777146656543 35371138038370165719984815)
    ·
      refine ⟨53056707057555248579977223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35371138038370165719984815 53056707057555248579977223)
      ·
        refine ⟨79585060586332872869965835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53056707057555248579977223 79585060586332872869965835)
        ·
          refine ⟨119377590879499309304948753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79585060586332872869965835 119377590879499309304948753)
          ·
            refine ⟨89533193159624481978711565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119377590879499309304948753 89533193159624481978711565)
            ·
              refine ⟨33574947434859180742016837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89533193159624481978711565 33574947434859180742016837)
              ·
                refine ⟨6295302644036096389128157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33574947434859180742016837 6295302644036096389128157)
                ·
                  refine ⟨2360738491513536145923059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6295302644036096389128157 2360738491513536145923059)
                  ·
                    refine ⟨3541107737270304218884589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2360738491513536145923059 3541107737270304218884589)
                    ·
                      refine ⟨1327915401476364082081721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3541107737270304218884589 1327915401476364082081721)
                      ·
                        rfl

theorem cell23_2586106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 4, 3, 1, 3].length) (baseStart_2586106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2586106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2586106 prefixEnd_2586106 := by exact prefixLift 2586106
  have htrace : WordTrace (prefixWord ++ tailWord_2586106) baseStart_2586106 baseEnd_2586106 := by
    simpa [prefixWord, tailWord_2586106, baseEnd_2586106] using wordTrace_append hprefix tailTrace_2586106
  have hstable : (prefixWord ++ tailWord_2586106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2586106).length < 2 ^ (prefixWord ++ tailWord_2586106).sum := by decide
  have hdescent : baseEnd_2586106 < baseStart_2586106 := by decide
  rcases family_descends (prefixWord ++ tailWord_2586106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2586133 : List Nat := [1, 3, 2, 1, 3, 3, 1, 2, 2, 3, 2]
def baseStart_2586133 : Nat := 118140960795 + 2586133 * 2 ^ 59
def prefixEnd_2586133 : Nat := 4983230072969 + 3 ^ 40 * 2586133 * 2
def baseEnd_2586133 : Nat := 1327929265454035476444097

theorem tailTrace_2586133 : CollatzResearch.WordTrace tailWord_2586133 prefixEnd_2586133 1327929265454035476444097 := by
  unfold tailWord_2586133
  simp only [CollatzResearch.WordTrace]
  refine ⟨94324019539889292197859053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62882679693259528131906035 94324019539889292197859053)
  ·
    refine ⟨35371507327458484574197145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94324019539889292197859053 35371507327458484574197145)
    ·
      refine ⟨26528630495593863430647859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35371507327458484574197145 26528630495593863430647859)
      ·
        refine ⟨39792945743390795145971789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26528630495593863430647859 39792945743390795145971789)
        ·
          refine ⟨14922354653771548179739421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39792945743390795145971789 14922354653771548179739421)
          ·
            refine ⟨5595882995164330567402283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14922354653771548179739421 5595882995164330567402283)
            ·
              refine ⟨8393824492746495851103425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5595882995164330567402283 8393824492746495851103425)
              ·
                refine ⟨6295368369559871888327569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8393824492746495851103425 6295368369559871888327569)
                ·
                  refine ⟨4721526277169903916245677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6295368369559871888327569 4721526277169903916245677)
                  ·
                    refine ⟨1770572353938713968592129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4721526277169903916245677 1770572353938713968592129)
                    ·
                      refine ⟨1327929265454035476444097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1770572353938713968592129 1327929265454035476444097)
                      ·
                        rfl

theorem cell23_2586133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 2, 2, 3, 2].length) (baseStart_2586133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2586133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2586133 prefixEnd_2586133 := by exact prefixLift 2586133
  have htrace : WordTrace (prefixWord ++ tailWord_2586133) baseStart_2586133 baseEnd_2586133 := by
    simpa [prefixWord, tailWord_2586133, baseEnd_2586133] using wordTrace_append hprefix tailTrace_2586133
  have hstable : (prefixWord ++ tailWord_2586133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2586133).length < 2 ^ (prefixWord ++ tailWord_2586133).sum := by decide
  have hdescent : baseEnd_2586133 < baseStart_2586133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2586133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2586149 : List Nat := [1, 3, 1, 2, 2, 1, 1, 1, 2, 6, 3]
def baseStart_2586149 : Nat := 118140960795 + 2586149 * 2 ^ 59
def prefixEnd_2586149 : Nat := 4983230072969 + 3 ^ 40 * 2586149 * 2
def baseEnd_2586149 : Nat := 1327937481144507413844023

theorem tailTrace_2586149 : CollatzResearch.WordTrace tailWord_2586149 prefixEnd_2586149 1327937481144507413844023 := by
  unfold tailWord_2586149
  simp only [CollatzResearch.WordTrace]
  refine ⟨94324603107831326930441501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62883068738554217953627667 94324603107831326930441501)
  ·
    refine ⟨35371726165436747598915563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94324603107831326930441501 35371726165436747598915563)
    ·
      refine ⟨53057589248155121398373345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35371726165436747598915563 53057589248155121398373345)
      ·
        refine ⟨39793191936116341048780009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53057589248155121398373345 39793191936116341048780009)
        ·
          refine ⟨29844893952087255786585007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39793191936116341048780009 29844893952087255786585007)
          ·
            refine ⟨44767340928130883679877511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29844893952087255786585007 44767340928130883679877511)
            ·
              refine ⟨67151011392196325519816267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44767340928130883679877511 67151011392196325519816267)
              ·
                refine ⟨100726517088294488279724401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67151011392196325519816267 100726517088294488279724401)
                ·
                  refine ⟨75544887816220866209793301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 100726517088294488279724401 75544887816220866209793301)
                  ·
                    refine ⟨3541166616385353103584061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 75544887816220866209793301 3541166616385353103584061)
                    ·
                      refine ⟨1327937481144507413844023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3541166616385353103584061 1327937481144507413844023)
                      ·
                        rfl

theorem cell23_2586149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 6, 3].length) (baseStart_2586149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2586149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2586149 prefixEnd_2586149 := by exact prefixLift 2586149
  have htrace : WordTrace (prefixWord ++ tailWord_2586149) baseStart_2586149 baseEnd_2586149 := by
    simpa [prefixWord, tailWord_2586149, baseEnd_2586149] using wordTrace_append hprefix tailTrace_2586149
  have hstable : (prefixWord ++ tailWord_2586149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2586149).length < 2 ^ (prefixWord ++ tailWord_2586149).sum := by decide
  have hdescent : baseEnd_2586149 < baseStart_2586149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2586149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2586163 : List Nat := [1, 1, 1, 2, 4, 5, 1, 2, 1, 1, 4]
def baseStart_2586163 : Nat := 118140960795 + 2586163 * 2 ^ 59
def prefixEnd_2586163 : Nat := 4983230072969 + 3 ^ 40 * 2586163 * 2
def baseEnd_2586163 : Nat := 1327944669873670359068959

theorem tailTrace_2586163 : CollatzResearch.WordTrace tailWord_2586163 prefixEnd_2586163 1327944669873670359068959 := by
  unfold tailWord_2586163
  simp only [CollatzResearch.WordTrace]
  refine ⟨94325113729780607321451143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62883409153187071547634095 94325113729780607321451143)
  ·
    refine ⟨141487670594670910982176715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94325113729780607321451143 141487670594670910982176715)
    ·
      refine ⟨212231505892006366473265073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141487670594670910982176715 212231505892006366473265073)
      ·
        refine ⟨159173629419004774854948805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212231505892006366473265073 159173629419004774854948805)
        ·
          refine ⟨29845055516063395285302901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 159173629419004774854948805 29845055516063395285302901)
          ·
            refine ⟨2797973954630943307997147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29845055516063395285302901 2797973954630943307997147)
            ·
              refine ⟨4196960931946414961995721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2797973954630943307997147 4196960931946414961995721)
              ·
                refine ⟨3147720698959811221496791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4196960931946414961995721 3147720698959811221496791)
                ·
                  refine ⟨4721581048439716832245187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3147720698959811221496791 4721581048439716832245187)
                  ·
                    refine ⟨7082371572659575248367781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4721581048439716832245187 7082371572659575248367781)
                    ·
                      refine ⟨1327944669873670359068959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7082371572659575248367781 1327944669873670359068959)
                      ·
                        rfl

theorem cell23_2586163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 2, 1, 1, 4].length) (baseStart_2586163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2586163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2586163 prefixEnd_2586163 := by exact prefixLift 2586163
  have htrace : WordTrace (prefixWord ++ tailWord_2586163) baseStart_2586163 baseEnd_2586163 := by
    simpa [prefixWord, tailWord_2586163, baseEnd_2586163] using wordTrace_append hprefix tailTrace_2586163
  have hstable : (prefixWord ++ tailWord_2586163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2586163).length < 2 ^ (prefixWord ++ tailWord_2586163).sum := by decide
  have hdescent : baseEnd_2586163 < baseStart_2586163 := by decide
  rcases family_descends (prefixWord ++ tailWord_2586163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2586169 : List Nat := [1, 2, 1, 5, 1, 2, 2, 9]
def baseStart_2586169 : Nat := 118140960795 + 2586169 * 2 ^ 59
def prefixEnd_2586169 : Nat := 4983230072969 + 3 ^ 40 * 2586169 * 2
def baseEnd_2586169 : Nat := 49183250028059160577553

theorem tailTrace_2586169 : CollatzResearch.WordTrace tailWord_2586169 prefixEnd_2586169 49183250028059160577553 := by
  unfold tailWord_2586169
  simp only [CollatzResearch.WordTrace]
  refine ⟨94325332567758870346169561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62883555045172580230779707 94325332567758870346169561)
  ·
    refine ⟨70743999425819152759627171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94325332567758870346169561 70743999425819152759627171)
    ·
      refine ⟨106115999138728729139440757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70743999425819152759627171 106115999138728729139440757)
      ·
        refine ⟨9948374919255818356822571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 106115999138728729139440757 9948374919255818356822571)
        ·
          refine ⟨14922562378883727535233857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9948374919255818356822571 14922562378883727535233857)
          ·
            refine ⟨11191921784162795651425393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14922562378883727535233857 11191921784162795651425393)
            ·
              refine ⟨8393941338122096738569045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11191921784162795651425393 8393941338122096738569045)
              ·
                refine ⟨49183250028059160577553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8393941338122096738569045 49183250028059160577553)
                ·
                  rfl

theorem cell23_2586169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 9].length) (baseStart_2586169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2586169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2586169 prefixEnd_2586169 := by exact prefixLift 2586169
  have htrace : WordTrace (prefixWord ++ tailWord_2586169) baseStart_2586169 baseEnd_2586169 := by
    simpa [prefixWord, tailWord_2586169, baseEnd_2586169] using wordTrace_append hprefix tailTrace_2586169
  have hstable : (prefixWord ++ tailWord_2586169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2586169).length < 2 ^ (prefixWord ++ tailWord_2586169).sum := by decide
  have hdescent : baseEnd_2586169 < baseStart_2586169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2586169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2586183 : List Nat := [1, 1, 4, 1, 5, 2, 1, 1, 1, 1, 5]
def baseStart_2586183 : Nat := 118140960795 + 2586183 * 2 ^ 59
def prefixEnd_2586183 : Nat := 4983230072969 + 3 ^ 40 * 2586183 * 2
def baseEnd_2586183 : Nat := 1327954939486760280818867

theorem tailTrace_2586183 : CollatzResearch.WordTrace tailWord_2586183 prefixEnd_2586183 1327954939486760280818867 := by
  unfold tailWord_2586183
  simp only [CollatzResearch.WordTrace]
  refine ⟨94325843189708150737179203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62883895459805433824786135 94325843189708150737179203)
  ·
    refine ⟨141488764784562226105768805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94325843189708150737179203 141488764784562226105768805)
    ·
      refine ⟨26529143397105417394831651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 141488764784562226105768805 26529143397105417394831651)
      ·
        refine ⟨39793715095658126092247477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26529143397105417394831651 39793715095658126092247477)
        ·
          refine ⟨3730660790217949321148201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39793715095658126092247477 3730660790217949321148201)
          ·
            refine ⟨2797995592663461990861151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3730660790217949321148201 2797995592663461990861151)
            ·
              refine ⟨4196993388995192986291727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2797995592663461990861151 4196993388995192986291727)
              ·
                refine ⟨6295490083492789479437591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4196993388995192986291727 6295490083492789479437591)
                ·
                  refine ⟨9443235125239184219156387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6295490083492789479437591 9443235125239184219156387)
                  ·
                    refine ⟨14164852687858776328734581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9443235125239184219156387 14164852687858776328734581)
                    ·
                      refine ⟨1327954939486760280818867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14164852687858776328734581 1327954939486760280818867)
                      ·
                        rfl

theorem cell23_2586183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 1, 1, 1, 5].length) (baseStart_2586183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2586183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2586183 prefixEnd_2586183 := by exact prefixLift 2586183
  have htrace : WordTrace (prefixWord ++ tailWord_2586183) baseStart_2586183 baseEnd_2586183 := by
    simpa [prefixWord, tailWord_2586183, baseEnd_2586183] using wordTrace_append hprefix tailTrace_2586183
  have hstable : (prefixWord ++ tailWord_2586183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2586183).length < 2 ^ (prefixWord ++ tailWord_2586183).sum := by decide
  have hdescent : baseEnd_2586183 < baseStart_2586183 := by decide
  rcases family_descends (prefixWord ++ tailWord_2586183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2586196 : List Nat := [2, 4, 1, 1, 1, 2, 1, 2, 3, 3, 3]
def baseStart_2586196 : Nat := 118140960795 + 2586196 * 2 ^ 59
def prefixEnd_2586196 : Nat := 4983230072969 + 3 ^ 40 * 2586196 * 2
def baseEnd_2586196 : Nat := 1327961614735268729956307

theorem tailTrace_2586196 : CollatzResearch.WordTrace tailWord_2586196 prefixEnd_2586196 1327961614735268729956307 := by
  unfold tailWord_2586196
  simp only [CollatzResearch.WordTrace]
  refine ⟨47163158669330526978701221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62884211559107369304934961 47163158669330526978701221)
  ·
    refine ⟨8843092250499473808506479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47163158669330526978701221 8843092250499473808506479)
    ·
      refine ⟨13264638375749210712759719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8843092250499473808506479 13264638375749210712759719)
      ·
        refine ⟨19896957563623816069139579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13264638375749210712759719 19896957563623816069139579)
        ·
          refine ⟨29845436345435724103709369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19896957563623816069139579 29845436345435724103709369)
          ·
            refine ⟨22384077259076793077782027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29845436345435724103709369 22384077259076793077782027)
            ·
              refine ⟨33576115888615189616673041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22384077259076793077782027 33576115888615189616673041)
              ·
                refine ⟨25182086916461392212504781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33576115888615189616673041 25182086916461392212504781)
                ·
                  refine ⟨9443282593673022079689293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25182086916461392212504781 9443282593673022079689293)
                  ·
                    refine ⟨3541230972627383279883485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9443282593673022079689293 3541230972627383279883485)
                    ·
                      refine ⟨1327961614735268729956307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3541230972627383279883485 1327961614735268729956307)
                      ·
                        rfl

theorem cell23_2586196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 3, 3, 3].length) (baseStart_2586196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2586196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2586196 prefixEnd_2586196 := by exact prefixLift 2586196
  have htrace : WordTrace (prefixWord ++ tailWord_2586196) baseStart_2586196 baseEnd_2586196 := by
    simpa [prefixWord, tailWord_2586196, baseEnd_2586196] using wordTrace_append hprefix tailTrace_2586196
  have hstable : (prefixWord ++ tailWord_2586196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2586196).length < 2 ^ (prefixWord ++ tailWord_2586196).sum := by decide
  have hdescent : baseEnd_2586196 < baseStart_2586196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2586196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2586199 : List Nat := [1, 1, 3, 2, 2, 3, 1, 1, 2, 7]
def baseStart_2586199 : Nat := 118140960795 + 2586199 * 2 ^ 59
def prefixEnd_2586199 : Nat := 4983230072969 + 3 ^ 40 * 2586199 * 2
def baseEnd_2586199 : Nat := 442654385059077406072931

theorem tailTrace_2586199 : CollatzResearch.WordTrace tailWord_2586199 prefixEnd_2586199 442654385059077406072931 := by
  unfold tailWord_2586199
  simp only [CollatzResearch.WordTrace]
  refine ⟨94326426757650185469761651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62884284505100123646507767 94326426757650185469761651)
  ·
    refine ⟨141489640136475278204642477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94326426757650185469761651 141489640136475278204642477)
    ·
      refine ⟨53058615051178229326740929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141489640136475278204642477 53058615051178229326740929)
      ·
        refine ⟨39793961288383671995055697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53058615051178229326740929 39793961288383671995055697)
        ·
          refine ⟨29845470966287753996291773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39793961288383671995055697 29845470966287753996291773)
          ·
            refine ⟨11192051612357907748609415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29845470966287753996291773 11192051612357907748609415)
            ·
              refine ⟨16788077418536861622914123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11192051612357907748609415 16788077418536861622914123)
              ·
                refine ⟨25182116127805292434371185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16788077418536861622914123 25182116127805292434371185)
                ·
                  refine ⟨18886587095853969325778389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25182116127805292434371185 18886587095853969325778389)
                  ·
                    refine ⟨442654385059077406072931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18886587095853969325778389 442654385059077406072931)
                    ·
                      rfl

theorem cell23_2586199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 2, 7].length) (baseStart_2586199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2586199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2586199 prefixEnd_2586199 := by exact prefixLift 2586199
  have htrace : WordTrace (prefixWord ++ tailWord_2586199) baseStart_2586199 baseEnd_2586199 := by
    simpa [prefixWord, tailWord_2586199, baseEnd_2586199] using wordTrace_append hprefix tailTrace_2586199
  have hstable : (prefixWord ++ tailWord_2586199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2586199).length < 2 ^ (prefixWord ++ tailWord_2586199).sum := by decide
  have hdescent : baseEnd_2586199 < baseStart_2586199 := by decide
  rcases family_descends (prefixWord ++ tailWord_2586199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2586213 : List Nat := [1, 3, 1, 3, 3, 2, 2, 1, 1, 3, 3]
def baseStart_2586213 : Nat := 118140960795 + 2586213 * 2 ^ 59
def prefixEnd_2586213 : Nat := 4983230072969 + 3 ^ 40 * 2586213 * 2
def baseEnd_2586213 : Nat := 1327970343906395163443729

theorem tailTrace_2586213 : CollatzResearch.WordTrace tailWord_2586213 prefixEnd_2586213 1327970343906395163443729 := by
  unfold tailWord_2586213
  simp only [CollatzResearch.WordTrace]
  refine ⟨94326937379599465860771293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62884624919732977240514195 94326937379599465860771293)
  ·
    refine ⟨35372601517349799697789235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94326937379599465860771293 35372601517349799697789235)
    ·
      refine ⟨53058902276024699546683853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35372601517349799697789235 53058902276024699546683853)
      ·
        refine ⟨19897088353509262330006445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53058902276024699546683853 19897088353509262330006445)
        ·
          refine ⟨7461408132565973373752417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19897088353509262330006445 7461408132565973373752417)
          ·
            refine ⟨5596056099424480030314313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7461408132565973373752417 5596056099424480030314313)
            ·
              refine ⟨4197042074568360022735735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5596056099424480030314313 4197042074568360022735735)
              ·
                refine ⟨6295563111852540034103603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4197042074568360022735735 6295563111852540034103603)
                ·
                  refine ⟨9443344667778810051155405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6295563111852540034103603 9443344667778810051155405)
                  ·
                    refine ⟨3541254250417053769183277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9443344667778810051155405 3541254250417053769183277)
                    ·
                      refine ⟨1327970343906395163443729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3541254250417053769183277 1327970343906395163443729)
                      ·
                        rfl

theorem cell23_2586213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 1, 1, 3, 3].length) (baseStart_2586213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2586213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2586213 prefixEnd_2586213 := by exact prefixLift 2586213
  have htrace : WordTrace (prefixWord ++ tailWord_2586213) baseStart_2586213 baseEnd_2586213 := by
    simpa [prefixWord, tailWord_2586213, baseEnd_2586213] using wordTrace_append hprefix tailTrace_2586213
  have hstable : (prefixWord ++ tailWord_2586213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2586213).length < 2 ^ (prefixWord ++ tailWord_2586213).sum := by decide
  have hdescent : baseEnd_2586213 < baseStart_2586213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2586213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2586223 : List Nat := [1, 1, 2, 1, 3, 2, 1, 6, 1, 3, 2]
def baseStart_2586223 : Nat := 118140960795 + 2586223 * 2 ^ 59
def prefixEnd_2586223 : Nat := 4983230072969 + 3 ^ 40 * 2586223 * 2
def baseEnd_2586223 : Nat := 1327975478712940124318683

theorem tailTrace_2586223 : CollatzResearch.WordTrace tailWord_2586223 prefixEnd_2586223 1327975478712940124318683 := by
  unfold tailWord_2586223
  simp only [CollatzResearch.WordTrace]
  refine ⟨94327302109563237568635323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62884868073042158379090215 94327302109563237568635323)
  ·
    refine ⟨141490953164344856352952985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94327302109563237568635323 141490953164344856352952985)
    ·
      refine ⟨106118214873258642264714739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141490953164344856352952985 106118214873258642264714739)
      ·
        refine ⟨159177322309887963397072109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106118214873258642264714739 159177322309887963397072109)
        ·
          refine ⟨59691495866207986273902041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 159177322309887963397072109 59691495866207986273902041)
          ·
            refine ⟨44768621899655989705426531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59691495866207986273902041 44768621899655989705426531)
            ·
              refine ⟨67152932849483984558139797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44768621899655989705426531 67152932849483984558139797)
              ·
                refine ⟨3147793727319561776162803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 67152932849483984558139797 3147793727319561776162803)
                ·
                  refine ⟨4721690590979342664244205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3147793727319561776162803 4721690590979342664244205)
                  ·
                    refine ⟨1770633971617253499091577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4721690590979342664244205 1770633971617253499091577)
                    ·
                      refine ⟨1327975478712940124318683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1770633971617253499091577 1327975478712940124318683)
                      ·
                        rfl

theorem cell23_2586223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 6, 1, 3, 2].length) (baseStart_2586223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2586223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2586223 prefixEnd_2586223 := by exact prefixLift 2586223
  have htrace : WordTrace (prefixWord ++ tailWord_2586223) baseStart_2586223 baseEnd_2586223 := by
    simpa [prefixWord, tailWord_2586223, baseEnd_2586223] using wordTrace_append hprefix tailTrace_2586223
  have hstable : (prefixWord ++ tailWord_2586223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2586223).length < 2 ^ (prefixWord ++ tailWord_2586223).sum := by decide
  have hdescent : baseEnd_2586223 < baseStart_2586223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2586223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2586239 : List Nat := [1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 5]
def baseStart_2586239 : Nat := 118140960795 + 2586239 * 2 ^ 59
def prefixEnd_2586239 : Nat := 4983230072969 + 3 ^ 40 * 2586239 * 2
def baseEnd_2586239 : Nat := 1327983694403412061718609

theorem tailTrace_2586239 : CollatzResearch.WordTrace tailWord_2586239 prefixEnd_2586239 1327983694403412061718609 := by
  unfold tailWord_2586239
  simp only [CollatzResearch.WordTrace]
  refine ⟨94327885677505272301217771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62885257118336848200811847 94327885677505272301217771)
  ·
    refine ⟨141491828516257908451826657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94327885677505272301217771 141491828516257908451826657)
    ·
      refine ⟨106118871387193431338869993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141491828516257908451826657 106118871387193431338869993)
      ·
        refine ⟨79589153540395073504152495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106118871387193431338869993 79589153540395073504152495)
        ·
          refine ⟨119383730310592610256228743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79589153540395073504152495 119383730310592610256228743)
          ·
            refine ⟨179075595465888915384343115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119383730310592610256228743 179075595465888915384343115)
            ·
              refine ⟨268613393198833373076514673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 179075595465888915384343115 268613393198833373076514673)
              ·
                refine ⟨201460044899125029807386005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 268613393198833373076514673 201460044899125029807386005)
                ·
                  refine ⟨9443439604646485772221219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 201460044899125029807386005 9443439604646485772221219)
                  ·
                    refine ⟨14165159406969728658331829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9443439604646485772221219 14165159406969728658331829)
                    ·
                      refine ⟨1327983694403412061718609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14165159406969728658331829 1327983694403412061718609)
                      ·
                        rfl

theorem cell23_2586239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 5].length) (baseStart_2586239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2586239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2586239 prefixEnd_2586239 := by exact prefixLift 2586239
  have htrace : WordTrace (prefixWord ++ tailWord_2586239) baseStart_2586239 baseEnd_2586239 := by
    simpa [prefixWord, tailWord_2586239, baseEnd_2586239] using wordTrace_append hprefix tailTrace_2586239
  have hstable : (prefixWord ++ tailWord_2586239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2586239).length < 2 ^ (prefixWord ++ tailWord_2586239).sum := by decide
  have hdescent : baseEnd_2586239 < baseStart_2586239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2586239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2586274 : List Nat := [3, 3, 1, 4, 1, 1, 2, 2, 1, 3, 2]
def baseStart_2586274 : Nat := 118140960795 + 2586274 * 2 ^ 59
def prefixEnd_2586274 : Nat := 4983230072969 + 3 ^ 40 * 2586274 * 2
def baseEnd_2586274 : Nat := 1328001666226319424780949

theorem tailTrace_2586274 : CollatzResearch.WordTrace tailWord_2586274 prefixEnd_2586274 1328001666226319424780949 := by
  unfold tailWord_2586274
  simp only [CollatzResearch.WordTrace]
  refine ⟨23582290558094618319685469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62886108154918982185827917 23582290558094618319685469)
  ·
    refine ⟨8843358959285481869882051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23582290558094618319685469 8843358959285481869882051)
    ·
      refine ⟨13265038438928222804823077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8843358959285481869882051 13265038438928222804823077)
      ·
        refine ⟨2487194707299041775904327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13265038438928222804823077 2487194707299041775904327)
        ·
          refine ⟨3730792060948562663856491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2487194707299041775904327 3730792060948562663856491)
          ·
            refine ⟨5596188091422843995784737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3730792060948562663856491 5596188091422843995784737)
            ·
              refine ⟨4197141068567132996838553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5596188091422843995784737 4197141068567132996838553)
              ·
                refine ⟨3147855801425349747628915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4197141068567132996838553 3147855801425349747628915)
                ·
                  refine ⟨4721783702138024621443373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3147855801425349747628915 4721783702138024621443373)
                  ·
                    refine ⟨1770668888301759233041265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4721783702138024621443373 1770668888301759233041265)
                    ·
                      refine ⟨1328001666226319424780949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1770668888301759233041265 1328001666226319424780949)
                      ·
                        rfl

theorem cell23_2586274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_2586274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2586274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2586274 prefixEnd_2586274 := by exact prefixLift 2586274
  have htrace : WordTrace (prefixWord ++ tailWord_2586274) baseStart_2586274 baseEnd_2586274 := by
    simpa [prefixWord, tailWord_2586274, baseEnd_2586274] using wordTrace_append hprefix tailTrace_2586274
  have hstable : (prefixWord ++ tailWord_2586274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2586274).length < 2 ^ (prefixWord ++ tailWord_2586274).sum := by decide
  have hdescent : baseEnd_2586274 < baseStart_2586274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2586274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2586276 : List Nat := [2, 3, 1, 2, 2, 2, 2, 2, 7]
def baseStart_2586276 : Nat := 118140960795 + 2586276 * 2 ^ 59
def prefixEnd_2586276 : Nat := 4983230072969 + 3 ^ 40 * 2586276 * 2
def baseEnd_2586276 : Nat := 147555854798625379661771

theorem tailTrace_2586276 : CollatzResearch.WordTrace tailWord_2586276 prefixEnd_2586276 147555854798625379661771 := by
  unfold tailWord_2586276
  simp only [CollatzResearch.WordTrace]
  refine ⟨47164617589185613810157341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62886156785580818413543121 47164617589185613810157341)
  ·
    refine ⟨17686731595944605178809003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47164617589185613810157341 17686731595944605178809003)
    ·
      refine ⟨26530097393916907768213505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17686731595944605178809003 26530097393916907768213505)
      ·
        refine ⟨19897573045437680826160129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26530097393916907768213505 19897573045437680826160129)
        ·
          refine ⟨14923179784078260619620097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19897573045437680826160129 14923179784078260619620097)
          ·
            refine ⟨11192384838058695464715073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14923179784078260619620097 11192384838058695464715073)
            ·
              refine ⟨8394288628544021598536305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11192384838058695464715073 8394288628544021598536305)
              ·
                refine ⟨6295716471408016198902229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8394288628544021598536305 6295716471408016198902229)
                ·
                  refine ⟨147555854798625379661771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6295716471408016198902229 147555854798625379661771)
                  ·
                    rfl

theorem cell23_2586276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 2, 7].length) (baseStart_2586276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2586276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2586276 prefixEnd_2586276 := by exact prefixLift 2586276
  have htrace : WordTrace (prefixWord ++ tailWord_2586276) baseStart_2586276 baseEnd_2586276 := by
    simpa [prefixWord, tailWord_2586276, baseEnd_2586276] using wordTrace_append hprefix tailTrace_2586276
  have hstable : (prefixWord ++ tailWord_2586276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2586276).length < 2 ^ (prefixWord ++ tailWord_2586276).sum := by decide
  have hdescent : baseEnd_2586276 < baseStart_2586276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2586276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2586299 : List Nat := [1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 7]
def baseStart_2586299 : Nat := 118140960795 + 2586299 * 2 ^ 59
def prefixEnd_2586299 : Nat := 4983230072969 + 3 ^ 40 * 2586299 * 2
def baseEnd_2586299 : Nat := 1328014503242681826968333

theorem tailTrace_2586299 : CollatzResearch.WordTrace tailWord_2586299 prefixEnd_2586299 1328014503242681826968333 := by
  unfold tailWord_2586299
  simp only [CollatzResearch.WordTrace]
  refine ⟨94330074057287902548401951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62886716038191935032267967 94330074057287902548401951)
  ·
    refine ⟨141495111085931853822602927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94330074057287902548401951 141495111085931853822602927)
    ·
      refine ⟨212242666628897780733904391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141495111085931853822602927 212242666628897780733904391)
      ·
        refine ⟨318363999943346671100856587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212242666628897780733904391 318363999943346671100856587)
        ·
          refine ⟨477545999915020006651284881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 318363999943346671100856587 477545999915020006651284881)
          ·
            refine ⟨358159499936265004988463661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 477545999915020006651284881 358159499936265004988463661)
            ·
              refine ⟨134309812476099376870673873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 358159499936265004988463661 134309812476099376870673873)
              ·
                refine ⟨100732359357074532653005405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 134309812476099376870673873 100732359357074532653005405)
                ·
                  refine ⟨37774634758902949744877027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 100732359357074532653005405 37774634758902949744877027)
                  ·
                    refine ⟨56661952138354424617315541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37774634758902949744877027 56661952138354424617315541)
                    ·
                      refine ⟨1328014503242681826968333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 56661952138354424617315541 1328014503242681826968333)
                      ·
                        rfl

theorem cell23_2586299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 7].length) (baseStart_2586299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2586299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2586299 prefixEnd_2586299 := by exact prefixLift 2586299
  have htrace : WordTrace (prefixWord ++ tailWord_2586299) baseStart_2586299 baseEnd_2586299 := by
    simpa [prefixWord, tailWord_2586299, baseEnd_2586299] using wordTrace_append hprefix tailTrace_2586299
  have hstable : (prefixWord ++ tailWord_2586299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2586299).length < 2 ^ (prefixWord ++ tailWord_2586299).sum := by decide
  have hdescent : baseEnd_2586299 < baseStart_2586299 := by decide
  rcases family_descends (prefixWord ++ tailWord_2586299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2586370 : List Nat := [3, 4, 1, 1, 1, 1, 2, 3, 3, 4]
def baseStart_2586370 : Nat := 118140960795 + 2586370 * 2 ^ 59
def prefixEnd_2586370 : Nat := 4983230072969 + 3 ^ 40 * 2586370 * 2
def baseEnd_2586370 : Nat := 442683653456383683060169

theorem tailTrace_2586370 : CollatzResearch.WordTrace tailWord_2586370 prefixEnd_2586370 442683653456383683060169 := by
  unfold tailWord_2586370
  simp only [CollatzResearch.WordTrace]
  refine ⟨23583165910007670418559141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62888442426687121116157709 23583165910007670418559141)
  ·
    refine ⟨4421843608126438203479839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23583165910007670418559141 4421843608126438203479839)
    ·
      refine ⟨6632765412189657305219759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4421843608126438203479839 6632765412189657305219759)
      ·
        refine ⟨9949148118284485957829639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6632765412189657305219759 9949148118284485957829639)
        ·
          refine ⟨14923722177426728936744459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9949148118284485957829639 14923722177426728936744459)
          ·
            refine ⟨22385583266140093405116689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14923722177426728936744459 22385583266140093405116689)
            ·
              refine ⟨16789187449605070053837517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22385583266140093405116689 16789187449605070053837517)
              ·
                refine ⟨6295945293601901270189069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16789187449605070053837517 6295945293601901270189069)
                ·
                  refine ⟨2360979485100712976320901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6295945293601901270189069 2360979485100712976320901)
                  ·
                    refine ⟨442683653456383683060169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2360979485100712976320901 442683653456383683060169)
                    ·
                      rfl

theorem cell23_2586370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_2586370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2586370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2586370 prefixEnd_2586370 := by exact prefixLift 2586370
  have htrace : WordTrace (prefixWord ++ tailWord_2586370) baseStart_2586370 baseEnd_2586370 := by
    simpa [prefixWord, tailWord_2586370, baseEnd_2586370] using wordTrace_append hprefix tailTrace_2586370
  have hstable : (prefixWord ++ tailWord_2586370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2586370).length < 2 ^ (prefixWord ++ tailWord_2586370).sum := by decide
  have hdescent : baseEnd_2586370 < baseStart_2586370 := by decide
  rcases family_descends (prefixWord ++ tailWord_2586370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2586450 : List Nat := [3, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4]
def baseStart_2586450 : Nat := 118140960795 + 2586450 * 2 ^ 59
def prefixEnd_2586450 : Nat := 4983230072969 + 3 ^ 40 * 2586450 * 2
def baseEnd_2586450 : Nat := 1328092038821510736180139

theorem tailTrace_2586450 : CollatzResearch.WordTrace tailWord_2586450 prefixEnd_2586450 1328092038821510736180139 := by
  unfold tailWord_2586450
  simp only [CollatzResearch.WordTrace]
  refine ⟨23583895369935213834287201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62890387653160570224765869 23583895369935213834287201)
  ·
    refine ⟨17687921527451410375715401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23583895369935213834287201 17687921527451410375715401)
    ·
      refine ⟨13265941145588557781786551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17687921527451410375715401 13265941145588557781786551)
      ·
        refine ⟨19898911718382836672679827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13265941145588557781786551 19898911718382836672679827)
        ·
          refine ⟨29848367577574255009019741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19898911718382836672679827 29848367577574255009019741)
          ·
            refine ⟨11193137841590345628382403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29848367577574255009019741 11193137841590345628382403)
            ·
              refine ⟨16789706762385518442573605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11193137841590345628382403 16789706762385518442573605)
              ·
                refine ⟨3148070017947284707982551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16789706762385518442573605 3148070017947284707982551)
                ·
                  refine ⟨4722105026920927061973827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3148070017947284707982551 4722105026920927061973827)
                  ·
                    refine ⟨7083157540381390592960741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4722105026920927061973827 7083157540381390592960741)
                    ·
                      refine ⟨1328092038821510736180139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7083157540381390592960741 1328092038821510736180139)
                      ·
                        rfl

theorem cell23_2586450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4].length) (baseStart_2586450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2586450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2586450 prefixEnd_2586450 := by exact prefixLift 2586450
  have htrace : WordTrace (prefixWord ++ tailWord_2586450) baseStart_2586450 baseEnd_2586450 := by
    simpa [prefixWord, tailWord_2586450, baseEnd_2586450] using wordTrace_append hprefix tailTrace_2586450
  have hstable : (prefixWord ++ tailWord_2586450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2586450).length < 2 ^ (prefixWord ++ tailWord_2586450).sum := by decide
  have hdescent : baseEnd_2586450 < baseStart_2586450 := by decide
  rcases family_descends (prefixWord ++ tailWord_2586450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2586494 : List Nat := [4, 2, 3, 1, 1, 2, 1, 3, 2, 4]
def baseStart_2586494 : Nat := 118140960795 + 2586494 * 2 ^ 59
def prefixEnd_2586494 : Nat := 4983230072969 + 3 ^ 40 * 2586494 * 2
def baseEnd_2586494 : Nat := 442704877323436188009979

theorem tailTrace_2586494 : CollatzResearch.WordTrace tailWord_2586494 prefixEnd_2586494 442704877323436188009979 := by
  unfold tailWord_2586494
  simp only [CollatzResearch.WordTrace]
  refine ⟨11792148286447681356468817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62891457527720967234500357 11792148286447681356468817)
  ·
    refine ⟨8844111214835761017351613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11792148286447681356468817 8844111214835761017351613)
    ·
      refine ⟨3316541705563410381506855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8844111214835761017351613 3316541705563410381506855)
      ·
        refine ⟨4974812558345115572260283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3316541705563410381506855 4974812558345115572260283)
        ·
          refine ⟨7462218837517673358390425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4974812558345115572260283 7462218837517673358390425)
          ·
            refine ⟨5596664128138255018792819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7462218837517673358390425 5596664128138255018792819)
            ·
              refine ⟨8394996192207382528189229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5596664128138255018792819 8394996192207382528189229)
              ·
                refine ⟨3148123572077768448070961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8394996192207382528189229 3148123572077768448070961)
                ·
                  refine ⟨2361092679058326336053221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3148123572077768448070961 2361092679058326336053221)
                  ·
                    refine ⟨442704877323436188009979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2361092679058326336053221 442704877323436188009979)
                    ·
                      rfl

theorem cell23_2586494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_2586494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2586494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2586494 prefixEnd_2586494 := by exact prefixLift 2586494
  have htrace : WordTrace (prefixWord ++ tailWord_2586494) baseStart_2586494 baseEnd_2586494 := by
    simpa [prefixWord, tailWord_2586494, baseEnd_2586494] using wordTrace_append hprefix tailTrace_2586494
  have hstable : (prefixWord ++ tailWord_2586494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2586494).length < 2 ^ (prefixWord ++ tailWord_2586494).sum := by decide
  have hdescent : baseEnd_2586494 < baseStart_2586494 := by decide
  rcases family_descends (prefixWord ++ tailWord_2586494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2586504 : List Nat := [2, 1, 3, 3, 3, 2, 1, 2, 1, 2, 3]
def baseStart_2586504 : Nat := 118140960795 + 2586504 * 2 ^ 59
def prefixEnd_2586504 : Nat := 4983230072969 + 3 ^ 40 * 2586504 * 2
def baseEnd_2586504 : Nat := 1328119766776853524904891

theorem tailTrace_2586504 : CollatzResearch.WordTrace tailWord_2586504 prefixEnd_2586504 1328119766776853524904891 := by
  unfold tailWord_2586504
  simp only [CollatzResearch.WordTrace]
  refine ⟨47168775510772611279807283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62891700681030148373076377 47168775510772611279807283)
  ·
    refine ⟨70753163266158916919710925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47168775510772611279807283 70753163266158916919710925)
    ·
      refine ⟨26532436224809593844891597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70753163266158916919710925 26532436224809593844891597)
      ·
        refine ⟨9949663584303597691834349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26532436224809593844891597 9949663584303597691834349)
        ·
          refine ⟨3731123844113849134437881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9949663584303597691834349 3731123844113849134437881)
          ·
            refine ⟨2798342883085386850828411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3731123844113849134437881 2798342883085386850828411)
            ·
              refine ⟨4197514324628080276242617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2798342883085386850828411 4197514324628080276242617)
              ·
                refine ⟨3148135743471060207181963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4197514324628080276242617 3148135743471060207181963)
                ·
                  refine ⟨4722203615206590310772945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3148135743471060207181963 4722203615206590310772945)
                  ·
                    refine ⟨3541652711404942733079709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4722203615206590310772945 3541652711404942733079709)
                    ·
                      refine ⟨1328119766776853524904891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3541652711404942733079709 1328119766776853524904891)
                      ·
                        rfl

theorem cell23_2586504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 2, 1, 2, 3].length) (baseStart_2586504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2586504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2586504 prefixEnd_2586504 := by exact prefixLift 2586504
  have htrace : WordTrace (prefixWord ++ tailWord_2586504) baseStart_2586504 baseEnd_2586504 := by
    simpa [prefixWord, tailWord_2586504, baseEnd_2586504] using wordTrace_append hprefix tailTrace_2586504
  have hstable : (prefixWord ++ tailWord_2586504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2586504).length < 2 ^ (prefixWord ++ tailWord_2586504).sum := by decide
  have hdescent : baseEnd_2586504 < baseStart_2586504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2586504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2586518 : List Nat := [5, 3, 1, 1, 2, 1, 3, 1, 1, 1, 4]
def baseStart_2586518 : Nat := 118140960795 + 2586518 * 2 ^ 59
def prefixEnd_2586518 : Nat := 4983230072969 + 3 ^ 40 * 2586518 * 2
def baseEnd_2586518 : Nat := 1328126955506016470129827

theorem tailTrace_2586518 : CollatzResearch.WordTrace tailWord_2586518 prefixEnd_2586518 1328126955506016470129827 := by
  unfold tailWord_2586518
  simp only [CollatzResearch.WordTrace]
  refine ⟨5896128852718406434414013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 62892041095663001967082805 5896128852718406434414013)
  ·
    refine ⟨2211048319769402412905255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5896128852718406434414013 2211048319769402412905255)
    ·
      refine ⟨3316572479654103619357883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2211048319769402412905255 3316572479654103619357883)
      ·
        refine ⟨4974858719481155429036825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3316572479654103619357883 4974858719481155429036825)
        ·
          refine ⟨3731144039610866571777619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4974858719481155429036825 3731144039610866571777619)
          ·
            refine ⟨5596716059416299857666429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3731144039610866571777619 5596716059416299857666429)
            ·
              refine ⟨2098768522281112446624911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5596716059416299857666429 2098768522281112446624911)
              ·
                refine ⟨3148152783421668669937367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2098768522281112446624911 3148152783421668669937367)
                ·
                  refine ⟨4722229175132503004906051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3148152783421668669937367 4722229175132503004906051)
                  ·
                    refine ⟨7083343762698754507359077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4722229175132503004906051 7083343762698754507359077)
                    ·
                      refine ⟨1328126955506016470129827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7083343762698754507359077 1328126955506016470129827)
                      ·
                        rfl

theorem cell23_2586518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_2586518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2586518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2586518 prefixEnd_2586518 := by exact prefixLift 2586518
  have htrace : WordTrace (prefixWord ++ tailWord_2586518) baseStart_2586518 baseEnd_2586518 := by
    simpa [prefixWord, tailWord_2586518, baseEnd_2586518] using wordTrace_append hprefix tailTrace_2586518
  have hstable : (prefixWord ++ tailWord_2586518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2586518).length < 2 ^ (prefixWord ++ tailWord_2586518).sum := by decide
  have hdescent : baseEnd_2586518 < baseStart_2586518 := by decide
  rcases family_descends (prefixWord ++ tailWord_2586518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2586543 : List Nat := [1, 1, 2, 1, 2, 2, 3, 1, 1, 6, 3]
def baseStart_2586543 : Nat := 118140960795 + 2586543 * 2 ^ 59
def prefixEnd_2586543 : Nat := 4983230072969 + 3 ^ 40 * 2586543 * 2
def baseEnd_2586543 : Nat := 1328139792522378872317211

theorem tailTrace_2586543 : CollatzResearch.WordTrace tailWord_2586543 prefixEnd_2586543 1328139792522378872317211 := by
  unfold tailWord_2586543
  simp only [CollatzResearch.WordTrace]
  refine ⟨94338973468403932220284283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62892648978935954813522855 94338973468403932220284283)
  ·
    refine ⟨141508460202605898330426425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94338973468403932220284283 141508460202605898330426425)
    ·
      refine ⟨106131345151954423747819819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141508460202605898330426425 106131345151954423747819819)
      ·
        refine ⟨159197017727931635621729729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106131345151954423747819819 159197017727931635621729729)
        ·
          refine ⟨119397763295948726716297297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159197017727931635621729729 119397763295948726716297297)
          ·
            refine ⟨89548322471961545037222973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119397763295948726716297297 89548322471961545037222973)
            ·
              refine ⟨33580620926985579388958615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89548322471961545037222973 33580620926985579388958615)
              ·
                refine ⟨50370931390478369083437923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33580620926985579388958615 50370931390478369083437923)
                ·
                  refine ⟨75556397085717553625156885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50370931390478369083437923 75556397085717553625156885)
                  ·
                    refine ⟨3541706113393010326179229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 75556397085717553625156885 3541706113393010326179229)
                    ·
                      refine ⟨1328139792522378872317211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3541706113393010326179229 1328139792522378872317211)
                      ·
                        rfl

theorem cell23_2586543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 6, 3].length) (baseStart_2586543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2586543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2586543 prefixEnd_2586543 := by exact prefixLift 2586543
  have htrace : WordTrace (prefixWord ++ tailWord_2586543) baseStart_2586543 baseEnd_2586543 := by
    simpa [prefixWord, tailWord_2586543, baseEnd_2586543] using wordTrace_append hprefix tailTrace_2586543
  have hstable : (prefixWord ++ tailWord_2586543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2586543).length < 2 ^ (prefixWord ++ tailWord_2586543).sum := by decide
  have hdescent : baseEnd_2586543 < baseStart_2586543 := by decide
  rcases family_descends (prefixWord ++ tailWord_2586543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2586557 : List Nat := [1, 4, 1, 2, 3, 1, 1, 3, 1, 4, 2]
def baseStart_2586557 : Nat := 118140960795 + 2586557 * 2 ^ 59
def prefixEnd_2586557 : Nat := 4983230072969 + 3 ^ 40 * 2586557 * 2
def baseEnd_2586557 : Nat := 1328146981251541817542147

theorem tailTrace_2586557 : CollatzResearch.WordTrace tailWord_2586557 prefixEnd_2586557 1328146981251541817542147 := by
  unfold tailWord_2586557
  simp only [CollatzResearch.WordTrace]
  refine ⟨94339484090353212611293925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62892989393568808407529283 94339484090353212611293925)
  ·
    refine ⟨17688653266941227364617611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94339484090353212611293925 17688653266941227364617611)
    ·
      refine ⟨26532979900411841046926417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17688653266941227364617611 26532979900411841046926417)
      ·
        refine ⟨19899734925308880785194813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26532979900411841046926417 19899734925308880785194813)
        ·
          refine ⟨7462400596990830294448055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19899734925308880785194813 7462400596990830294448055)
          ·
            refine ⟨11193600895486245441672083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7462400596990830294448055 11193600895486245441672083)
            ·
              refine ⟨16790401343229368162508125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11193600895486245441672083 16790401343229368162508125)
              ·
                refine ⟨6296400503711013060940547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16790401343229368162508125 6296400503711013060940547)
                ·
                  refine ⟨9444600755566519591410821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6296400503711013060940547 9444600755566519591410821)
                  ·
                    refine ⟨1770862641668722423389529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9444600755566519591410821 1770862641668722423389529)
                    ·
                      refine ⟨1328146981251541817542147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1770862641668722423389529 1328146981251541817542147)
                      ·
                        rfl

theorem cell23_2586557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 3, 1, 4, 2].length) (baseStart_2586557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2586557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2586557 prefixEnd_2586557 := by exact prefixLift 2586557
  have htrace : WordTrace (prefixWord ++ tailWord_2586557) baseStart_2586557 baseEnd_2586557 := by
    simpa [prefixWord, tailWord_2586557, baseEnd_2586557] using wordTrace_append hprefix tailTrace_2586557
  have hstable : (prefixWord ++ tailWord_2586557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2586557).length < 2 ^ (prefixWord ++ tailWord_2586557).sum := by decide
  have hdescent : baseEnd_2586557 < baseStart_2586557 := by decide
  rcases family_descends (prefixWord ++ tailWord_2586557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2586578 : List Nat := [3, 2, 2, 3, 2, 2, 2, 1, 1, 3, 2]
def baseStart_2586578 : Nat := 118140960795 + 2586578 * 2 ^ 59
def prefixEnd_2586578 : Nat := 4983230072969 + 3 ^ 40 * 2586578 * 2
def baseEnd_2586578 : Nat := 1328157764345286235379551

theorem tailTrace_2586578 : CollatzResearch.WordTrace tailWord_2586578 prefixEnd_2586578 1328157764345286235379551 := by
  unfold tailWord_2586578
  simp only [CollatzResearch.WordTrace]
  refine ⟨23585062505819283299452097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62893500015518088798538925 23585062505819283299452097)
  ·
    refine ⟨17688796879364462474589073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23585062505819283299452097 17688796879364462474589073)
    ·
      refine ⟨13266597659523346855941805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17688796879364462474589073 13266597659523346855941805)
      ·
        refine ⟨4974974122321255070978177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13266597659523346855941805 4974974122321255070978177)
        ·
          refine ⟨3731230591740941303233633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4974974122321255070978177 3731230591740941303233633)
          ·
            refine ⟨2798422943805705977425225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3731230591740941303233633 2798422943805705977425225)
            ·
              refine ⟨2098817207854279483068919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2798422943805705977425225 2098817207854279483068919)
              ·
                refine ⟨3148225811781419224603379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2098817207854279483068919 3148225811781419224603379)
                ·
                  refine ⟨4722338717672128836905069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3148225811781419224603379 4722338717672128836905069)
                  ·
                    refine ⟨1770877019127048313839401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4722338717672128836905069 1770877019127048313839401)
                    ·
                      refine ⟨1328157764345286235379551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1770877019127048313839401 1328157764345286235379551)
                      ·
                        rfl

theorem cell23_2586578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_2586578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2586578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2586578 prefixEnd_2586578 := by exact prefixLift 2586578
  have htrace : WordTrace (prefixWord ++ tailWord_2586578) baseStart_2586578 baseEnd_2586578 := by
    simpa [prefixWord, tailWord_2586578, baseEnd_2586578] using wordTrace_append hprefix tailTrace_2586578
  have hstable : (prefixWord ++ tailWord_2586578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2586578).length < 2 ^ (prefixWord ++ tailWord_2586578).sum := by decide
  have hdescent : baseEnd_2586578 < baseStart_2586578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2586578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2586591 : List Nat := [1, 1, 2, 3, 4, 3, 1, 2, 2, 2, 2]
def baseStart_2586591 : Nat := 118140960795 + 2586591 * 2 ^ 59
def prefixEnd_2586591 : Nat := 4983230072969 + 3 ^ 40 * 2586591 * 2
def baseEnd_2586591 : Nat := 1328164439593794684516991

theorem tailTrace_2586591 : CollatzResearch.WordTrace tailWord_2586591 prefixEnd_2586591 1328164439593794684516991 := by
  unfold tailWord_2586591
  simp only [CollatzResearch.WordTrace]
  refine ⟨94340724172230036418031627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62893816114820024278687751 94340724172230036418031627)
  ·
    refine ⟨141511086258345054627047441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94340724172230036418031627 141511086258345054627047441)
    ·
      refine ⟨106133314693758790970285581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141511086258345054627047441 106133314693758790970285581)
      ·
        refine ⟨39799993010159546613857093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106133314693758790970285581 39799993010159546613857093)
        ·
          refine ⟨7462498689404914990098205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39799993010159546613857093 7462498689404914990098205)
          ·
            refine ⟨2798437008526843121286827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7462498689404914990098205 2798437008526843121286827)
            ·
              refine ⟨4197655512790264681930241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2798437008526843121286827 4197655512790264681930241)
              ·
                refine ⟨3148241634592698511447681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4197655512790264681930241 3148241634592698511447681)
                ·
                  refine ⟨2361181225944523883585761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3148241634592698511447681 2361181225944523883585761)
                  ·
                    refine ⟨1770885919458392912689321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2361181225944523883585761 1770885919458392912689321)
                    ·
                      refine ⟨1328164439593794684516991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1770885919458392912689321 1328164439593794684516991)
                      ·
                        rfl

theorem cell23_2586591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 2, 2, 2, 2].length) (baseStart_2586591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2586591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2586591 prefixEnd_2586591 := by exact prefixLift 2586591
  have htrace : WordTrace (prefixWord ++ tailWord_2586591) baseStart_2586591 baseEnd_2586591 := by
    simpa [prefixWord, tailWord_2586591, baseEnd_2586591] using wordTrace_append hprefix tailTrace_2586591
  have hstable : (prefixWord ++ tailWord_2586591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2586591).length < 2 ^ (prefixWord ++ tailWord_2586591).sum := by decide
  have hdescent : baseEnd_2586591 < baseStart_2586591 := by decide
  rcases family_descends (prefixWord ++ tailWord_2586591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2586603 : List Nat := [1, 1, 1, 1, 2, 3, 1, 5, 1, 2, 5]
def baseStart_2586603 : Nat := 118140960795 + 2586603 * 2 ^ 59
def prefixEnd_2586603 : Nat := 4983230072969 + 3 ^ 40 * 2586603 * 2
def baseEnd_2586603 : Nat := 1328170601361648637566935

theorem tailTrace_2586603 : CollatzResearch.WordTrace tailWord_2586603 prefixEnd_2586603 1328170601361648637566935 := by
  unfold tailWord_2586603
  simp only [CollatzResearch.WordTrace]
  refine ⟨94341161848186562467468463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62894107898791041644978975 94341161848186562467468463)
  ·
    refine ⟨141511742772279843701202695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94341161848186562467468463 141511742772279843701202695)
    ·
      refine ⟨212267614158419765551804043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141511742772279843701202695 212267614158419765551804043)
      ·
        refine ⟨318401421237629648327706065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212267614158419765551804043 318401421237629648327706065)
        ·
          refine ⟨238801065928222236245779549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 318401421237629648327706065 238801065928222236245779549)
          ·
            refine ⟨89550399723083338592167331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 238801065928222236245779549 89550399723083338592167331)
            ·
              refine ⟨134325599584625007888250997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89550399723083338592167331 134325599584625007888250997)
              ·
                refine ⟨12593024961058594489523531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 134325599584625007888250997 12593024961058594489523531)
                ·
                  refine ⟨18889537441587891734285297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12593024961058594489523531 18889537441587891734285297)
                  ·
                    refine ⟨14167153081190918800713973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18889537441587891734285297 14167153081190918800713973)
                    ·
                      refine ⟨1328170601361648637566935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14167153081190918800713973 1328170601361648637566935)
                      ·
                        rfl

theorem cell23_2586603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 5, 1, 2, 5].length) (baseStart_2586603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2586603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2586603 prefixEnd_2586603 := by exact prefixLift 2586603
  have htrace : WordTrace (prefixWord ++ tailWord_2586603) baseStart_2586603 baseEnd_2586603 := by
    simpa [prefixWord, tailWord_2586603, baseEnd_2586603] using wordTrace_append hprefix tailTrace_2586603
  have hstable : (prefixWord ++ tailWord_2586603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2586603).length < 2 ^ (prefixWord ++ tailWord_2586603).sum := by decide
  have hdescent : baseEnd_2586603 < baseStart_2586603 := by decide
  rcases family_descends (prefixWord ++ tailWord_2586603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2586633 : List Nat := [1, 2, 1, 1, 3, 1, 1, 1, 4, 3, 5]
def baseStart_2586633 : Nat := 118140960795 + 2586633 * 2 ^ 59
def prefixEnd_2586633 : Nat := 4983230072969 + 3 ^ 40 * 2586633 * 2
def baseEnd_2586633 : Nat := 1328186005781283520191797

theorem tailTrace_2586633 : CollatzResearch.WordTrace tailWord_2586633 prefixEnd_2586633 1328186005781283520191797 := by
  unfold tailWord_2586633
  simp only [CollatzResearch.WordTrace]
  refine ⟨94342256038077877591060553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62894837358718585060707035 94342256038077877591060553)
  ·
    refine ⟨70756692028558408193295415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94342256038077877591060553 70756692028558408193295415)
    ·
      refine ⟨106135038042837612289943123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70756692028558408193295415 106135038042837612289943123)
      ·
        refine ⟨159202557064256418434914685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106135038042837612289943123 159202557064256418434914685)
        ·
          refine ⟨59700958899096156913093007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 159202557064256418434914685 59700958899096156913093007)
          ·
            refine ⟨89551438348644235369639511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59700958899096156913093007 89551438348644235369639511)
            ·
              refine ⟨134327157522966353054459267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89551438348644235369639511 134327157522966353054459267)
              ·
                refine ⟨201490736284449529581688901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 134327157522966353054459267 201490736284449529581688901)
                ·
                  refine ⟨37779513053334286796566669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 201490736284449529581688901 37779513053334286796566669)
                  ·
                    refine ⟨14167317395000357548712501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37779513053334286796566669 14167317395000357548712501)
                    ·
                      refine ⟨1328186005781283520191797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14167317395000357548712501 1328186005781283520191797)
                      ·
                        rfl

theorem cell23_2586633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 3, 5].length) (baseStart_2586633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2586633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2586633 prefixEnd_2586633 := by exact prefixLift 2586633
  have htrace : WordTrace (prefixWord ++ tailWord_2586633) baseStart_2586633 baseEnd_2586633 := by
    simpa [prefixWord, tailWord_2586633, baseEnd_2586633] using wordTrace_append hprefix tailTrace_2586633
  have hstable : (prefixWord ++ tailWord_2586633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2586633).length < 2 ^ (prefixWord ++ tailWord_2586633).sum := by decide
  have hdescent : baseEnd_2586633 < baseStart_2586633 := by decide
  rcases family_descends (prefixWord ++ tailWord_2586633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2586643 : List Nat := [1, 1, 1, 2, 1, 4, 2, 1, 1, 3, 6]
def baseStart_2586643 : Nat := 118140960795 + 2586643 * 2 ^ 59
def prefixEnd_2586643 : Nat := 4983230072969 + 3 ^ 40 * 2586643 * 2
def baseEnd_2586643 : Nat := 1328191140587828481066751

theorem tailTrace_2586643 : CollatzResearch.WordTrace tailWord_2586643 prefixEnd_2586643 1328191140587828481066751 := by
  unfold tailWord_2586643
  simp only [CollatzResearch.WordTrace]
  refine ⟨94342620768041649298924583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62895080512027766199283055 94342620768041649298924583)
  ·
    refine ⟨141513931152062473948386875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94342620768041649298924583 141513931152062473948386875)
    ·
      refine ⟨212270896728093710922580313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141513931152062473948386875 212270896728093710922580313)
      ·
        refine ⟨159203172546070283191935235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212270896728093710922580313 159203172546070283191935235)
        ·
          refine ⟨238804758819105424787902853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159203172546070283191935235 238804758819105424787902853)
          ·
            refine ⟨44775892278582267147731785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 238804758819105424787902853 44775892278582267147731785)
            ·
              refine ⟨33581919208936700360798839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44775892278582267147731785 33581919208936700360798839)
              ·
                refine ⟨50372878813405050541198259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33581919208936700360798839 50372878813405050541198259)
                ·
                  refine ⟨75559318220107575811797389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50372878813405050541198259 75559318220107575811797389)
                  ·
                    refine ⟨28334744332540340929424021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 75559318220107575811797389 28334744332540340929424021)
                    ·
                      refine ⟨1328191140587828481066751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28334744332540340929424021 1328191140587828481066751)
                      ·
                        rfl

theorem cell23_2586643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 3, 6].length) (baseStart_2586643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2586643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2586643 prefixEnd_2586643 := by exact prefixLift 2586643
  have htrace : WordTrace (prefixWord ++ tailWord_2586643) baseStart_2586643 baseEnd_2586643 := by
    simpa [prefixWord, tailWord_2586643, baseEnd_2586643] using wordTrace_append hprefix tailTrace_2586643
  have hstable : (prefixWord ++ tailWord_2586643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2586643).length < 2 ^ (prefixWord ++ tailWord_2586643).sum := by decide
  have hdescent : baseEnd_2586643 < baseStart_2586643 := by decide
  rcases family_descends (prefixWord ++ tailWord_2586643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2586683 : List Nat := [1, 1, 1, 1, 1, 2, 1, 4, 2, 9]
def baseStart_2586683 : Nat := 118140960795 + 2586683 * 2 ^ 59
def prefixEnd_2586683 : Nat := 4983230072969 + 3 ^ 40 * 2586683 * 2
def baseEnd_2586683 : Nat := 442737226604669441522189

theorem tailTrace_2586683 : CollatzResearch.WordTrace tailWord_2586683 prefixEnd_2586683 442737226604669441522189 := by
  unfold tailWord_2586683
  simp only [CollatzResearch.WordTrace]
  refine ⟨94344079687896736130380703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62896053125264490753587135 94344079687896736130380703)
  ·
    refine ⟨141516119531845104195571055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94344079687896736130380703 141516119531845104195571055)
    ·
      refine ⟨212274179297767656293356583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141516119531845104195571055 212274179297767656293356583)
      ·
        refine ⟨318411268946651484440034875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212274179297767656293356583 318411268946651484440034875)
        ·
          refine ⟨477616903419977226660052313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 318411268946651484440034875 477616903419977226660052313)
          ·
            refine ⟨358212677564982919995039235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 477616903419977226660052313 358212677564982919995039235)
            ·
              refine ⟨537319016347474379992558853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 358212677564982919995039235 537319016347474379992558853)
              ·
                refine ⟨100747315565151446248604785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 537319016347474379992558853 100747315565151446248604785)
                ·
                  refine ⟨75560486673863584686453589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 100747315565151446248604785 75560486673863584686453589)
                  ·
                    refine ⟨442737226604669441522189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 75560486673863584686453589 442737226604669441522189)
                    ·
                      rfl

theorem cell23_2586683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 9].length) (baseStart_2586683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2586683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2586683 prefixEnd_2586683 := by exact prefixLift 2586683
  have htrace : WordTrace (prefixWord ++ tailWord_2586683) baseStart_2586683 baseEnd_2586683 := by
    simpa [prefixWord, tailWord_2586683, baseEnd_2586683] using wordTrace_append hprefix tailTrace_2586683
  have hstable : (prefixWord ++ tailWord_2586683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2586683).length < 2 ^ (prefixWord ++ tailWord_2586683).sum := by decide
  have hdescent : baseEnd_2586683 < baseStart_2586683 := by decide
  rcases family_descends (prefixWord ++ tailWord_2586683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2586737 : List Nat := [1, 2, 2, 2, 1, 1, 4, 4, 1, 1, 4]
def baseStart_2586737 : Nat := 118140960795 + 2586737 * 2 ^ 59
def prefixEnd_2586737 : Nat := 4983230072969 + 3 ^ 40 * 2586737 * 2
def baseEnd_2586737 : Nat := 1328239407769351113291319

theorem tailTrace_2586737 : CollatzResearch.WordTrace tailWord_2586737 prefixEnd_2586737 1328239407769351113291319 := by
  unfold tailWord_2586737
  simp only [CollatzResearch.WordTrace]
  refine ⟨94346049229701103352846465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62897366153134068901897643 94346049229701103352846465)
  ·
    refine ⟨70759536922275827514634849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94346049229701103352846465 70759536922275827514634849)
    ·
      refine ⟨53069652691706870635976137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70759536922275827514634849 53069652691706870635976137)
      ·
        refine ⟨39802239518780152976982103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53069652691706870635976137 39802239518780152976982103)
        ·
          refine ⟨59703359278170229465473155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39802239518780152976982103 59703359278170229465473155)
          ·
            refine ⟨89555038917255344198209733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59703359278170229465473155 89555038917255344198209733)
            ·
              refine ⟨16791569796985377037164325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 89555038917255344198209733 16791569796985377037164325)
              ·
                refine ⟨3148419336934758194468311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16791569796985377037164325 3148419336934758194468311)
                ·
                  refine ⟨4722629005402137291702467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3148419336934758194468311 4722629005402137291702467)
                  ·
                    refine ⟨7083943508103205937553701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4722629005402137291702467 7083943508103205937553701)
                    ·
                      refine ⟨1328239407769351113291319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7083943508103205937553701 1328239407769351113291319)
                      ·
                        rfl

theorem cell23_2586737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 4, 1, 1, 4].length) (baseStart_2586737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2586737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2586737 prefixEnd_2586737 := by exact prefixLift 2586737
  have htrace : WordTrace (prefixWord ++ tailWord_2586737) baseStart_2586737 baseEnd_2586737 := by
    simpa [prefixWord, tailWord_2586737, baseEnd_2586737] using wordTrace_append hprefix tailTrace_2586737
  have hstable : (prefixWord ++ tailWord_2586737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2586737).length < 2 ^ (prefixWord ++ tailWord_2586737).sum := by decide
  have hdescent : baseEnd_2586737 < baseStart_2586737 := by decide
  rcases family_descends (prefixWord ++ tailWord_2586737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2586781 : List Nat := [1, 4, 2, 1, 1, 4, 3, 1, 2, 4]
def baseStart_2586781 : Nat := 118140960795 + 2586781 * 2 ^ 59
def prefixEnd_2586781 : Nat := 4983230072969 + 3 ^ 40 * 2586781 * 2
def baseEnd_2586781 : Nat := 442754000306049647047039

theorem tailTrace_2586781 : CollatzResearch.WordTrace tailWord_2586781 prefixEnd_2586781 442754000306049647047039 := by
  unfold tailWord_2586781
  simp only [CollatzResearch.WordTrace]
  refine ⟨94347654041541698867448197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62898436027694465911632131 94347654041541698867448197)
  ·
    refine ⟨17690185132789068537646537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94347654041541698867448197 17690185132789068537646537)
    ·
      refine ⟨13267638849591801403234903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17690185132789068537646537 13267638849591801403234903)
      ·
        refine ⟨19901458274387702104852355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13267638849591801403234903 19901458274387702104852355)
        ·
          refine ⟨29852187411581553157278533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19901458274387702104852355 29852187411581553157278533)
          ·
            refine ⟨5597285139671541216989725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29852187411581553157278533 5597285139671541216989725)
            ·
              refine ⟨2098981927376827956371147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5597285139671541216989725 2098981927376827956371147)
              ·
                refine ⟨3148472891065241934556721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2098981927376827956371147 3148472891065241934556721)
                ·
                  refine ⟨2361354668298931450917541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3148472891065241934556721 2361354668298931450917541)
                  ·
                    refine ⟨442754000306049647047039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2361354668298931450917541 442754000306049647047039)
                    ·
                      rfl

theorem cell23_2586781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 3, 1, 2, 4].length) (baseStart_2586781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2586781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2586781 prefixEnd_2586781 := by exact prefixLift 2586781
  have htrace : WordTrace (prefixWord ++ tailWord_2586781) baseStart_2586781 baseEnd_2586781 := by
    simpa [prefixWord, tailWord_2586781, baseEnd_2586781] using wordTrace_append hprefix tailTrace_2586781
  have hstable : (prefixWord ++ tailWord_2586781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2586781).length < 2 ^ (prefixWord ++ tailWord_2586781).sum := by decide
  have hdescent : baseEnd_2586781 < baseStart_2586781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2586781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2586784 : List Nat := [2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 4]
def baseStart_2586784 : Nat := 118140960795 + 2586784 * 2 ^ 59
def prefixEnd_2586784 : Nat := 4983230072969 + 3 ^ 40 * 2586784 * 2
def baseEnd_2586784 : Nat := 1328263541360112429403603

theorem tailTrace_2586784 : CollatzResearch.WordTrace tailWord_2586784 prefixEnd_2586784 1328263541360112429403603 := by
  unfold tailWord_2586784
  simp only [CollatzResearch.WordTrace]
  refine ⟨47173881730265415189903703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62898508973687220253204937 47173881730265415189903703)
  ·
    refine ⟨70760822595398122784855555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47173881730265415189903703 70760822595398122784855555)
    ·
      refine ⟨106141233893097184177283333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70760822595398122784855555 106141233893097184177283333)
      ·
        refine ⟨19901481354955722033240625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106141233893097184177283333 19901481354955722033240625)
        ·
          refine ⟨14926111016216791524930469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19901481354955722033240625 14926111016216791524930469)
          ·
            refine ⟨2798645815540648410924463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14926111016216791524930469 2798645815540648410924463)
            ·
              refine ⟨4197968723310972616386695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2798645815540648410924463 4197968723310972616386695)
              ·
                refine ⟨6296953084966458924580043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4197968723310972616386695 6296953084966458924580043)
                ·
                  refine ⟨9445429627449688386870065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6296953084966458924580043 9445429627449688386870065)
                  ·
                    refine ⟨7084072220587266290152549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9445429627449688386870065 7084072220587266290152549)
                    ·
                      refine ⟨1328263541360112429403603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7084072220587266290152549 1328263541360112429403603)
                      ·
                        rfl

theorem cell23_2586784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 4].length) (baseStart_2586784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2586784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2586784 prefixEnd_2586784 := by exact prefixLift 2586784
  have htrace : WordTrace (prefixWord ++ tailWord_2586784) baseStart_2586784 baseEnd_2586784 := by
    simpa [prefixWord, tailWord_2586784, baseEnd_2586784] using wordTrace_append hprefix tailTrace_2586784
  have hstable : (prefixWord ++ tailWord_2586784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2586784).length < 2 ^ (prefixWord ++ tailWord_2586784).sum := by decide
  have hdescent : baseEnd_2586784 < baseStart_2586784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2586784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2586794 : List Nat := [3, 1, 5, 1, 2, 1, 1, 9]
def baseStart_2586794 : Nat := 118140960795 + 2586794 * 2 ^ 59
def prefixEnd_2586794 : Nat := 4983230072969 + 3 ^ 40 * 2586794 * 2
def baseEnd_2586794 : Nat := 49195136154320644084391

theorem tailTrace_2586794 : CollatzResearch.WordTrace tailWord_2586794 prefixEnd_2586794 49195136154320644084391 := by
  unfold tailWord_2586794
  simp only [CollatzResearch.WordTrace]
  refine ⟨23587032047623650521917859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62898752126996401391780957 23587032047623650521917859)
  ·
    refine ⟨35380548071435475782876789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23587032047623650521917859 35380548071435475782876789)
    ·
      refine ⟨3316926381697075854644699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35380548071435475782876789 3316926381697075854644699)
      ·
        refine ⟨4975389572545613781967049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3316926381697075854644699 4975389572545613781967049)
        ·
          refine ⟨3731542179409210336475287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4975389572545613781967049 3731542179409210336475287)
          ·
            refine ⟨5597313269113815504712931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3731542179409210336475287 5597313269113815504712931)
            ·
              refine ⟨8395969903670723257069397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5597313269113815504712931 8395969903670723257069397)
              ·
                refine ⟨49195136154320644084391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8395969903670723257069397 49195136154320644084391)
                ·
                  rfl

theorem cell23_2586794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 9].length) (baseStart_2586794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2586794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2586794 prefixEnd_2586794 := by exact prefixLift 2586794
  have htrace : WordTrace (prefixWord ++ tailWord_2586794) baseStart_2586794 baseEnd_2586794 := by
    simpa [prefixWord, tailWord_2586794, baseEnd_2586794] using wordTrace_append hprefix tailTrace_2586794
  have hstable : (prefixWord ++ tailWord_2586794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2586794).length < 2 ^ (prefixWord ++ tailWord_2586794).sum := by decide
  have hdescent : baseEnd_2586794 < baseStart_2586794 := by decide
  rcases family_descends (prefixWord ++ tailWord_2586794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2586877 : List Nat := [1, 4, 1, 1, 1, 1, 1, 2, 3, 5, 3]
def baseStart_2586877 : Nat := 118140960795 + 2586877 * 2 ^ 59
def prefixEnd_2586877 : Nat := 4983230072969 + 3 ^ 40 * 2586877 * 2
def baseEnd_2586877 : Nat := 1328311295060980565540675

theorem tailTrace_2586877 : CollatzResearch.WordTrace tailWord_2586877 prefixEnd_2586877 1328311295060980565540675 := by
  unfold tailWord_2586877
  simp only [CollatzResearch.WordTrace]
  refine ⟨94351155449193907262942885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62900770299462604841961923 94351155449193907262942885)
  ·
    refine ⟨17690841646723857611801791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94351155449193907262942885 17690841646723857611801791)
    ·
      refine ⟨26536262470085786417702687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17690841646723857611801791 26536262470085786417702687)
      ·
        refine ⟨39804393705128679626554031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26536262470085786417702687 39804393705128679626554031)
        ·
          refine ⟨59706590557693019439831047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39804393705128679626554031 59706590557693019439831047)
          ·
            refine ⟨89559885836539529159746571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59706590557693019439831047 89559885836539529159746571)
            ·
              refine ⟨134339828754809293739619857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89559885836539529159746571 134339828754809293739619857)
              ·
                refine ⟨100754871566106970304714893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 134339828754809293739619857 100754871566106970304714893)
                ·
                  refine ⟨37783076837290113864268085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 100754871566106970304714893 37783076837290113864268085)
                  ·
                    refine ⟨3542163453495948174775133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37783076837290113864268085 3542163453495948174775133)
                    ·
                      refine ⟨1328311295060980565540675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3542163453495948174775133 1328311295060980565540675)
                      ·
                        rfl

theorem cell23_2586877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 5, 3].length) (baseStart_2586877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2586877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2586877 prefixEnd_2586877 := by exact prefixLift 2586877
  have htrace : WordTrace (prefixWord ++ tailWord_2586877) baseStart_2586877 baseEnd_2586877 := by
    simpa [prefixWord, tailWord_2586877, baseEnd_2586877] using wordTrace_append hprefix tailTrace_2586877
  have hstable : (prefixWord ++ tailWord_2586877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2586877).length < 2 ^ (prefixWord ++ tailWord_2586877).sum := by decide
  have hdescent : baseEnd_2586877 < baseStart_2586877 := by decide
  rcases family_descends (prefixWord ++ tailWord_2586877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2586894 : List Nat := [4, 1, 1, 2, 1, 2, 3, 1, 2, 3, 3]
def baseStart_2586894 : Nat := 118140960795 + 2586894 * 2 ^ 59
def prefixEnd_2586894 : Nat := 4983230072969 + 3 ^ 40 * 2586894 * 2
def baseEnd_2586894 : Nat := 1328320024232106999028097

theorem tailTrace_2586894 : CollatzResearch.WordTrace tailWord_2586894 prefixEnd_2586894 1328320024232106999028097 := by
  unfold tailWord_2586894
  simp only [CollatzResearch.WordTrace]
  refine ⟨11793971936266539895788967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62901183660088212777541157 11793971936266539895788967)
  ·
    refine ⟨17690957904399809843683451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11793971936266539895788967 17690957904399809843683451)
    ·
      refine ⟨26536436856599714765525177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17690957904399809843683451 26536436856599714765525177)
      ·
        refine ⟨19902327642449786074143883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26536436856599714765525177 19902327642449786074143883)
        ·
          refine ⟨29853491463674679111215825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19902327642449786074143883 29853491463674679111215825)
          ·
            refine ⟨22390118597756009333411869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29853491463674679111215825 22390118597756009333411869)
            ·
              refine ⟨8396294474158503500029451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22390118597756009333411869 8396294474158503500029451)
              ·
                refine ⟨12594441711237755250044177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8396294474158503500029451 12594441711237755250044177)
                ·
                  refine ⟨9445831283428316437533133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12594441711237755250044177 9445831283428316437533133)
                  ·
                    refine ⟨3542186731285618664074925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9445831283428316437533133 3542186731285618664074925)
                    ·
                      refine ⟨1328320024232106999028097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3542186731285618664074925 1328320024232106999028097)
                      ·
                        rfl

theorem cell23_2586894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 1, 2, 3, 3].length) (baseStart_2586894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2586894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2586894 prefixEnd_2586894 := by exact prefixLift 2586894
  have htrace : WordTrace (prefixWord ++ tailWord_2586894) baseStart_2586894 baseEnd_2586894 := by
    simpa [prefixWord, tailWord_2586894, baseEnd_2586894] using wordTrace_append hprefix tailTrace_2586894
  have hstable : (prefixWord ++ tailWord_2586894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2586894).length < 2 ^ (prefixWord ++ tailWord_2586894).sum := by decide
  have hdescent : baseEnd_2586894 < baseStart_2586894 := by decide
  rcases family_descends (prefixWord ++ tailWord_2586894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2586904 : List Nat := [2, 1, 2, 3, 1, 2, 1, 2, 2, 5, 2]
def baseStart_2586904 : Nat := 118140960795 + 2586904 * 2 ^ 59
def prefixEnd_2586904 : Nat := 4983230072969 + 3 ^ 40 * 2586904 * 2
def baseEnd_2586904 : Nat := 1328325159038651959903051

theorem tailTrace_2586904 : CollatzResearch.WordTrace tailWord_2586904 prefixEnd_2586904 1328325159038651959903051 := by
  unfold tailWord_2586904
  simp only [CollatzResearch.WordTrace]
  refine ⟨47176070110048045437087883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62901426813397393916117177 47176070110048045437087883)
  ·
    refine ⟨70764105165072068155631825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47176070110048045437087883 70764105165072068155631825)
    ·
      refine ⟨53073078873804051116723869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70764105165072068155631825 53073078873804051116723869)
      ·
        refine ⟨19902404577676519168771451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53073078873804051116723869 19902404577676519168771451)
        ·
          refine ⟨29853606866514778753157177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19902404577676519168771451 29853606866514778753157177)
          ·
            refine ⟨22390205149886084064867883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29853606866514778753157177 22390205149886084064867883)
            ·
              refine ⟨33585307724829126097301825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22390205149886084064867883 33585307724829126097301825)
              ·
                refine ⟨25188980793621844572976369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33585307724829126097301825 25188980793621844572976369)
                ·
                  refine ⟨18891735595216383429732277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25188980793621844572976369 18891735595216383429732277)
                  ·
                    refine ⟨1771100212051535946537401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18891735595216383429732277 1771100212051535946537401)
                    ·
                      refine ⟨1328325159038651959903051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1771100212051535946537401 1328325159038651959903051)
                      ·
                        rfl

theorem cell23_2586904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 2, 5, 2].length) (baseStart_2586904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2586904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2586904 prefixEnd_2586904 := by exact prefixLift 2586904
  have htrace : WordTrace (prefixWord ++ tailWord_2586904) baseStart_2586904 baseEnd_2586904 := by
    simpa [prefixWord, tailWord_2586904, baseEnd_2586904] using wordTrace_append hprefix tailTrace_2586904
  have hstable : (prefixWord ++ tailWord_2586904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2586904).length < 2 ^ (prefixWord ++ tailWord_2586904).sum := by decide
  have hdescent : baseEnd_2586904 < baseStart_2586904 := by decide
  rcases family_descends (prefixWord ++ tailWord_2586904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2586914 : List Nat := [3, 3, 1, 1, 3, 2, 1, 1, 1, 7]
def baseStart_2586914 : Nat := 118140960795 + 2586914 * 2 ^ 59
def prefixEnd_2586914 : Nat := 4983230072969 + 3 ^ 40 * 2586914 * 2
def baseEnd_2586914 : Nat := 442776764615065640259335

theorem tailTrace_2586914 : CollatzResearch.WordTrace tailWord_2586914 prefixEnd_2586914 442776764615065640259335 := by
  unfold tailWord_2586914
  simp only [CollatzResearch.WordTrace]
  refine ⟨23588126237514965645509949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62901669966706575054693197 23588126237514965645509949)
  ·
    refine ⟨8845547339068112117066231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23588126237514965645509949 8845547339068112117066231)
    ·
      refine ⟨13268321008602168175599347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8845547339068112117066231 13268321008602168175599347)
      ·
        refine ⟨19902481512903252263399021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13268321008602168175599347 19902481512903252263399021)
        ·
          refine ⟨7463430567338719598774633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19902481512903252263399021 7463430567338719598774633)
          ·
            refine ⟨5597572925504039699080975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7463430567338719598774633 5597572925504039699080975)
            ·
              refine ⟨8396359388256059548621463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5597572925504039699080975 8396359388256059548621463)
              ·
                refine ⟨12594539082384089322932195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8396359388256059548621463 12594539082384089322932195)
                ·
                  refine ⟨18891808623576133984398293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12594539082384089322932195 18891808623576133984398293)
                  ·
                    refine ⟨442776764615065640259335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18891808623576133984398293 442776764615065640259335)
                    ·
                      rfl

theorem cell23_2586914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 1, 1, 7].length) (baseStart_2586914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2586914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2586914 prefixEnd_2586914 := by exact prefixLift 2586914
  have htrace : WordTrace (prefixWord ++ tailWord_2586914) baseStart_2586914 baseEnd_2586914 := by
    simpa [prefixWord, tailWord_2586914, baseEnd_2586914] using wordTrace_append hprefix tailTrace_2586914
  have hstable : (prefixWord ++ tailWord_2586914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2586914).length < 2 ^ (prefixWord ++ tailWord_2586914).sum := by decide
  have hdescent : baseEnd_2586914 < baseStart_2586914 := by decide
  rcases family_descends (prefixWord ++ tailWord_2586914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2587027 : List Nat := [1, 1, 1, 2, 1, 2, 1, 1, 1, 7, 5]
def baseStart_2587027 : Nat := 118140960795 + 2587027 * 2 ^ 59
def prefixEnd_2587027 : Nat := 4983230072969 + 3 ^ 40 * 2587027 * 2
def baseEnd_2587027 : Nat := 1328388317159154978664985

theorem tailTrace_2587027 : CollatzResearch.WordTrace tailWord_2587027 prefixEnd_2587027 1328388317159154978664985 := by
  unfold tailWord_2587027
  simp only [CollatzResearch.WordTrace]
  refine ⟨94356626398650482880903335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62904417599100321920602223 94356626398650482880903335)
  ·
    refine ⟨141534939597975724321355003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94356626398650482880903335 141534939597975724321355003)
    ·
      refine ⟨212302409396963586482032505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141534939597975724321355003 212302409396963586482032505)
      ·
        refine ⟨159226807047722689861524379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212302409396963586482032505 159226807047722689861524379)
        ·
          refine ⟨238840210571584034792286569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159226807047722689861524379 238840210571584034792286569)
          ·
            refine ⟨179130157928688026094214927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 238840210571584034792286569 179130157928688026094214927)
            ·
              refine ⟨268695236893032039141322391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 179130157928688026094214927 268695236893032039141322391)
              ·
                refine ⟨403042855339548058711983587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 268695236893032039141322391 403042855339548058711983587)
                ·
                  refine ⟨604564283009322088067975381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 403042855339548058711983587 604564283009322088067975381)
                  ·
                    refine ⟨14169475383030986439093173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 604564283009322088067975381 14169475383030986439093173)
                    ·
                      refine ⟨1328388317159154978664985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14169475383030986439093173 1328388317159154978664985)
                      ·
                        rfl

theorem cell23_2587027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 7, 5].length) (baseStart_2587027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2587027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2587027 prefixEnd_2587027 := by exact prefixLift 2587027
  have htrace : WordTrace (prefixWord ++ tailWord_2587027) baseStart_2587027 baseEnd_2587027 := by
    simpa [prefixWord, tailWord_2587027, baseEnd_2587027] using wordTrace_append hprefix tailTrace_2587027
  have hstable : (prefixWord ++ tailWord_2587027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2587027).length < 2 ^ (prefixWord ++ tailWord_2587027).sum := by decide
  have hdescent : baseEnd_2587027 < baseStart_2587027 := by decide
  rcases family_descends (prefixWord ++ tailWord_2587027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2587034 : List Nat := [3, 1, 1, 4, 1, 2, 1, 1, 3, 6]
def baseStart_2587034 : Nat := 118140960795 + 2587034 * 2 ^ 59
def prefixEnd_2587034 : Nat := 4983230072969 + 3 ^ 40 * 2587034 * 2
def baseEnd_2587034 : Nat := 442797303841245483759151

theorem tailTrace_2587034 : CollatzResearch.WordTrace tailWord_2587034 prefixEnd_2587034 442797303841245483759151 := by
  unfold tailWord_2587034
  simp only [CollatzResearch.WordTrace]
  refine ⟨23589220427406280769102039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62904587806416748717605437 23589220427406280769102039)
  ·
    refine ⟨35383830641109421153653059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23589220427406280769102039 35383830641109421153653059)
    ·
      refine ⟨53075745961664131730479589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35383830641109421153653059 53075745961664131730479589)
      ·
        refine ⟨9951702367812024699464923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53075745961664131730479589 9951702367812024699464923)
        ·
          refine ⟨14927553551718037049197385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9951702367812024699464923 14927553551718037049197385)
          ·
            refine ⟨11195665163788527786898039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14927553551718037049197385 11195665163788527786898039)
            ·
              refine ⟨16793497745682791680347059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11195665163788527786898039 16793497745682791680347059)
              ·
                refine ⟨25190246618524187520520589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16793497745682791680347059 25190246618524187520520589)
                ·
                  refine ⟨9446342481946570320195221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25190246618524187520520589 9446342481946570320195221)
                  ·
                    refine ⟨442797303841245483759151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9446342481946570320195221 442797303841245483759151)
                    ·
                      rfl

theorem cell23_2587034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 3, 6].length) (baseStart_2587034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2587034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2587034 prefixEnd_2587034 := by exact prefixLift 2587034
  have htrace : WordTrace (prefixWord ++ tailWord_2587034) baseStart_2587034 baseEnd_2587034 := by
    simpa [prefixWord, tailWord_2587034, baseEnd_2587034] using wordTrace_append hprefix tailTrace_2587034
  have hstable : (prefixWord ++ tailWord_2587034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2587034).length < 2 ^ (prefixWord ++ tailWord_2587034).sum := by decide
  have hdescent : baseEnd_2587034 < baseStart_2587034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2587034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2587058 : List Nat := [3, 2, 1, 1, 1, 1, 4, 3, 3, 2, 2]
def baseStart_2587058 : Nat := 118140960795 + 2587058 * 2 ^ 59
def prefixEnd_2587058 : Nat := 4983230072969 + 3 ^ 40 * 2587058 * 2
def baseEnd_2587058 : Nat := 1328404235059444357377343

theorem tailTrace_2587058 : CollatzResearch.WordTrace tailWord_2587058 prefixEnd_2587058 1328404235059444357377343 := by
  unfold tailWord_2587058
  simp only [CollatzResearch.WordTrace]
  refine ⟨23589439265384543793820457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62905171374358783450187885 23589439265384543793820457)
  ·
    refine ⟨17692079449038407845365343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23589439265384543793820457 17692079449038407845365343)
    ·
      refine ⟨26538119173557611768048015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17692079449038407845365343 26538119173557611768048015)
      ·
        refine ⟨39807178760336417652072023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26538119173557611768048015 39807178760336417652072023)
        ·
          refine ⟨59710768140504626478108035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39807178760336417652072023 59710768140504626478108035)
          ·
            refine ⟨89566152210756939717162053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59710768140504626478108035 89566152210756939717162053)
            ·
              refine ⟨16793653539516926196967885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 89566152210756939717162053 16793653539516926196967885)
              ·
                refine ⟨6297620077318847323862957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16793653539516926196967885 6297620077318847323862957)
                ·
                  refine ⟨2361607528994567746448609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6297620077318847323862957 2361607528994567746448609)
                  ·
                    refine ⟨1771205646745925809836457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2361607528994567746448609 1771205646745925809836457)
                    ·
                      refine ⟨1328404235059444357377343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1771205646745925809836457 1328404235059444357377343)
                      ·
                        rfl

theorem cell23_2587058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 3, 3, 2, 2].length) (baseStart_2587058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2587058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2587058 prefixEnd_2587058 := by exact prefixLift 2587058
  have htrace : WordTrace (prefixWord ++ tailWord_2587058) baseStart_2587058 baseEnd_2587058 := by
    simpa [prefixWord, tailWord_2587058, baseEnd_2587058] using wordTrace_append hprefix tailTrace_2587058
  have hstable : (prefixWord ++ tailWord_2587058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2587058).length < 2 ^ (prefixWord ++ tailWord_2587058).sum := by decide
  have hdescent : baseEnd_2587058 < baseStart_2587058 := by decide
  rcases family_descends (prefixWord ++ tailWord_2587058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2587068 : List Nat := [2, 2, 2, 4, 1, 1, 2, 3, 2, 4]
def baseStart_2587068 : Nat := 118140960795 + 2587068 * 2 ^ 59
def prefixEnd_2587068 : Nat := 4983230072969 + 3 ^ 40 * 2587068 * 2
def baseEnd_2587068 : Nat := 442803123288663106084099

theorem tailTrace_2587068 : CollatzResearch.WordTrace tailWord_2587068 prefixEnd_2587068 442803123288663106084099 := by
  unfold tailWord_2587068
  simp only [CollatzResearch.WordTrace]
  refine ⟨47179060895750973441572929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62905414527667964588763905 47179060895750973441572929)
  ·
    refine ⟨35384295671813230081179697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47179060895750973441572929 35384295671813230081179697)
    ·
      refine ⟨26538221753859922560884773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35384295671813230081179697 26538221753859922560884773)
      ·
        refine ⟨4975916578848735480165895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26538221753859922560884773 4975916578848735480165895)
        ·
          refine ⟨7463874868273103220248843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4975916578848735480165895 7463874868273103220248843)
          ·
            refine ⟨11195812302409654830373265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7463874868273103220248843 11195812302409654830373265)
            ·
              refine ⟨8396859226807241122779949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11195812302409654830373265 8396859226807241122779949)
              ·
                refine ⟨3148822210052715421042481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8396859226807241122779949 3148822210052715421042481)
                ·
                  refine ⟨2361616657539536565781861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3148822210052715421042481 2361616657539536565781861)
                  ·
                    refine ⟨442803123288663106084099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2361616657539536565781861 442803123288663106084099)
                    ·
                      rfl

theorem cell23_2587068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 3, 2, 4].length) (baseStart_2587068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2587068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2587068 prefixEnd_2587068 := by exact prefixLift 2587068
  have htrace : WordTrace (prefixWord ++ tailWord_2587068) baseStart_2587068 baseEnd_2587068 := by
    simpa [prefixWord, tailWord_2587068, baseEnd_2587068] using wordTrace_append hprefix tailTrace_2587068
  have hstable : (prefixWord ++ tailWord_2587068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2587068).length < 2 ^ (prefixWord ++ tailWord_2587068).sum := by decide
  have hdescent : baseEnd_2587068 < baseStart_2587068 := by decide
  rcases family_descends (prefixWord ++ tailWord_2587068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2587092 : List Nat := [2, 4, 1, 2, 2, 1, 1, 5, 1, 2, 2]
def baseStart_2587092 : Nat := 118140960795 + 2587092 * 2 ^ 59
def prefixEnd_2587092 : Nat := 4983230072969 + 3 ^ 40 * 2587092 * 2
def baseEnd_2587092 : Nat := 1328421693401697224352187

theorem tailTrace_2587092 : CollatzResearch.WordTrace tailWord_2587092 prefixEnd_2587092 1328421693401697224352187 := by
  unfold tailWord_2587092
  simp only [CollatzResearch.WordTrace]
  refine ⟨47179498571707499491009765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62905998095609999321346353 47179498571707499491009765)
  ·
    refine ⟨8846155982195156154564331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47179498571707499491009765 8846155982195156154564331)
    ·
      refine ⟨13269233973292734231846497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8846155982195156154564331 13269233973292734231846497)
      ·
        refine ⟨9951925479969550673884873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13269233973292734231846497 9951925479969550673884873)
        ·
          refine ⟨7463944109977163005413655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9951925479969550673884873 7463944109977163005413655)
          ·
            refine ⟨11195916164965744508120483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7463944109977163005413655 11195916164965744508120483)
            ·
              refine ⟨16793874247448616762180725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11195916164965744508120483 16793874247448616762180725)
              ·
                refine ⟨1574425710698307821454443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16793874247448616762180725 1574425710698307821454443)
                ·
                  refine ⟨2361638566047461732181665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1574425710698307821454443 2361638566047461732181665)
                  ·
                    refine ⟨1771228924535596299136249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2361638566047461732181665 1771228924535596299136249)
                    ·
                      refine ⟨1328421693401697224352187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1771228924535596299136249 1328421693401697224352187)
                      ·
                        rfl

theorem cell23_2587092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 5, 1, 2, 2].length) (baseStart_2587092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2587092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2587092 prefixEnd_2587092 := by exact prefixLift 2587092
  have htrace : WordTrace (prefixWord ++ tailWord_2587092) baseStart_2587092 baseEnd_2587092 := by
    simpa [prefixWord, tailWord_2587092, baseEnd_2587092] using wordTrace_append hprefix tailTrace_2587092
  have hstable : (prefixWord ++ tailWord_2587092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2587092).length < 2 ^ (prefixWord ++ tailWord_2587092).sum := by decide
  have hdescent : baseEnd_2587092 < baseStart_2587092 := by decide
  rcases family_descends (prefixWord ++ tailWord_2587092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2587165 : List Nat := [1, 4, 2, 2, 1, 2, 2, 1, 4, 2, 2]
def baseStart_2587165 : Nat := 118140960795 + 2587165 * 2 ^ 59
def prefixEnd_2587165 : Nat := 4983230072969 + 3 ^ 40 * 2587165 * 2
def baseEnd_2587165 : Nat := 1328459177489475438739351

theorem tailTrace_2587165 : CollatzResearch.WordTrace tailWord_2587165 prefixEnd_2587165 1328459177489475438739351 := by
  unfold tailWord_2587165
  simp only [CollatzResearch.WordTrace]
  refine ⟨94361659672150532449426949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62907773114767021632951299 94361659672150532449426949)
  ·
    refine ⟨17692811188528224834267553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94361659672150532449426949 17692811188528224834267553)
    ·
      refine ⟨13269608391396168625700665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17692811188528224834267553 13269608391396168625700665)
      ·
        refine ⟨9952206293547126469275499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13269608391396168625700665 9952206293547126469275499)
        ·
          refine ⟨14928309440320689703913249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9952206293547126469275499 14928309440320689703913249)
          ·
            refine ⟨11196232080240517277934937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14928309440320689703913249 11196232080240517277934937)
            ·
              refine ⟨8397174060180387958451203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11196232080240517277934937 8397174060180387958451203)
              ·
                refine ⟨12595761090270581937676805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8397174060180387958451203 12595761090270581937676805)
                ·
                  refine ⟨2361705204425734113314401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12595761090270581937676805 2361705204425734113314401)
                  ·
                    refine ⟨1771278903319300584985801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2361705204425734113314401 1771278903319300584985801)
                    ·
                      refine ⟨1328459177489475438739351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1771278903319300584985801 1328459177489475438739351)
                      ·
                        rfl

theorem cell23_2587165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 1, 4, 2, 2].length) (baseStart_2587165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2587165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2587165 prefixEnd_2587165 := by exact prefixLift 2587165
  have htrace : WordTrace (prefixWord ++ tailWord_2587165) baseStart_2587165 baseEnd_2587165 := by
    simpa [prefixWord, tailWord_2587165, baseEnd_2587165] using wordTrace_append hprefix tailTrace_2587165
  have hstable : (prefixWord ++ tailWord_2587165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2587165).length < 2 ^ (prefixWord ++ tailWord_2587165).sum := by decide
  have hdescent : baseEnd_2587165 < baseStart_2587165 := by decide
  rcases family_descends (prefixWord ++ tailWord_2587165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2587171 : List Nat := [1, 1, 1, 4, 4, 1, 3, 1, 7]
def baseStart_2587171 : Nat := 118140960795 + 2587171 * 2 ^ 59
def prefixEnd_2587171 : Nat := 4983230072969 + 3 ^ 40 * 2587171 * 2
def baseEnd_2587171 : Nat := 147606917597044712807147

theorem tailTrace_2587171 : CollatzResearch.WordTrace tailWord_2587171 prefixEnd_2587171 147606917597044712807147 := by
  unfold tailWord_2587171
  simp only [CollatzResearch.WordTrace]
  refine ⟨94361878510128795474145367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62907919006752530316096911 94361878510128795474145367)
  ·
    refine ⟨141542817765193193211218051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94361878510128795474145367 141542817765193193211218051)
    ·
      refine ⟨212314226647789789816827077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141542817765193193211218051 212314226647789789816827077)
      ·
        refine ⟨39808917496460585590655077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 212314226647789789816827077 39808917496460585590655077)
        ·
          refine ⟨7464172030586359798247827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39808917496460585590655077 7464172030586359798247827)
          ·
            refine ⟨11196258045879539697371741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7464172030586359798247827 11196258045879539697371741)
            ·
              refine ⟨4198596767204827386514403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11196258045879539697371741 4198596767204827386514403)
              ·
                refine ⟨6297895150807241079771605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4198596767204827386514403 6297895150807241079771605)
                ·
                  refine ⟨147606917597044712807147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6297895150807241079771605 147606917597044712807147)
                  ·
                    rfl

theorem cell23_2587171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 1, 7].length) (baseStart_2587171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2587171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2587171 prefixEnd_2587171 := by exact prefixLift 2587171
  have htrace : WordTrace (prefixWord ++ tailWord_2587171) baseStart_2587171 baseEnd_2587171 := by
    simpa [prefixWord, tailWord_2587171, baseEnd_2587171] using wordTrace_append hprefix tailTrace_2587171
  have hstable : (prefixWord ++ tailWord_2587171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2587171).length < 2 ^ (prefixWord ++ tailWord_2587171).sum := by decide
  have hdescent : baseEnd_2587171 < baseStart_2587171 := by decide
  rcases family_descends (prefixWord ++ tailWord_2587171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2587184 : List Nat := [2, 1, 1, 1, 2, 3, 2, 1, 3, 7]
def baseStart_2587184 : Nat := 118140960795 + 2587184 * 2 ^ 59
def prefixEnd_2587184 : Nat := 4983230072969 + 3 ^ 40 * 2587184 * 2
def baseEnd_2587184 : Nat := 442822977873970288133921

theorem tailTrace_2587184 : CollatzResearch.WordTrace tailWord_2587184 prefixEnd_2587184 442822977873970288133921 := by
  unfold tailWord_2587184
  simp only [CollatzResearch.WordTrace]
  refine ⟨47181176329540849347184303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62908235106054465796245737 47181176329540849347184303)
  ·
    refine ⟨70771764494311274020776455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47181176329540849347184303 70771764494311274020776455)
    ·
      refine ⟨106157646741466911031164683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70771764494311274020776455 106157646741466911031164683)
      ·
        refine ⟨159236470112200366546747025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106157646741466911031164683 159236470112200366546747025)
        ·
          refine ⟨119427352584150274910060269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159236470112200366546747025 119427352584150274910060269)
          ·
            refine ⟨44785257219056353091272601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 119427352584150274910060269 44785257219056353091272601)
            ·
              refine ⟨33588942914292264818454451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44785257219056353091272601 33588942914292264818454451)
              ·
                refine ⟨50383414371438397227681677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33588942914292264818454451 50383414371438397227681677)
                ·
                  refine ⟨18893780389289398960380629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50383414371438397227681677 18893780389289398960380629)
                  ·
                    refine ⟨442822977873970288133921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18893780389289398960380629 442822977873970288133921)
                    ·
                      rfl

theorem cell23_2587184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 3, 7].length) (baseStart_2587184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2587184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2587184 prefixEnd_2587184 := by exact prefixLift 2587184
  have htrace : WordTrace (prefixWord ++ tailWord_2587184) baseStart_2587184 baseEnd_2587184 := by
    simpa [prefixWord, tailWord_2587184, baseEnd_2587184] using wordTrace_append hprefix tailTrace_2587184
  have hstable : (prefixWord ++ tailWord_2587184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2587184).length < 2 ^ (prefixWord ++ tailWord_2587184).sum := by decide
  have hdescent : baseEnd_2587184 < baseStart_2587184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2587184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2587231 : List Nat := [1, 1, 2, 3, 1, 1, 1, 2, 7, 4]
def baseStart_2587231 : Nat := 118140960795 + 2587231 * 2 ^ 59
def prefixEnd_2587231 : Nat := 4983230072969 + 3 ^ 40 * 2587231 * 2
def baseEnd_2587231 : Nat := 442831022404224060171349

theorem tailTrace_2587231 : CollatzResearch.WordTrace tailWord_2587231 prefixEnd_2587231 442831022404224060171349 := by
  unfold tailWord_2587231
  simp only [CollatzResearch.WordTrace]
  refine ⟨94364066889911425721329547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62909377926607617147553031 94364066889911425721329547)
  ·
    refine ⟨141546100334867138581994321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94364066889911425721329547 141546100334867138581994321)
    ·
      refine ⟨106159575251150353936495741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141546100334867138581994321 106159575251150353936495741)
      ·
        refine ⟨39809840719181382726185903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106159575251150353936495741 39809840719181382726185903)
        ·
          refine ⟨59714761078772074089278855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39809840719181382726185903 59714761078772074089278855)
          ·
            refine ⟨89572141618158111133918283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59714761078772074089278855 89572141618158111133918283)
            ·
              refine ⟨134358212427237166700877425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89572141618158111133918283 134358212427237166700877425)
              ·
                refine ⟨100768659320427875025658069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 134358212427237166700877425 100768659320427875025658069)
                ·
                  refine ⟨2361765452822528320913861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 100768659320427875025658069 2361765452822528320913861)
                  ·
                    refine ⟨442831022404224060171349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2361765452822528320913861 442831022404224060171349)
                    ·
                      rfl

theorem cell23_2587231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 7, 4].length) (baseStart_2587231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2587231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2587231 prefixEnd_2587231 := by exact prefixLift 2587231
  have htrace : WordTrace (prefixWord ++ tailWord_2587231) baseStart_2587231 baseEnd_2587231 := by
    simpa [prefixWord, tailWord_2587231, baseEnd_2587231] using wordTrace_append hprefix tailTrace_2587231
  have hstable : (prefixWord ++ tailWord_2587231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2587231).length < 2 ^ (prefixWord ++ tailWord_2587231).sum := by decide
  have hdescent : baseEnd_2587231 < baseStart_2587231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2587231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2587241 : List Nat := [1, 2, 1, 1, 1, 4, 1, 4, 1, 4, 3]
def baseStart_2587241 : Nat := 118140960795 + 2587241 * 2 ^ 59
def prefixEnd_2587241 : Nat := 4983230072969 + 3 ^ 40 * 2587241 * 2
def baseEnd_2587241 : Nat := 1328498202019217141389001

theorem tailTrace_2587241 : CollatzResearch.WordTrace tailWord_2587241 prefixEnd_2587241 1328498202019217141389001 := by
  unfold tailWord_2587241
  simp only [CollatzResearch.WordTrace]
  refine ⟨94364431619875197429193577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62909621079916798286129051 94364431619875197429193577)
  ·
    refine ⟨70773323714906398071895183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94364431619875197429193577 70773323714906398071895183)
    ·
      refine ⟨106159985572359597107842775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70773323714906398071895183 106159985572359597107842775)
      ·
        refine ⟨159239978358539395661764163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106159985572359597107842775 159239978358539395661764163)
        ·
          refine ⟨238859967537809093492646245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159239978358539395661764163 238859967537809093492646245)
          ·
            refine ⟨44786243913339205029871171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 238859967537809093492646245 44786243913339205029871171)
            ·
              refine ⟨67179365870008807544806757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44786243913339205029871171 67179365870008807544806757)
              ·
                refine ⟨12596131100626651414651267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67179365870008807544806757 12596131100626651414651267)
                ·
                  refine ⟨18894196650939977121976901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12596131100626651414651267 18894196650939977121976901)
                  ·
                    refine ⟨3542661872051245710370669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18894196650939977121976901 3542661872051245710370669)
                    ·
                      refine ⟨1328498202019217141389001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3542661872051245710370669 1328498202019217141389001)
                      ·
                        rfl

theorem cell23_2587241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 4, 1, 4, 3].length) (baseStart_2587241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2587241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2587241 prefixEnd_2587241 := by exact prefixLift 2587241
  have htrace : WordTrace (prefixWord ++ tailWord_2587241) baseStart_2587241 baseEnd_2587241 := by
    simpa [prefixWord, tailWord_2587241, baseEnd_2587241] using wordTrace_append hprefix tailTrace_2587241
  have hstable : (prefixWord ++ tailWord_2587241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2587241).length < 2 ^ (prefixWord ++ tailWord_2587241).sum := by decide
  have hdescent : baseEnd_2587241 < baseStart_2587241 := by decide
  rcases family_descends (prefixWord ++ tailWord_2587241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2587282 : List Nat := [3, 2, 3, 1, 2, 1, 2, 4, 1, 4]
def baseStart_2587282 : Nat := 118140960795 + 2587282 * 2 ^ 59
def prefixEnd_2587282 : Nat := 4983230072969 + 3 ^ 40 * 2587282 * 2
def baseEnd_2587282 : Nat := 442839751575350493658771

theorem tailTrace_2587282 : CollatzResearch.WordTrace tailWord_2587282 prefixEnd_2587282 442839751575350493658771 := by
  unfold tailWord_2587282
  simp only [CollatzResearch.WordTrace]
  refine ⟨23591481753181665357859025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62910618008484440954290733 23591481753181665357859025)
  ·
    refine ⟨17693611314886249018394269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23591481753181665357859025 17693611314886249018394269)
    ·
      refine ⟨6635104243082343381897851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17693611314886249018394269 6635104243082343381897851)
      ·
        refine ⟨9952656364623515072846777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6635104243082343381897851 9952656364623515072846777)
        ·
          refine ⟨7464492273467636304635083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9952656364623515072846777 7464492273467636304635083)
          ·
            refine ⟨11196738410201454456952625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7464492273467636304635083 11196738410201454456952625)
            ·
              refine ⟨8397553807651090842714469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11196738410201454456952625 8397553807651090842714469)
              ·
                refine ⟨1574541338934579533008963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8397553807651090842714469 1574541338934579533008963)
                ·
                  refine ⟨2361812008401869299513445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1574541338934579533008963 2361812008401869299513445)
                  ·
                    refine ⟨442839751575350493658771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2361812008401869299513445 442839751575350493658771)
                    ·
                      rfl

theorem cell23_2587282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 4, 1, 4].length) (baseStart_2587282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2587282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2587282 prefixEnd_2587282 := by exact prefixLift 2587282
  have htrace : WordTrace (prefixWord ++ tailWord_2587282) baseStart_2587282 baseEnd_2587282 := by
    simpa [prefixWord, tailWord_2587282, baseEnd_2587282] using wordTrace_append hprefix tailTrace_2587282
  have hstable : (prefixWord ++ tailWord_2587282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2587282).length < 2 ^ (prefixWord ++ tailWord_2587282).sum := by decide
  have hdescent : baseEnd_2587282 < baseStart_2587282 := by decide
  rcases family_descends (prefixWord ++ tailWord_2587282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2587321 : List Nat := [1, 2, 1, 4, 1, 1, 1, 3, 3, 6]
def baseStart_2587321 : Nat := 118140960795 + 2587321 * 2 ^ 59
def prefixEnd_2587321 : Nat := 4983230072969 + 3 ^ 40 * 2587321 * 2
def baseEnd_2587321 : Nat := 442846426823858942796211

theorem tailTrace_2587321 : CollatzResearch.WordTrace tailWord_2587321 prefixEnd_2587321 442846426823858942796211 := by
  unfold tailWord_2587321
  simp only [CollatzResearch.WordTrace]
  refine ⟨94367349459585371092105817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62911566306390247394737211 94367349459585371092105817)
  ·
    refine ⟨70775512094689028319079363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94367349459585371092105817 70775512094689028319079363)
    ·
      refine ⟨106163268142033542478619045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70775512094689028319079363 106163268142033542478619045)
      ·
        refine ⟨19905612776631289214741071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106163268142033542478619045 19905612776631289214741071)
        ·
          refine ⟨29858419164946933822111607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19905612776631289214741071 29858419164946933822111607)
          ·
            refine ⟨44787628747420400733167411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29858419164946933822111607 44787628747420400733167411)
            ·
              refine ⟨67181443121130601099751117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44787628747420400733167411 67181443121130601099751117)
              ·
                refine ⟨25193041170423975412406669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67181443121130601099751117 25193041170423975412406669)
                ·
                  refine ⟨9447390438908990779652501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25193041170423975412406669 9447390438908990779652501)
                  ·
                    refine ⟨442846426823858942796211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9447390438908990779652501 442846426823858942796211)
                    ·
                      rfl

theorem cell23_2587321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 3, 6].length) (baseStart_2587321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2587321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2587321 prefixEnd_2587321 := by exact prefixLift 2587321
  have htrace : WordTrace (prefixWord ++ tailWord_2587321) baseStart_2587321 baseEnd_2587321 := by
    simpa [prefixWord, tailWord_2587321, baseEnd_2587321] using wordTrace_append hprefix tailTrace_2587321
  have hstable : (prefixWord ++ tailWord_2587321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2587321).length < 2 ^ (prefixWord ++ tailWord_2587321).sum := by decide
  have hdescent : baseEnd_2587321 < baseStart_2587321 := by decide
  rcases family_descends (prefixWord ++ tailWord_2587321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2587332 : List Nat := [2, 3, 3, 1, 1, 3, 1, 2, 2, 3, 2]
def baseStart_2587332 : Nat := 118140960795 + 2587332 * 2 ^ 59
def prefixEnd_2587332 : Nat := 4983230072969 + 3 ^ 40 * 2587332 * 2
def baseEnd_2587332 : Nat := 1328544928758776285351083

theorem tailTrace_2587332 : CollatzResearch.WordTrace tailWord_2587332 prefixEnd_2587332 1328544928758776285351083 := by
  unfold tailWord_2587332
  simp only [CollatzResearch.WordTrace]
  refine ⟨47183875331272759985378125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62911833775030346647170833 47183875331272759985378125)
  ·
    refine ⟨17693953249227284994516797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47183875331272759985378125 17693953249227284994516797)
    ·
      refine ⟨6635232468460231872943799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17693953249227284994516797 6635232468460231872943799)
      ·
        refine ⟨9952848702690347809415699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6635232468460231872943799 9952848702690347809415699)
        ·
          refine ⟨14929273054035521714123549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9952848702690347809415699 14929273054035521714123549)
          ·
            refine ⟨5598477395263320642796331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14929273054035521714123549 5598477395263320642796331)
            ·
              refine ⟨8397716092894980964194497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5598477395263320642796331 8397716092894980964194497)
              ·
                refine ⟨6298287069671235723145873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8397716092894980964194497 6298287069671235723145873)
                ·
                  refine ⟨4723715302253426792359405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6298287069671235723145873 4723715302253426792359405)
                  ·
                    refine ⟨1771393238345035047134777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4723715302253426792359405 1771393238345035047134777)
                    ·
                      refine ⟨1328544928758776285351083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1771393238345035047134777 1328544928758776285351083)
                      ·
                        rfl

theorem cell23_2587332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 2, 2, 3, 2].length) (baseStart_2587332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2587332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2587332 prefixEnd_2587332 := by exact prefixLift 2587332
  have htrace : WordTrace (prefixWord ++ tailWord_2587332) baseStart_2587332 baseEnd_2587332 := by
    simpa [prefixWord, tailWord_2587332, baseEnd_2587332] using wordTrace_append hprefix tailTrace_2587332
  have hstable : (prefixWord ++ tailWord_2587332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2587332).length < 2 ^ (prefixWord ++ tailWord_2587332).sum := by decide
  have hdescent : baseEnd_2587332 < baseStart_2587332 := by decide
  rcases family_descends (prefixWord ++ tailWord_2587332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2587351 : List Nat := [1, 1, 3, 2, 1, 4, 1, 10]
def baseStart_2587351 : Nat := 118140960795 + 2587351 * 2 ^ 59
def prefixEnd_2587351 : Nat := 4983230072969 + 3 ^ 40 * 2587351 * 2
def baseEnd_2587351 : Nat := 49205729070044878185685

theorem tailTrace_2587351 : CollatzResearch.WordTrace tailWord_2587351 prefixEnd_2587351 49205729070044878185685 := by
  unfold tailWord_2587351
  simp only [CollatzResearch.WordTrace]
  refine ⟨94368443649476686215697907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62912295766317790810465271 94368443649476686215697907)
  ·
    refine ⟨141552665474215029323546861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94368443649476686215697907 141552665474215029323546861)
    ·
      refine ⟨53082249552830635996330073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141552665474215029323546861 53082249552830635996330073)
      ·
        refine ⟨39811687164622976997247555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53082249552830635996330073 39811687164622976997247555)
        ·
          refine ⟨59717530746934465495871333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39811687164622976997247555 59717530746934465495871333)
          ·
            refine ⟨11197037015050212280475875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59717530746934465495871333 11197037015050212280475875)
            ·
              refine ⟨16795555522575318420713813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11197037015050212280475875 16795555522575318420713813)
              ·
                refine ⟨49205729070044878185685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 16795555522575318420713813 49205729070044878185685)
                ·
                  rfl

theorem cell23_2587351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 10].length) (baseStart_2587351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2587351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2587351 prefixEnd_2587351 := by exact prefixLift 2587351
  have htrace : WordTrace (prefixWord ++ tailWord_2587351) baseStart_2587351 baseEnd_2587351 := by
    simpa [prefixWord, tailWord_2587351, baseEnd_2587351] using wordTrace_append hprefix tailTrace_2587351
  have hstable : (prefixWord ++ tailWord_2587351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2587351).length < 2 ^ (prefixWord ++ tailWord_2587351).sum := by decide
  have hdescent : baseEnd_2587351 < baseStart_2587351 := by decide
  rcases family_descends (prefixWord ++ tailWord_2587351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2587365 : List Nat := [1, 3, 1, 4, 1, 3, 1, 1, 3, 2, 3]
def baseStart_2587365 : Nat := 118140960795 + 2587365 * 2 ^ 59
def prefixEnd_2587365 : Nat := 4983230072969 + 3 ^ 40 * 2587365 * 2
def baseEnd_2587365 : Nat := 1328561873620374656238431

theorem tailTrace_2587365 : CollatzResearch.WordTrace tailWord_2587365 prefixEnd_2587365 1328561873620374656238431 := by
  unfold tailWord_2587365
  simp only [CollatzResearch.WordTrace]
  refine ⟨94368954271425966606707549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62912636180950644404471699 94368954271425966606707549)
  ·
    refine ⟨35388357851784737477515331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94368954271425966606707549 35388357851784737477515331)
    ·
      refine ⟨53082536777677106216272997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35388357851784737477515331 53082536777677106216272997)
      ·
        refine ⟨9952975645814457415551187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53082536777677106216272997 9952975645814457415551187)
        ·
          refine ⟨14929463468721686123326781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9952975645814457415551187 14929463468721686123326781)
          ·
            refine ⟨5598548800770632296247543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14929463468721686123326781 5598548800770632296247543)
            ·
              refine ⟨8397823201155948444371315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5598548800770632296247543 8397823201155948444371315)
              ·
                refine ⟨12596734801733922666556973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8397823201155948444371315 12596734801733922666556973)
                ·
                  refine ⟨4723775550650220999958865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12596734801733922666556973 4723775550650220999958865)
                  ·
                    refine ⟨3542831662987665749969149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4723775550650220999958865 3542831662987665749969149)
                    ·
                      refine ⟨1328561873620374656238431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3542831662987665749969149 1328561873620374656238431)
                      ·
                        rfl

theorem cell23_2587365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_2587365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2587365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2587365 prefixEnd_2587365 := by exact prefixLift 2587365
  have htrace : WordTrace (prefixWord ++ tailWord_2587365) baseStart_2587365 baseEnd_2587365 := by
    simpa [prefixWord, tailWord_2587365, baseEnd_2587365] using wordTrace_append hprefix tailTrace_2587365
  have hstable : (prefixWord ++ tailWord_2587365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2587365).length < 2 ^ (prefixWord ++ tailWord_2587365).sum := by decide
  have hdescent : baseEnd_2587365 < baseStart_2587365 := by decide
  rcases family_descends (prefixWord ++ tailWord_2587365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2587418 : List Nat := [3, 1, 1, 3, 2, 1, 1, 2, 2, 3, 4]
def baseStart_2587418 : Nat := 118140960795 + 2587418 * 2 ^ 59
def prefixEnd_2587418 : Nat := 4983230072969 + 3 ^ 40 * 2587418 * 2
def baseEnd_2587418 : Nat := 1328589088095062948875687

theorem tailTrace_2587418 : CollatzResearch.WordTrace tailWord_2587418 prefixEnd_2587418 1328589088095062948875687 := by
  unfold tailWord_2587418
  simp only [CollatzResearch.WordTrace]
  refine ⟨23592721835058489164596727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62913924893489304438924605 23592721835058489164596727)
  ·
    refine ⟨35389082752587733746895091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23592721835058489164596727 35389082752587733746895091)
    ·
      refine ⟨53083624128881600620342637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35389082752587733746895091 53083624128881600620342637)
      ·
        refine ⟨19906359048330600232628489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53083624128881600620342637 19906359048330600232628489)
        ·
          refine ⟨14929769286247950174471367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19906359048330600232628489 14929769286247950174471367)
          ·
            refine ⟨22394653929371925261707051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14929769286247950174471367 22394653929371925261707051)
            ·
              refine ⟨33591980894057887892560577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22394653929371925261707051 33591980894057887892560577)
              ·
                refine ⟨25193985670543415919420433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33591980894057887892560577 25193985670543415919420433)
                ·
                  refine ⟨18895489252907561939565325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25193985670543415919420433 18895489252907561939565325)
                  ·
                    refine ⟨7085808469840335727336997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18895489252907561939565325 7085808469840335727336997)
                    ·
                      refine ⟨1328589088095062948875687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7085808469840335727336997 1328589088095062948875687)
                      ·
                        rfl

theorem cell23_2587418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_2587418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2587418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2587418 prefixEnd_2587418 := by exact prefixLift 2587418
  have htrace : WordTrace (prefixWord ++ tailWord_2587418) baseStart_2587418 baseEnd_2587418 := by
    simpa [prefixWord, tailWord_2587418, baseEnd_2587418] using wordTrace_append hprefix tailTrace_2587418
  have hstable : (prefixWord ++ tailWord_2587418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2587418).length < 2 ^ (prefixWord ++ tailWord_2587418).sum := by decide
  have hdescent : baseEnd_2587418 < baseStart_2587418 := by decide
  rcases family_descends (prefixWord ++ tailWord_2587418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2587448 : List Nat := [2, 1, 2, 1, 3, 2, 1, 1, 4, 2, 4]
def baseStart_2587448 : Nat := 118140960795 + 2587448 * 2 ^ 59
def prefixEnd_2587448 : Nat := 4983230072969 + 3 ^ 40 * 2587448 * 2
def baseEnd_2587448 : Nat := 1328604492514697831500549

theorem tailTrace_2587448 : CollatzResearch.WordTrace tailWord_2587448 prefixEnd_2587448 1328604492514697831500549 := by
  unfold tailWord_2587448
  simp only [CollatzResearch.WordTrace]
  refine ⟨47185990765062635890989499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62914654353416847854652665 47185990765062635890989499)
  ·
    refine ⟨70778986147593953836484249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47185990765062635890989499 70778986147593953836484249)
    ·
      refine ⟨53084239610695465377363187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70778986147593953836484249 53084239610695465377363187)
      ·
        refine ⟨79626359416043198066044781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53084239610695465377363187 79626359416043198066044781)
        ·
          refine ⟨29859884781016199274766793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79626359416043198066044781 29859884781016199274766793)
          ·
            refine ⟨22394913585762149456075095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29859884781016199274766793 22394913585762149456075095)
            ·
              refine ⟨33592370378643224184112643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22394913585762149456075095 33592370378643224184112643)
              ·
                refine ⟨50388555567964836276168965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33592370378643224184112643 50388555567964836276168965)
                ·
                  refine ⟨9447854168993406801781681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50388555567964836276168965 9447854168993406801781681)
                  ·
                    refine ⟨7085890626745055101336261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9447854168993406801781681 7085890626745055101336261)
                    ·
                      refine ⟨1328604492514697831500549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7085890626745055101336261 1328604492514697831500549)
                      ·
                        rfl

theorem cell23_2587448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 4, 2, 4].length) (baseStart_2587448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2587448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2587448 prefixEnd_2587448 := by exact prefixLift 2587448
  have htrace : WordTrace (prefixWord ++ tailWord_2587448) baseStart_2587448 baseEnd_2587448 := by
    simpa [prefixWord, tailWord_2587448, baseEnd_2587448] using wordTrace_append hprefix tailTrace_2587448
  have hstable : (prefixWord ++ tailWord_2587448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2587448).length < 2 ^ (prefixWord ++ tailWord_2587448).sum := by decide
  have hdescent : baseEnd_2587448 < baseStart_2587448 := by decide
  rcases family_descends (prefixWord ++ tailWord_2587448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2587488 : List Nat := [2, 1, 1, 3, 3, 1, 1, 3, 1, 7]
def baseStart_2587488 : Nat := 118140960795 + 2587488 * 2 ^ 59
def prefixEnd_2587488 : Nat := 4983230072969 + 3 ^ 40 * 2587488 * 2
def baseEnd_2587488 : Nat := 442875010580292558333455

theorem tailTrace_2587488 : CollatzResearch.WordTrace tailWord_2587488 prefixEnd_2587488 442875010580292558333455 := by
  unfold tailWord_2587488
  simp only [CollatzResearch.WordTrace]
  refine ⟨47186720224990179306717559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62915626966653572408956745 47186720224990179306717559)
  ·
    refine ⟨70780080337485268960076339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47186720224990179306717559 70780080337485268960076339)
    ·
      refine ⟨106170120506227903440114509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70780080337485268960076339 106170120506227903440114509)
      ·
        refine ⟨39813795189835463790042941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106170120506227903440114509 39813795189835463790042941)
        ·
          refine ⟨14930173196188298921266103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39813795189835463790042941 14930173196188298921266103)
          ·
            refine ⟨22395259794282448381899155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14930173196188298921266103 22395259794282448381899155)
            ·
              refine ⟨33592889691423672572848733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22395259794282448381899155 33592889691423672572848733)
              ·
                refine ⟨12597333634283877214818275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33592889691423672572848733 12597333634283877214818275)
                ·
                  refine ⟨18896000451425815822227413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12597333634283877214818275 18896000451425815822227413)
                  ·
                    refine ⟨442875010580292558333455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18896000451425815822227413 442875010580292558333455)
                    ·
                      rfl

theorem cell23_2587488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 3, 1, 7].length) (baseStart_2587488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2587488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2587488 prefixEnd_2587488 := by exact prefixLift 2587488
  have htrace : WordTrace (prefixWord ++ tailWord_2587488) baseStart_2587488 baseEnd_2587488 := by
    simpa [prefixWord, tailWord_2587488, baseEnd_2587488] using wordTrace_append hprefix tailTrace_2587488
  have hstable : (prefixWord ++ tailWord_2587488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2587488).length < 2 ^ (prefixWord ++ tailWord_2587488).sum := by decide
  have hdescent : baseEnd_2587488 < baseStart_2587488 := by decide
  rcases family_descends (prefixWord ++ tailWord_2587488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2587492 : List Nat := [2, 3, 1, 1, 4, 1, 3, 3, 5]
def baseStart_2587492 : Nat := 118140960795 + 2587492 * 2 ^ 59
def prefixEnd_2587492 : Nat := 4983230072969 + 3 ^ 40 * 2587492 * 2
def baseEnd_2587492 : Nat := 147625231740388406594483

theorem tailTrace_2587492 : CollatzResearch.WordTrace tailWord_2587492 prefixEnd_2587492 147625231740388406594483 := by
  unfold tailWord_2587492
  simp only [CollatzResearch.WordTrace]
  refine ⟨47186793170982933648290365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62915724227977244864387153 47186793170982933648290365)
  ·
    refine ⟨17695047439118600118108887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47186793170982933648290365 17695047439118600118108887)
    ·
      refine ⟨26542571158677900177163331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17695047439118600118108887 26542571158677900177163331)
      ·
        refine ⟨39813856738016850265744997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26542571158677900177163331 39813856738016850265744997)
        ·
          refine ⟨7465098138378159424827187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39813856738016850265744997 7465098138378159424827187)
          ·
            refine ⟨11197647207567239137240781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7465098138378159424827187 11197647207567239137240781)
            ·
              refine ⟨4199117702837714676465293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11197647207567239137240781 4199117702837714676465293)
              ·
                refine ⟨1574669138564143003674485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4199117702837714676465293 1574669138564143003674485)
                ·
                  refine ⟨147625231740388406594483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1574669138564143003674485 147625231740388406594483)
                  ·
                    rfl

theorem cell23_2587492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 3, 5].length) (baseStart_2587492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2587492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2587492 prefixEnd_2587492 := by exact prefixLift 2587492
  have htrace : WordTrace (prefixWord ++ tailWord_2587492) baseStart_2587492 baseEnd_2587492 := by
    simpa [prefixWord, tailWord_2587492, baseEnd_2587492] using wordTrace_append hprefix tailTrace_2587492
  have hstable : (prefixWord ++ tailWord_2587492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2587492).length < 2 ^ (prefixWord ++ tailWord_2587492).sum := by decide
  have hdescent : baseEnd_2587492 < baseStart_2587492 := by decide
  rcases family_descends (prefixWord ++ tailWord_2587492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2587505 : List Nat := [1, 2, 2, 2, 1, 5, 1, 2, 2, 5]
def baseStart_2587505 : Nat := 118140960795 + 2587505 * 2 ^ 59
def prefixEnd_2587505 : Nat := 4983230072969 + 3 ^ 40 * 2587505 * 2
def baseEnd_2587505 : Nat := 442877920304001369495929

theorem tailTrace_2587505 : CollatzResearch.WordTrace tailWord_2587505 prefixEnd_2587505 442877920304001369495929 := by
  unfold tailWord_2587505
  simp only [CollatzResearch.WordTrace]
  refine ⟨94374060490918770516803969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62916040327279180344535979 94374060490918770516803969)
  ·
    refine ⟨70780545368189077887602977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94374060490918770516803969 70780545368189077887602977)
    ·
      refine ⟨53085409026141808415702233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70780545368189077887602977 53085409026141808415702233)
      ·
        refine ⟨39814056769606356311776675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53085409026141808415702233 39814056769606356311776675)
        ·
          refine ⟨59721085154409534467665013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39814056769606356311776675 59721085154409534467665013)
          ·
            refine ⟨5598851733225893856343595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 59721085154409534467665013 5598851733225893856343595)
            ·
              refine ⟨8398277599838840784515393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5598851733225893856343595 8398277599838840784515393)
              ·
                refine ⟨6298708199879130588386545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8398277599838840784515393 6298708199879130588386545)
                ·
                  refine ⟨4724031149909347941289909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6298708199879130588386545 4724031149909347941289909)
                  ·
                    refine ⟨442877920304001369495929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4724031149909347941289909 442877920304001369495929)
                    ·
                      rfl

theorem cell23_2587505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 2, 2, 5].length) (baseStart_2587505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2587505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2587505 prefixEnd_2587505 := by exact prefixLift 2587505
  have htrace : WordTrace (prefixWord ++ tailWord_2587505) baseStart_2587505 baseEnd_2587505 := by
    simpa [prefixWord, tailWord_2587505, baseEnd_2587505] using wordTrace_append hprefix tailTrace_2587505
  have hstable : (prefixWord ++ tailWord_2587505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2587505).length < 2 ^ (prefixWord ++ tailWord_2587505).sum := by decide
  have hdescent : baseEnd_2587505 < baseStart_2587505 := by decide
  rcases family_descends (prefixWord ++ tailWord_2587505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2587509 : List Nat := [1, 3, 4, 1, 1, 3, 3, 2, 5]
def baseStart_2587509 : Nat := 118140960795 + 2587509 * 2 ^ 59
def prefixEnd_2587509 : Nat := 4983230072969 + 3 ^ 40 * 2587509 * 2
def baseEnd_2587509 : Nat := 147626201648291343648641

theorem tailTrace_2587509 : CollatzResearch.WordTrace tailWord_2587509 prefixEnd_2587509 147626201648291343648641 := by
  unfold tailWord_2587509
  simp only [CollatzResearch.WordTrace]
  refine ⟨94374206382904279199949581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62916137588602852799966387 94374206382904279199949581)
  ·
    refine ⟨35390327393589104699981093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94374206382904279199949581 35390327393589104699981093)
    ·
      refine ⟨6635686386297957131246455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35390327393589104699981093 6635686386297957131246455)
      ·
        refine ⟨9953529579446935696869683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6635686386297957131246455 9953529579446935696869683)
        ·
          refine ⟨14930294369170403545304525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9953529579446935696869683 14930294369170403545304525)
          ·
            refine ⟨5598860388438901329489197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14930294369170403545304525 5598860388438901329489197)
            ·
              refine ⟨2099572645664587998558449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5598860388438901329489197 2099572645664587998558449)
              ·
                refine ⟨1574679484248440998918837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2099572645664587998558449 1574679484248440998918837)
                ·
                  refine ⟨147626201648291343648641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1574679484248440998918837 147626201648291343648641)
                  ·
                    rfl

theorem cell23_2587509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 3, 2, 5].length) (baseStart_2587509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2587509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2587509 prefixEnd_2587509 := by exact prefixLift 2587509
  have htrace : WordTrace (prefixWord ++ tailWord_2587509) baseStart_2587509 baseEnd_2587509 := by
    simpa [prefixWord, tailWord_2587509, baseEnd_2587509] using wordTrace_append hprefix tailTrace_2587509
  have hstable : (prefixWord ++ tailWord_2587509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2587509).length < 2 ^ (prefixWord ++ tailWord_2587509).sum := by decide
  have hdescent : baseEnd_2587509 < baseStart_2587509 := by decide
  rcases family_descends (prefixWord ++ tailWord_2587509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2587590 : List Nat := [6, 1, 3, 1, 1, 2, 1, 1, 2, 5]
def baseStart_2587590 : Nat := 118140960795 + 2587590 * 2 ^ 59
def prefixEnd_2587590 : Nat := 4983230072969 + 3 ^ 40 * 2587590 * 2
def baseEnd_2587590 : Nat := 442892468922545425308299

theorem tailTrace_2587590 : CollatzResearch.WordTrace tailWord_2587590 prefixEnd_2587590 442892468922545425308299 := by
  unfold tailWord_2587590
  simp only [CollatzResearch.WordTrace]
  refine ⟨2949286271737838438551507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 62918107130407220022432149 2949286271737838438551507)
  ·
    refine ⟨4423929407606757657827261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2949286271737838438551507 4423929407606757657827261)
    ·
      refine ⟨1658973527852534121685223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4423929407606757657827261 1658973527852534121685223)
      ·
        refine ⟨2488460291778801182527835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1658973527852534121685223 2488460291778801182527835)
        ·
          refine ⟨3732690437668201773791753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2488460291778801182527835 3732690437668201773791753)
          ·
            refine ⟨2799517828251151330343815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3732690437668201773791753 2799517828251151330343815)
            ·
              refine ⟨4199276742376726995515723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2799517828251151330343815 4199276742376726995515723)
              ·
                refine ⟨6298915113565090493273585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4199276742376726995515723 6298915113565090493273585)
                ·
                  refine ⟨4724186335173817869955189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6298915113565090493273585 4724186335173817869955189)
                  ·
                    refine ⟨442892468922545425308299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4724186335173817869955189 442892468922545425308299)
                    ·
                      rfl

theorem cell23_2587590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_2587590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2587590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2587590 prefixEnd_2587590 := by exact prefixLift 2587590
  have htrace : WordTrace (prefixWord ++ tailWord_2587590) baseStart_2587590 baseEnd_2587590 := by
    simpa [prefixWord, tailWord_2587590, baseEnd_2587590] using wordTrace_append hprefix tailTrace_2587590
  have hstable : (prefixWord ++ tailWord_2587590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2587590).length < 2 ^ (prefixWord ++ tailWord_2587590).sum := by decide
  have hdescent : baseEnd_2587590 < baseStart_2587590 := by decide
  rcases family_descends (prefixWord ++ tailWord_2587590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2587595 : List Nat := [1, 1, 1, 1, 3, 5, 2, 1, 3, 5]
def baseStart_2587595 : Nat := 118140960795 + 2587595 * 2 ^ 59
def prefixEnd_2587595 : Nat := 4983230072969 + 3 ^ 40 * 2587595 * 2
def baseEnd_2587595 : Nat := 442893324723636252120791

theorem tailTrace_2587595 : CollatzResearch.WordTrace tailWord_2587595 prefixEnd_2587595 442893324723636252120791 := by
  unfold tailWord_2587595
  simp only [CollatzResearch.WordTrace]
  refine ⟨94377343060592715887580239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62918228707061810591720159 94377343060592715887580239)
  ·
    refine ⟨141566014590889073831370359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94377343060592715887580239 141566014590889073831370359)
    ·
      refine ⟨212349021886333610747055539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141566014590889073831370359 212349021886333610747055539)
      ·
        refine ⟨318523532829500416120583309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212349021886333610747055539 318523532829500416120583309)
        ·
          refine ⟨119446324811062656045218741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 318523532829500416120583309 119446324811062656045218741)
          ·
            refine ⟨11198092951037124004239257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 119446324811062656045218741 11198092951037124004239257)
            ·
              refine ⟨8398569713277843003179443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11198092951037124004239257 8398569713277843003179443)
              ·
                refine ⟨12597854569916764504769165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8398569713277843003179443 12597854569916764504769165)
                ·
                  refine ⟨4724195463718786689288437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12597854569916764504769165 4724195463718786689288437)
                  ·
                    refine ⟨442893324723636252120791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4724195463718786689288437 442893324723636252120791)
                    ·
                      rfl

theorem cell23_2587595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 1, 3, 5].length) (baseStart_2587595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2587595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2587595 prefixEnd_2587595 := by exact prefixLift 2587595
  have htrace : WordTrace (prefixWord ++ tailWord_2587595) baseStart_2587595 baseEnd_2587595 := by
    simpa [prefixWord, tailWord_2587595, baseEnd_2587595] using wordTrace_append hprefix tailTrace_2587595
  have hstable : (prefixWord ++ tailWord_2587595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2587595).length < 2 ^ (prefixWord ++ tailWord_2587595).sum := by decide
  have hdescent : baseEnd_2587595 < baseStart_2587595 := by decide
  rcases family_descends (prefixWord ++ tailWord_2587595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2587626 : List Nat := [3, 1, 3, 1, 2, 2, 2, 4, 1, 1, 3]
def baseStart_2587626 : Nat := 118140960795 + 2587626 * 2 ^ 59
def prefixEnd_2587626 : Nat := 4983230072969 + 3 ^ 40 * 2587626 * 2
def baseEnd_2587626 : Nat := 1328695892071198135074731

theorem tailTrace_2587626 : CollatzResearch.WordTrace tailWord_2587626 prefixEnd_2587626 1328695892071198135074731 := by
  unfold tailWord_2587626
  simp only [CollatzResearch.WordTrace]
  refine ⟨23594618430870102045489683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62918982482320272121305821 23594618430870102045489683)
  ·
    refine ⟨35391927646305153068234525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23594618430870102045489683 35391927646305153068234525)
    ·
      refine ⟨13271972867364432400587947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35391927646305153068234525 13271972867364432400587947)
      ·
        refine ⟨19907959301046648600881921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13271972867364432400587947 19907959301046648600881921)
        ·
          refine ⟨14930969475784986450661441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19907959301046648600881921 14930969475784986450661441)
          ·
            refine ⟨11198227106838739837996081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14930969475784986450661441 11198227106838739837996081)
            ·
              refine ⟨8398670330129054878497061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11198227106838739837996081 8398670330129054878497061)
              ·
                refine ⟨1574750686899197789718199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8398670330129054878497061 1574750686899197789718199)
                ·
                  refine ⟨2362126030348796684577299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1574750686899197789718199 2362126030348796684577299)
                  ·
                    refine ⟨3543189045523195026865949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2362126030348796684577299 3543189045523195026865949)
                    ·
                      refine ⟨1328695892071198135074731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3543189045523195026865949 1328695892071198135074731)
                      ·
                        rfl

theorem cell23_2587626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 4, 1, 1, 3].length) (baseStart_2587626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2587626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2587626 prefixEnd_2587626 := by exact prefixLift 2587626
  have htrace : WordTrace (prefixWord ++ tailWord_2587626) baseStart_2587626 baseEnd_2587626 := by
    simpa [prefixWord, tailWord_2587626, baseEnd_2587626] using wordTrace_append hprefix tailTrace_2587626
  have hstable : (prefixWord ++ tailWord_2587626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2587626).length < 2 ^ (prefixWord ++ tailWord_2587626).sum := by decide
  have hdescent : baseEnd_2587626 < baseStart_2587626 := by decide
  rcases family_descends (prefixWord ++ tailWord_2587626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2587642 : List Nat := [3, 1, 1, 1, 1, 2, 1, 7, 2, 4]
def baseStart_2587642 : Nat := 118140960795 + 2587642 * 2 ^ 59
def prefixEnd_2587642 : Nat := 4983230072969 + 3 ^ 40 * 2587642 * 2
def baseEnd_2587642 : Nat := 442901369253890024158219

theorem tailTrace_2587642 : CollatzResearch.WordTrace tailWord_2587642 prefixEnd_2587642 442901369253890024158219 := by
  unfold tailWord_2587642
  simp only [CollatzResearch.WordTrace]
  refine ⟨23594764322855610728635295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62919371527614961943027453 23594764322855610728635295)
  ·
    refine ⟨35392146484283416092952943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23594764322855610728635295 35392146484283416092952943)
    ·
      refine ⟨53088219726425124139429415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35392146484283416092952943 53088219726425124139429415)
      ·
        refine ⟨79632329589637686209144123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53088219726425124139429415 79632329589637686209144123)
        ·
          refine ⟨119448494384456529313716185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79632329589637686209144123 119448494384456529313716185)
          ·
            refine ⟨89586370788342396985287139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119448494384456529313716185 89586370788342396985287139)
            ·
              refine ⟨134379556182513595477930709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89586370788342396985287139 134379556182513595477930709)
              ·
                refine ⟨3149520848027662394014001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 134379556182513595477930709 3149520848027662394014001)
                ·
                  refine ⟨2362140636020746795510501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3149520848027662394014001 2362140636020746795510501)
                  ·
                    refine ⟨442901369253890024158219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2362140636020746795510501 442901369253890024158219)
                    ·
                      rfl

theorem cell23_2587642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 7, 2, 4].length) (baseStart_2587642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2587642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2587642 prefixEnd_2587642 := by exact prefixLift 2587642
  have htrace : WordTrace (prefixWord ++ tailWord_2587642) baseStart_2587642 baseEnd_2587642 := by
    simpa [prefixWord, tailWord_2587642, baseEnd_2587642] using wordTrace_append hprefix tailTrace_2587642
  have hstable : (prefixWord ++ tailWord_2587642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2587642).length < 2 ^ (prefixWord ++ tailWord_2587642).sum := by decide
  have hdescent : baseEnd_2587642 < baseStart_2587642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2587642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2587646 : List Nat := [4, 2, 2, 2, 2, 1, 2, 2, 1, 5]
def baseStart_2587646 : Nat := 118140960795 + 2587646 * 2 ^ 59
def prefixEnd_2587646 : Nat := 4983230072969 + 3 ^ 40 * 2587646 * 2
def baseEnd_2587646 : Nat := 442902053894762685608213

theorem tailTrace_2587646 : CollatzResearch.WordTrace tailWord_2587646 prefixEnd_2587646 442902053894762685608213 := by
  unfold tailWord_2587646
  simp only [CollatzResearch.WordTrace]
  refine ⟨11797400397925993949710849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62919468788938634398457861 11797400397925993949710849)
  ·
    refine ⟨8848050298444495462283137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11797400397925993949710849 8848050298444495462283137)
    ·
      refine ⟨6636037723833371596712353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8848050298444495462283137 6636037723833371596712353)
      ·
        refine ⟨4977028292875028697534265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6636037723833371596712353 4977028292875028697534265)
        ·
          refine ⟨3732771219656271523150699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4977028292875028697534265 3732771219656271523150699)
          ·
            refine ⟨5599156829484407284726049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3732771219656271523150699 5599156829484407284726049)
            ·
              refine ⟨4199367622113305463544537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5599156829484407284726049 4199367622113305463544537)
              ·
                refine ⟨3149525716584979097658403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4199367622113305463544537 3149525716584979097658403)
                ·
                  refine ⟨4724288574877468646487605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3149525716584979097658403 4724288574877468646487605)
                  ·
                    refine ⟨442902053894762685608213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4724288574877468646487605 442902053894762685608213)
                    ·
                      rfl

theorem cell23_2587646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_2587646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2587646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2587646 prefixEnd_2587646 := by exact prefixLift 2587646
  have htrace : WordTrace (prefixWord ++ tailWord_2587646) baseStart_2587646 baseEnd_2587646 := by
    simpa [prefixWord, tailWord_2587646, baseEnd_2587646] using wordTrace_append hprefix tailTrace_2587646
  have hstable : (prefixWord ++ tailWord_2587646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2587646).length < 2 ^ (prefixWord ++ tailWord_2587646).sum := by decide
  have hdescent : baseEnd_2587646 < baseStart_2587646 := by decide
  rcases family_descends (prefixWord ++ tailWord_2587646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2587649 : List Nat := [1, 2, 4, 1, 2, 3, 2, 2, 1, 1, 4]
def baseStart_2587649 : Nat := 118140960795 + 2587649 * 2 ^ 59
def prefixEnd_2587649 : Nat := 4983230072969 + 3 ^ 40 * 2587649 * 2
def baseEnd_2587649 : Nat := 1328707702126251545087125

theorem tailTrace_2587649 : CollatzResearch.WordTrace tailWord_2587649 prefixEnd_2587649 1328707702126251545087125 := by
  unfold tailWord_2587649
  simp only [CollatzResearch.WordTrace]
  refine ⟨94379312602397083110046001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62919541734931388740030667 94379312602397083110046001)
  ·
    refine ⟨70784484451797812332534501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94379312602397083110046001 70784484451797812332534501)
    ·
      refine ⟨13272090834712089812350219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70784484451797812332534501 13272090834712089812350219)
      ·
        refine ⟨19908136252068134718525329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13272090834712089812350219 19908136252068134718525329)
        ·
          refine ⟨14931102189051101038893997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19908136252068134718525329 14931102189051101038893997)
          ·
            refine ⟨5599163320894162889585249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14931102189051101038893997 5599163320894162889585249)
            ·
              refine ⟨4199372490670622167188937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5599163320894162889585249 4199372490670622167188937)
              ·
                refine ⟨3149529368002966625391703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4199372490670622167188937 3149529368002966625391703)
                ·
                  refine ⟨4724294052004449938087555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3149529368002966625391703 4724294052004449938087555)
                  ·
                    refine ⟨7086441078006674907131333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4724294052004449938087555 7086441078006674907131333)
                    ·
                      refine ⟨1328707702126251545087125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7086441078006674907131333 1328707702126251545087125)
                      ·
                        rfl

theorem cell23_2587649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 2, 1, 1, 4].length) (baseStart_2587649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2587649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2587649 prefixEnd_2587649 := by exact prefixLift 2587649
  have htrace : WordTrace (prefixWord ++ tailWord_2587649) baseStart_2587649 baseEnd_2587649 := by
    simpa [prefixWord, tailWord_2587649, baseEnd_2587649] using wordTrace_append hprefix tailTrace_2587649
  have hstable : (prefixWord ++ tailWord_2587649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2587649).length < 2 ^ (prefixWord ++ tailWord_2587649).sum := by decide
  have hdescent : baseEnd_2587649 < baseStart_2587649 := by decide
  rcases family_descends (prefixWord ++ tailWord_2587649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2587655 : List Nat := [1, 1, 4, 3, 1, 1, 3, 9]
def baseStart_2587655 : Nat := 118140960795 + 2587655 * 2 ^ 59
def prefixEnd_2587655 : Nat := 4983230072969 + 3 ^ 40 * 2587655 * 2
def baseEnd_2587655 : Nat := 49211510481858463763411

theorem tailTrace_2587655 : CollatzResearch.WordTrace tailWord_2587655 prefixEnd_2587655 49211510481858463763411 := by
  unfold tailWord_2587655
  simp only [CollatzResearch.WordTrace]
  refine ⟨94379531440375346134764419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62919687626916897423176279 94379531440375346134764419)
  ·
    refine ⟨141569297160563019202146629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94379531440375346134764419 141569297160563019202146629)
    ·
      refine ⟨26544243217605566100402493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 141569297160563019202146629 26544243217605566100402493)
      ·
        refine ⟨9954091206602087287650935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26544243217605566100402493 9954091206602087287650935)
        ·
          refine ⟨14931136809903130931476403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9954091206602087287650935 14931136809903130931476403)
          ·
            refine ⟨22396705214854696397214605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14931136809903130931476403 22396705214854696397214605)
            ·
              refine ⟨8398764455570511148955477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22396705214854696397214605 8398764455570511148955477)
              ·
                refine ⟨49211510481858463763411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8398764455570511148955477 49211510481858463763411)
                ·
                  rfl

theorem cell23_2587655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 9].length) (baseStart_2587655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2587655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2587655 prefixEnd_2587655 := by exact prefixLift 2587655
  have htrace : WordTrace (prefixWord ++ tailWord_2587655) baseStart_2587655 baseEnd_2587655 := by
    simpa [prefixWord, tailWord_2587655, baseEnd_2587655] using wordTrace_append hprefix tailTrace_2587655
  have hstable : (prefixWord ++ tailWord_2587655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2587655).length < 2 ^ (prefixWord ++ tailWord_2587655).sum := by decide
  have hdescent : baseEnd_2587655 < baseStart_2587655 := by decide
  rcases family_descends (prefixWord ++ tailWord_2587655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2587669 : List Nat := [1, 3, 2, 1, 4, 1, 2, 3, 1, 2, 3]
def baseStart_2587669 : Nat := 118140960795 + 2587669 * 2 ^ 59
def prefixEnd_2587669 : Nat := 4983230072969 + 3 ^ 40 * 2587669 * 2
def baseEnd_2587669 : Nat := 1328717971739341466837033

theorem tailTrace_2587669 : CollatzResearch.WordTrace tailWord_2587669 prefixEnd_2587669 1328717971739341466837033 := by
  unfold tailWord_2587669
  simp only [CollatzResearch.WordTrace]
  refine ⟨94380042062324626525774061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62920028041549751017182707 94380042062324626525774061)
  ·
    refine ⟨35392515773371734947165273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94380042062324626525774061 35392515773371734947165273)
    ·
      refine ⟨26544386830028801210373955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35392515773371734947165273 26544386830028801210373955)
      ·
        refine ⟨39816580245043201815560933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26544386830028801210373955 39816580245043201815560933)
        ·
          refine ⟨7465608795945600340417675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39816580245043201815560933 7465608795945600340417675)
          ·
            refine ⟨11198413193918400510626513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7465608795945600340417675 11198413193918400510626513)
            ·
              refine ⟨8398809895438800382969885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11198413193918400510626513 8398809895438800382969885)
              ·
                refine ⟨3149553710789550143613707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8398809895438800382969885 3149553710789550143613707)
                ·
                  refine ⟨4724330566184325215420561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3149553710789550143613707 4724330566184325215420561)
                  ·
                    refine ⟨3543247924638243911565421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4724330566184325215420561 3543247924638243911565421)
                    ·
                      refine ⟨1328717971739341466837033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3543247924638243911565421 1328717971739341466837033)
                      ·
                        rfl

theorem cell23_2587669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 3, 1, 2, 3].length) (baseStart_2587669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2587669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2587669 prefixEnd_2587669 := by exact prefixLift 2587669
  have htrace : WordTrace (prefixWord ++ tailWord_2587669) baseStart_2587669 baseEnd_2587669 := by
    simpa [prefixWord, tailWord_2587669, baseEnd_2587669] using wordTrace_append hprefix tailTrace_2587669
  have hstable : (prefixWord ++ tailWord_2587669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2587669).length < 2 ^ (prefixWord ++ tailWord_2587669).sum := by decide
  have hdescent : baseEnd_2587669 < baseStart_2587669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2587669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2587685 : List Nat := [1, 3, 1, 2, 2, 2, 2, 1, 2, 7]
def baseStart_2587685 : Nat := 118140960795 + 2587685 * 2 ^ 59
def prefixEnd_2587685 : Nat := 4983230072969 + 3 ^ 40 * 2587685 * 2
def baseEnd_2587685 : Nat := 442908729143271134745653

theorem tailTrace_2587685 : CollatzResearch.WordTrace tailWord_2587685 prefixEnd_2587685 442908729143271134745653 := by
  unfold tailWord_2587685
  simp only [CollatzResearch.WordTrace]
  refine ⟨94380625630266661258356509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62920417086844440838904339 94380625630266661258356509)
  ·
    refine ⟨35392734611349997971883691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94380625630266661258356509 35392734611349997971883691)
    ·
      refine ⟨53089101917024996957825537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35392734611349997971883691 53089101917024996957825537)
      ·
        refine ⟨39816826437768747718369153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53089101917024996957825537 39816826437768747718369153)
        ·
          refine ⟨29862619828326560788776865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39816826437768747718369153 29862619828326560788776865)
          ·
            refine ⟨22396964871244920591582649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29862619828326560788776865 22396964871244920591582649)
            ·
              refine ⟨16797723653433690443686987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22396964871244920591582649 16797723653433690443686987)
              ·
                refine ⟨25196585480150535665530481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16797723653433690443686987 25196585480150535665530481)
                ·
                  refine ⟨18897439110112901749147861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25196585480150535665530481 18897439110112901749147861)
                  ·
                    refine ⟨442908729143271134745653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18897439110112901749147861 442908729143271134745653)
                    ·
                      rfl

theorem cell23_2587685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 2, 7].length) (baseStart_2587685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2587685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2587685 prefixEnd_2587685 := by exact prefixLift 2587685
  have htrace : WordTrace (prefixWord ++ tailWord_2587685) baseStart_2587685 baseEnd_2587685 := by
    simpa [prefixWord, tailWord_2587685, baseEnd_2587685] using wordTrace_append hprefix tailTrace_2587685
  have hstable : (prefixWord ++ tailWord_2587685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2587685).length < 2 ^ (prefixWord ++ tailWord_2587685).sum := by decide
  have hdescent : baseEnd_2587685 < baseStart_2587685 := by decide
  rcases family_descends (prefixWord ++ tailWord_2587685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2587735 : List Nat := [1, 1, 3, 2, 2, 1, 1, 1, 2, 3, 6]
def baseStart_2587735 : Nat := 118140960795 + 2587735 * 2 ^ 59
def prefixEnd_2587735 : Nat := 4983230072969 + 3 ^ 40 * 2587735 * 2
def baseEnd_2587735 : Nat := 1328751861462538208611729

theorem tailTrace_2587735 : CollatzResearch.WordTrace tailWord_2587735 prefixEnd_2587735 1328751861462538208611729 := by
  unfold tailWord_2587735
  simp only [CollatzResearch.WordTrace]
  refine ⟨94382449280085519797676659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62921632853390346531784439 94382449280085519797676659)
  ·
    refine ⟨141573673920128279696514989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94382449280085519797676659 141573673920128279696514989)
    ·
      refine ⟨53090127720048104886193121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141573673920128279696514989 53090127720048104886193121)
      ·
        refine ⟨39817595790036078664644841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53090127720048104886193121 39817595790036078664644841)
        ·
          refine ⟨29863196842527058998483631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39817595790036078664644841 29863196842527058998483631)
          ·
            refine ⟨44794795263790588497725447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29863196842527058998483631 44794795263790588497725447)
            ·
              refine ⟨67192192895685882746588171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44794795263790588497725447 67192192895685882746588171)
              ·
                refine ⟨100788289343528824119882257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67192192895685882746588171 100788289343528824119882257)
                ·
                  refine ⟨75591217007646618089911693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 100788289343528824119882257 75591217007646618089911693)
                  ·
                    refine ⟨28346706377867481783716885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 75591217007646618089911693 28346706377867481783716885)
                    ·
                      refine ⟨1328751861462538208611729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28346706377867481783716885 1328751861462538208611729)
                      ·
                        rfl

theorem cell23_2587735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 3, 6].length) (baseStart_2587735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2587735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2587735 prefixEnd_2587735 := by exact prefixLift 2587735
  have htrace : WordTrace (prefixWord ++ tailWord_2587735) baseStart_2587735 baseEnd_2587735 := by
    simpa [prefixWord, tailWord_2587735, baseEnd_2587735] using wordTrace_append hprefix tailTrace_2587735
  have hstable : (prefixWord ++ tailWord_2587735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2587735).length < 2 ^ (prefixWord ++ tailWord_2587735).sum := by decide
  have hdescent : baseEnd_2587735 < baseStart_2587735 := by decide
  rcases family_descends (prefixWord ++ tailWord_2587735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2587756 : List Nat := [2, 2, 1, 1, 3, 2, 1, 5, 2, 2, 2]
def baseStart_2587756 : Nat := 118140960795 + 2587756 * 2 ^ 59
def prefixEnd_2587756 : Nat := 4983230072969 + 3 ^ 40 * 2587756 * 2
def baseEnd_2587756 : Nat := 1328762644556282626449133

theorem tailTrace_2587756 : CollatzResearch.WordTrace tailWord_2587756 prefixEnd_2587756 1328762644556282626449133 := by
  unfold tailWord_2587756
  simp only [CollatzResearch.WordTrace]
  refine ⟨47191607606504720192095561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62922143475339626922794081 47191607606504720192095561)
  ·
    refine ⟨35393705704878540144071671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47191607606504720192095561 35393705704878540144071671)
    ·
      refine ⟨53090558557317810216107507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35393705704878540144071671 53090558557317810216107507)
      ·
        refine ⟨79635837835976715324161261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53090558557317810216107507 79635837835976715324161261)
        ·
          refine ⟨29863439188491268246560473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79635837835976715324161261 29863439188491268246560473)
          ·
            refine ⟨22397579391368451184920355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29863439188491268246560473 22397579391368451184920355)
            ·
              refine ⟨33596369087052676777380533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22397579391368451184920355 33596369087052676777380533)
              ·
                refine ⟨3149659601911188447879425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33596369087052676777380533 3149659601911188447879425)
                ·
                  refine ⟨2362244701433391335909569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3149659601911188447879425 2362244701433391335909569)
                  ·
                    refine ⟨1771683526075043501932177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2362244701433391335909569 1771683526075043501932177)
                    ·
                      refine ⟨1328762644556282626449133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1771683526075043501932177 1328762644556282626449133)
                      ·
                        rfl

theorem cell23_2587756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 2, 2].length) (baseStart_2587756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2587756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2587756 prefixEnd_2587756 := by exact prefixLift 2587756
  have htrace : WordTrace (prefixWord ++ tailWord_2587756) baseStart_2587756 baseEnd_2587756 := by
    simpa [prefixWord, tailWord_2587756, baseEnd_2587756] using wordTrace_append hprefix tailTrace_2587756
  have hstable : (prefixWord ++ tailWord_2587756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2587756).length < 2 ^ (prefixWord ++ tailWord_2587756).sum := by decide
  have hdescent : baseEnd_2587756 < baseStart_2587756 := by decide
  rcases family_descends (prefixWord ++ tailWord_2587756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2587762 : List Nat := [3, 2, 1, 2, 2, 1, 3, 2, 7]
def baseStart_2587762 : Nat := 118140960795 + 2587762 * 2 ^ 59
def prefixEnd_2587762 : Nat := 4983230072969 + 3 ^ 40 * 2587762 * 2
def baseEnd_2587762 : Nat := 147640636160023289219345

theorem tailTrace_2587762 : CollatzResearch.WordTrace tailWord_2587762 prefixEnd_2587762 147640636160023289219345 := by
  unfold tailWord_2587762
  simp only [CollatzResearch.WordTrace]
  refine ⟨23595858512746925852227385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62922289367325135605939693 23595858512746925852227385)
  ·
    refine ⟨17696893884560194389170539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23595858512746925852227385 17696893884560194389170539)
    ·
      refine ⟨26545340826840291583755809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17696893884560194389170539 26545340826840291583755809)
      ·
        refine ⟨19909005620130218687816857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26545340826840291583755809 19909005620130218687816857)
        ·
          refine ⟨14931754215097664015862643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19909005620130218687816857 14931754215097664015862643)
          ·
            refine ⟨22397631322646496023793965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14931754215097664015862643 22397631322646496023793965)
            ·
              refine ⟨8399111745992436008922737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22397631322646496023793965 8399111745992436008922737)
              ·
                refine ⟨6299333809494327006692053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8399111745992436008922737 6299333809494327006692053)
                ·
                  refine ⟨147640636160023289219345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6299333809494327006692053 147640636160023289219345)
                  ·
                    rfl

theorem cell23_2587762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 2, 7].length) (baseStart_2587762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2587762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2587762 prefixEnd_2587762 := by exact prefixLift 2587762
  have htrace : WordTrace (prefixWord ++ tailWord_2587762) baseStart_2587762 baseEnd_2587762 := by
    simpa [prefixWord, tailWord_2587762, baseEnd_2587762] using wordTrace_append hprefix tailTrace_2587762
  have hstable : (prefixWord ++ tailWord_2587762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2587762).length < 2 ^ (prefixWord ++ tailWord_2587762).sum := by decide
  have hdescent : baseEnd_2587762 < baseStart_2587762 := by decide
  rcases family_descends (prefixWord ++ tailWord_2587762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2587772 : List Nat := [2, 2, 2, 1, 1, 3, 1, 2, 1, 5, 3]
def baseStart_2587772 : Nat := 118140960795 + 2587772 * 2 ^ 59
def prefixEnd_2587772 : Nat := 4983230072969 + 3 ^ 40 * 2587772 * 2
def baseEnd_2587772 : Nat := 1328770860246754563849059

theorem tailTrace_2587772 : CollatzResearch.WordTrace tailWord_2587772 prefixEnd_2587772 1328770860246754563849059 := by
  unfold tailWord_2587772
  simp only [CollatzResearch.WordTrace]
  refine ⟨47191899390475737558386785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62922532520634316744515713 47191899390475737558386785)
  ·
    refine ⟨35393924542856803168790089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47191899390475737558386785 35393924542856803168790089)
    ·
      refine ⟨26545443407142602376592567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35393924542856803168790089 26545443407142602376592567)
      ·
        refine ⟨39818165110713903564888851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26545443407142602376592567 39818165110713903564888851)
        ·
          refine ⟨59727247666070855347333277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39818165110713903564888851 59727247666070855347333277)
          ·
            refine ⟨22397717874776570755249979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59727247666070855347333277 22397717874776570755249979)
            ·
              refine ⟨33596576812164856132874969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22397717874776570755249979 33596576812164856132874969)
              ·
                refine ⟨25197432609123642099656227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33596576812164856132874969 25197432609123642099656227)
                ·
                  refine ⟨37796148913685463149484341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25197432609123642099656227 37796148913685463149484341)
                  ·
                    refine ⟨3543388960658012170264157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37796148913685463149484341 3543388960658012170264157)
                    ·
                      refine ⟨1328770860246754563849059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3543388960658012170264157 1328770860246754563849059)
                      ·
                        rfl

theorem cell23_2587772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 1, 5, 3].length) (baseStart_2587772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2587772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2587772 prefixEnd_2587772 := by exact prefixLift 2587772
  have htrace : WordTrace (prefixWord ++ tailWord_2587772) baseStart_2587772 baseEnd_2587772 := by
    simpa [prefixWord, tailWord_2587772, baseEnd_2587772] using wordTrace_append hprefix tailTrace_2587772
  have hstable : (prefixWord ++ tailWord_2587772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2587772).length < 2 ^ (prefixWord ++ tailWord_2587772).sum := by decide
  have hdescent : baseEnd_2587772 < baseStart_2587772 := by decide
  rcases family_descends (prefixWord ++ tailWord_2587772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2587779 : List Nat := [1, 1, 1, 3, 3, 2, 4, 3, 5]
def baseStart_2587779 : Nat := 118140960795 + 2587779 * 2 ^ 59
def prefixEnd_2587779 : Nat := 4983230072969 + 3 ^ 40 * 2587779 * 2
def baseEnd_2587779 : Nat := 147641606067926226273503

theorem tailTrace_2587779 : CollatzResearch.WordTrace tailWord_2587779 prefixEnd_2587779 147641606067926226273503 := by
  unfold tailWord_2587779
  simp only [CollatzResearch.WordTrace]
  refine ⟨94384054091926115312278391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62922702727950743541518927 94384054091926115312278391)
  ·
    refine ⟨141576081137889172968417587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94384054091926115312278391 141576081137889172968417587)
    ·
      refine ⟨212364121706833759452626381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141576081137889172968417587 212364121706833759452626381)
      ·
        refine ⟨79636545640062659794734893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 212364121706833759452626381 79636545640062659794734893)
        ·
          refine ⟨29863704615023497423025585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79636545640062659794734893 29863704615023497423025585)
          ·
            refine ⟨22397778461267623067269189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29863704615023497423025585 22397778461267623067269189)
            ·
              refine ⟨4199583461487679325112973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22397778461267623067269189 4199583461487679325112973)
              ·
                refine ⟨1574843798057879746917365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4199583461487679325112973 1574843798057879746917365)
                ·
                  refine ⟨147641606067926226273503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1574843798057879746917365 147641606067926226273503)
                  ·
                    rfl

theorem cell23_2587779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 3, 5].length) (baseStart_2587779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2587779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2587779 prefixEnd_2587779 := by exact prefixLift 2587779
  have htrace : WordTrace (prefixWord ++ tailWord_2587779) baseStart_2587779 baseEnd_2587779 := by
    simpa [prefixWord, tailWord_2587779, baseEnd_2587779] using wordTrace_append hprefix tailTrace_2587779
  have hstable : (prefixWord ++ tailWord_2587779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2587779).length < 2 ^ (prefixWord ++ tailWord_2587779).sum := by decide
  have hdescent : baseEnd_2587779 < baseStart_2587779 := by decide
  rcases family_descends (prefixWord ++ tailWord_2587779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2587790 : List Nat := [4, 1, 1, 3, 2, 3, 1, 2, 2, 2, 2]
def baseStart_2587790 : Nat := 118140960795 + 2587790 * 2 ^ 59
def prefixEnd_2587790 : Nat := 4983230072969 + 3 ^ 40 * 2587790 * 2
def baseEnd_2587790 : Nat := 1328780102898535493423977

theorem tailTrace_2587790 : CollatzResearch.WordTrace tailWord_2587790 prefixEnd_2587790 1328780102898535493423977 := by
  unfold tailWord_2587790
  simp only [CollatzResearch.WordTrace]
  refine ⟨11798056911860783023866103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62922970196590842793952549 11798056911860783023866103)
  ·
    refine ⟨17697085367791174535799155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11798056911860783023866103 17697085367791174535799155)
    ·
      refine ⟨26545628051686761803698733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17697085367791174535799155 26545628051686761803698733)
      ·
        refine ⟨9954610519382535676387025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26545628051686761803698733 9954610519382535676387025)
        ·
          refine ⟨7465957889536901757290269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9954610519382535676387025 7465957889536901757290269)
          ·
            refine ⟨2799734208576338158983851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7465957889536901757290269 2799734208576338158983851)
            ·
              refine ⟨4199601312864507238475777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2799734208576338158983851 4199601312864507238475777)
              ·
                refine ⟨3149700984648380428856833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4199601312864507238475777 3149700984648380428856833)
                ·
                  refine ⟨2362275738486285321642625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3149700984648380428856833 2362275738486285321642625)
                  ·
                    refine ⟨1771706803864713991231969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2362275738486285321642625 1771706803864713991231969)
                    ·
                      refine ⟨1328780102898535493423977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1771706803864713991231969 1328780102898535493423977)
                      ·
                        rfl

theorem cell23_2587790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 2, 2, 2, 2].length) (baseStart_2587790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2587790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2587790 prefixEnd_2587790 := by exact prefixLift 2587790
  have htrace : WordTrace (prefixWord ++ tailWord_2587790) baseStart_2587790 baseEnd_2587790 := by
    simpa [prefixWord, tailWord_2587790, baseEnd_2587790] using wordTrace_append hprefix tailTrace_2587790
  have hstable : (prefixWord ++ tailWord_2587790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2587790).length < 2 ^ (prefixWord ++ tailWord_2587790).sum := by decide
  have hdescent : baseEnd_2587790 < baseStart_2587790 := by decide
  rcases family_descends (prefixWord ++ tailWord_2587790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2587806 : List Nat := [4, 3, 1, 1, 2, 1, 2, 1, 2, 3, 3]
def baseStart_2587806 : Nat := 118140960795 + 2587806 * 2 ^ 59
def prefixEnd_2587806 : Nat := 4983230072969 + 3 ^ 40 * 2587806 * 2
def baseEnd_2587806 : Nat := 1328788318589007430823903

theorem tailTrace_2587806 : CollatzResearch.WordTrace tailWord_2587806 prefixEnd_2587806 1328788318589007430823903 := by
  unfold tailWord_2587806
  simp only [CollatzResearch.WordTrace]
  refine ⟨11798129857853537365438909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62923359241885532615674181 11798129857853537365438909)
  ·
    refine ⟨4424298696695076512039591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11798129857853537365438909 4424298696695076512039591)
    ·
      refine ⟨6636448045042614768059387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4424298696695076512039591 6636448045042614768059387)
      ·
        refine ⟨9954672067563922152089081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6636448045042614768059387 9954672067563922152089081)
        ·
          refine ⟨7466004050672941614066811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9954672067563922152089081 7466004050672941614066811)
          ·
            refine ⟨11199006076009412421100217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7466004050672941614066811 11199006076009412421100217)
            ·
              refine ⟨8399254557007059315825163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11199006076009412421100217 8399254557007059315825163)
              ·
                refine ⟨12598881835510588973737745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8399254557007059315825163 12598881835510588973737745)
                ·
                  refine ⟨9449161376632941730303309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12598881835510588973737745 9449161376632941730303309)
                  ·
                    refine ⟨3543435516237353148863741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9449161376632941730303309 3543435516237353148863741)
                    ·
                      refine ⟨1328788318589007430823903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3543435516237353148863741 1328788318589007430823903)
                      ·
                        rfl

theorem cell23_2587806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_2587806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2587806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2587806 prefixEnd_2587806 := by exact prefixLift 2587806
  have htrace : WordTrace (prefixWord ++ tailWord_2587806) baseStart_2587806 baseEnd_2587806 := by
    simpa [prefixWord, tailWord_2587806, baseEnd_2587806] using wordTrace_append hprefix tailTrace_2587806
  have hstable : (prefixWord ++ tailWord_2587806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2587806).length < 2 ^ (prefixWord ++ tailWord_2587806).sum := by decide
  have hdescent : baseEnd_2587806 < baseStart_2587806 := by decide
  rcases family_descends (prefixWord ++ tailWord_2587806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2587853 : List Nat := [1, 6, 2, 2, 1, 1, 1, 1, 1, 2, 5]
def baseStart_2587853 : Nat := 118140960795 + 2587853 * 2 ^ 59
def prefixEnd_2587853 : Nat := 4983230072969 + 3 ^ 40 * 2587853 * 2
def baseEnd_2587853 : Nat := 1328812452179768746936187

theorem tailTrace_2587853 : CollatzResearch.WordTrace tailWord_2587853 prefixEnd_2587853 1328812452179768746936187 := by
  unfold tailWord_2587853
  simp only [CollatzResearch.WordTrace]
  refine ⟨94386753093658025950472213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62924502062438683966981475 94386753093658025950472213)
  ·
    refine ⟨4424379051265219966428385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 94386753093658025950472213 4424379051265219966428385)
    ·
      refine ⟨3318284288448914974821289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4424379051265219966428385 3318284288448914974821289)
      ·
        refine ⟨2488713216336686231115967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3318284288448914974821289 2488713216336686231115967)
        ·
          refine ⟨3733069824505029346673951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2488713216336686231115967 3733069824505029346673951)
          ·
            refine ⟨5599604736757544020010927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3733069824505029346673951 5599604736757544020010927)
            ·
              refine ⟨8399407105136316030016391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5599604736757544020010927 8399407105136316030016391)
              ·
                refine ⟨12599110657704474045024587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8399407105136316030016391 12599110657704474045024587)
                ·
                  refine ⟨18898665986556711067536881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12599110657704474045024587 18898665986556711067536881)
                  ·
                    refine ⟨14173999489917533300652661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18898665986556711067536881 14173999489917533300652661)
                    ·
                      refine ⟨1328812452179768746936187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14173999489917533300652661 1328812452179768746936187)
                      ·
                        rfl

theorem cell23_2587853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_2587853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2587853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2587853 prefixEnd_2587853 := by exact prefixLift 2587853
  have htrace : WordTrace (prefixWord ++ tailWord_2587853) baseStart_2587853 baseEnd_2587853 := by
    simpa [prefixWord, tailWord_2587853, baseEnd_2587853] using wordTrace_append hprefix tailTrace_2587853
  have hstable : (prefixWord ++ tailWord_2587853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2587853).length < 2 ^ (prefixWord ++ tailWord_2587853).sum := by decide
  have hdescent : baseEnd_2587853 < baseStart_2587853 := by decide
  rcases family_descends (prefixWord ++ tailWord_2587853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2587913 : List Nat := [1, 2, 1, 1, 3, 3, 3, 4, 1, 1, 3]
def baseStart_2587913 : Nat := 118140960795 + 2587913 * 2 ^ 59
def prefixEnd_2587913 : Nat := 4983230072969 + 3 ^ 40 * 2587913 * 2
def baseEnd_2587913 : Nat := 1328843261019038512185911

theorem tailTrace_2587913 : CollatzResearch.WordTrace tailWord_2587913 prefixEnd_2587913 1328843261019038512185911 := by
  unfold tailWord_2587913
  simp only [CollatzResearch.WordTrace]
  refine ⟨94388941473440656197656393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62925960982293770798437595 94388941473440656197656393)
  ·
    refine ⟨70791706105080492148242295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94388941473440656197656393 70791706105080492148242295)
    ·
      refine ⟨106187559157620738222363443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70791706105080492148242295 106187559157620738222363443)
      ·
        refine ⟨159281338736431107333545165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106187559157620738222363443 159281338736431107333545165)
        ·
          refine ⟨59730502026161665250079437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 159281338736431107333545165 59730502026161665250079437)
          ·
            refine ⟨22398938259810624468779789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59730502026161665250079437 22398938259810624468779789)
            ·
              refine ⟨8399601847428984175792421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22398938259810624468779789 8399601847428984175792421)
              ·
                refine ⟨1574925346392934532961079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8399601847428984175792421 1574925346392934532961079)
                ·
                  refine ⟨2362388019589401799441619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1574925346392934532961079 2362388019589401799441619)
                  ·
                    refine ⟨3543582029384102699162429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2362388019589401799441619 3543582029384102699162429)
                    ·
                      refine ⟨1328843261019038512185911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3543582029384102699162429 1328843261019038512185911)
                      ·
                        rfl

theorem cell23_2587913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 4, 1, 1, 3].length) (baseStart_2587913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2587913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2587913 prefixEnd_2587913 := by exact prefixLift 2587913
  have htrace : WordTrace (prefixWord ++ tailWord_2587913) baseStart_2587913 baseEnd_2587913 := by
    simpa [prefixWord, tailWord_2587913, baseEnd_2587913] using wordTrace_append hprefix tailTrace_2587913
  have hstable : (prefixWord ++ tailWord_2587913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2587913).length < 2 ^ (prefixWord ++ tailWord_2587913).sum := by decide
  have hdescent : baseEnd_2587913 < baseStart_2587913 := by decide
  rcases family_descends (prefixWord ++ tailWord_2587913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2587919 : List Nat := [1, 1, 2, 1, 1, 1, 3, 1, 4, 6, 2]
def baseStart_2587919 : Nat := 118140960795 + 2587919 * 2 ^ 59
def prefixEnd_2587919 : Nat := 4983230072969 + 3 ^ 40 * 2587919 * 2
def baseEnd_2587919 : Nat := 1328846341902965488710883

theorem tailTrace_2587919 : CollatzResearch.WordTrace tailWord_2587919 prefixEnd_2587919 1328846341902965488710883 := by
  unfold tailWord_2587919
  simp only [CollatzResearch.WordTrace]
  refine ⟨94389160311418919222374811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62926106874279279481583207 94389160311418919222374811)
  ·
    refine ⟨141583740467128378833562217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94389160311418919222374811 141583740467128378833562217)
    ·
      refine ⟨106187805350346284125171663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141583740467128378833562217 106187805350346284125171663)
      ·
        refine ⟨159281708025519426187757495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106187805350346284125171663 159281708025519426187757495)
        ·
          refine ⟨238922562038279139281636243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159281708025519426187757495 238922562038279139281636243)
          ·
            refine ⟨358383843057418708922454365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 238922562038279139281636243 358383843057418708922454365)
            ·
              refine ⟨134393941146532015845920387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 358383843057418708922454365 134393941146532015845920387)
              ·
                refine ⟨201590911719798023768880581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 134393941146532015845920387 201590911719798023768880581)
                ·
                  refine ⟨37798295947462129456665109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 201590911719798023768880581 37798295947462129456665109)
                  ·
                    refine ⟨1771795122537287318281177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 37798295947462129456665109 1771795122537287318281177)
                    ·
                      refine ⟨1328846341902965488710883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1771795122537287318281177 1328846341902965488710883)
                      ·
                        rfl

theorem cell23_2587919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 6, 2].length) (baseStart_2587919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2587919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2587919 prefixEnd_2587919 := by exact prefixLift 2587919
  have htrace : WordTrace (prefixWord ++ tailWord_2587919) baseStart_2587919 baseEnd_2587919 := by
    simpa [prefixWord, tailWord_2587919, baseEnd_2587919] using wordTrace_append hprefix tailTrace_2587919
  have hstable : (prefixWord ++ tailWord_2587919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2587919).length < 2 ^ (prefixWord ++ tailWord_2587919).sum := by decide
  have hdescent : baseEnd_2587919 < baseStart_2587919 := by decide
  rcases family_descends (prefixWord ++ tailWord_2587919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2587946 : List Nat := [3, 1, 4, 2, 1, 1, 2, 2, 1, 6]
def baseStart_2587946 : Nat := 118140960795 + 2587946 * 2 ^ 59
def prefixEnd_2587946 : Nat := 4983230072969 + 3 ^ 40 * 2587946 * 2
def baseEnd_2587946 : Nat := 442953401960212294357753

theorem tailTrace_2587946 : CollatzResearch.WordTrace tailWord_2587946 prefixEnd_2587946 442953401960212294357753 := by
  unfold tailWord_2587946
  simp only [CollatzResearch.WordTrace]
  refine ⟨23597536270580275708401923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62926763388214068555738461 23597536270580275708401923)
  ·
    refine ⟨35396304405870413562602885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23597536270580275708401923 35396304405870413562602885)
    ·
      refine ⟨6636807076100702542988041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35396304405870413562602885 6636807076100702542988041)
      ·
        refine ⟨4977605307075526907241031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6636807076100702542988041 4977605307075526907241031)
        ·
          refine ⟨7466407960613290360861547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4977605307075526907241031 7466407960613290360861547)
          ·
            refine ⟨11199611940919935541292321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7466407960613290360861547 11199611940919935541292321)
            ·
              refine ⟨8399708955689951655969241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11199611940919935541292321 8399708955689951655969241)
              ·
                refine ⟨6299781716767463741976931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8399708955689951655969241 6299781716767463741976931)
                ·
                  refine ⟨9449672575151195612965397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6299781716767463741976931 9449672575151195612965397)
                  ·
                    refine ⟨442953401960212294357753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9449672575151195612965397 442953401960212294357753)
                    ·
                      rfl

theorem cell23_2587946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_2587946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2587946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2587946 prefixEnd_2587946 := by exact prefixLift 2587946
  have htrace : WordTrace (prefixWord ++ tailWord_2587946) baseStart_2587946 baseEnd_2587946 := by
    simpa [prefixWord, tailWord_2587946, baseEnd_2587946] using wordTrace_append hprefix tailTrace_2587946
  have hstable : (prefixWord ++ tailWord_2587946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2587946).length < 2 ^ (prefixWord ++ tailWord_2587946).sum := by decide
  have hdescent : baseEnd_2587946 < baseStart_2587946 := by decide
  rcases family_descends (prefixWord ++ tailWord_2587946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2587953 : List Nat := [1, 2, 2, 3, 3, 1, 4, 1, 1, 1, 4]
def baseStart_2587953 : Nat := 118140960795 + 2587953 * 2 ^ 59
def prefixEnd_2587953 : Nat := 4983230072969 + 3 ^ 40 * 2587953 * 2
def baseEnd_2587953 : Nat := 1328863800245218355685727

theorem tailTrace_2587953 : CollatzResearch.WordTrace tailWord_2587953 prefixEnd_2587953 1328863800245218355685727 := by
  unfold tailWord_2587953
  simp only [CollatzResearch.WordTrace]
  refine ⟨94390400393295743029112513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62926933595530495352741675 94390400393295743029112513)
  ·
    refine ⟨70792800294971807271834385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94390400393295743029112513 70792800294971807271834385)
    ·
      refine ⟨53094600221228855453875789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70792800294971807271834385 53094600221228855453875789)
      ·
        refine ⟨19910475082960820795203421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53094600221228855453875789 19910475082960820795203421)
        ·
          refine ⟨7466428156110307798201283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19910475082960820795203421 7466428156110307798201283)
          ·
            refine ⟨11199642234165461697301925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7466428156110307798201283 11199642234165461697301925)
            ·
              refine ⟨2099932918906024068244111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11199642234165461697301925 2099932918906024068244111)
              ·
                refine ⟨3149899378359036102366167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2099932918906024068244111 3149899378359036102366167)
                ·
                  refine ⟨4724849067538554153549251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3149899378359036102366167 4724849067538554153549251)
                  ·
                    refine ⟨7087273601307831230323877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4724849067538554153549251 7087273601307831230323877)
                    ·
                      refine ⟨1328863800245218355685727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7087273601307831230323877 1328863800245218355685727)
                      ·
                        rfl

theorem cell23_2587953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 4, 1, 1, 1, 4].length) (baseStart_2587953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2587953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2587953 prefixEnd_2587953 := by exact prefixLift 2587953
  have htrace : WordTrace (prefixWord ++ tailWord_2587953) baseStart_2587953 baseEnd_2587953 := by
    simpa [prefixWord, tailWord_2587953, baseEnd_2587953] using wordTrace_append hprefix tailTrace_2587953
  have hstable : (prefixWord ++ tailWord_2587953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2587953).length < 2 ^ (prefixWord ++ tailWord_2587953).sum := by decide
  have hdescent : baseEnd_2587953 < baseStart_2587953 := by decide
  rcases family_descends (prefixWord ++ tailWord_2587953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2587956 : List Nat := [2, 5, 1, 1, 1, 1, 2, 3, 1, 1, 5]
def baseStart_2587956 : Nat := 118140960795 + 2587956 * 2 ^ 59
def prefixEnd_2587956 : Nat := 4983230072969 + 3 ^ 40 * 2587956 * 2
def baseEnd_2587956 : Nat := 1328865340687181843948213

theorem tailTrace_2587956 : CollatzResearch.WordTrace tailWord_2587956 prefixEnd_2587956 1328865340687181843948213 := by
  unfold tailWord_2587956
  simp only [CollatzResearch.WordTrace]
  refine ⟨47195254906142437270735861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62927006541523249694314481 47195254906142437270735861)
  ·
    refine ⟨4424555147450853494131487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 47195254906142437270735861 4424555147450853494131487)
    ·
      refine ⟨6636832721176280241197231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4424555147450853494131487 6636832721176280241197231)
      ·
        refine ⟨9955249081764420361795847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6636832721176280241197231 9955249081764420361795847)
        ·
          refine ⟨14932873622646630542693771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9955249081764420361795847 14932873622646630542693771)
          ·
            refine ⟨22399310433969945814040657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14932873622646630542693771 22399310433969945814040657)
            ·
              refine ⟨16799482825477459360530493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22399310433969945814040657 16799482825477459360530493)
              ·
                refine ⟨6299806059554047260198935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16799482825477459360530493 6299806059554047260198935)
                ·
                  refine ⟨9449709089331070890298403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6299806059554047260198935 9449709089331070890298403)
                  ·
                    refine ⟨14174563633996606335447605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9449709089331070890298403 14174563633996606335447605)
                    ·
                      refine ⟨1328865340687181843948213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14174563633996606335447605 1328865340687181843948213)
                      ·
                        rfl

theorem cell23_2587956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_2587956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2587956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2587956 prefixEnd_2587956 := by exact prefixLift 2587956
  have htrace : WordTrace (prefixWord ++ tailWord_2587956) baseStart_2587956 baseEnd_2587956 := by
    simpa [prefixWord, tailWord_2587956, baseEnd_2587956] using wordTrace_append hprefix tailTrace_2587956
  have hstable : (prefixWord ++ tailWord_2587956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2587956).length < 2 ^ (prefixWord ++ tailWord_2587956).sum := by decide
  have hdescent : baseEnd_2587956 < baseStart_2587956 := by decide
  rcases family_descends (prefixWord ++ tailWord_2587956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2588026 : List Nat := [3, 1, 1, 1, 1, 1, 2, 4, 3, 4, 2]
def baseStart_2588026 : Nat := 118140960795 + 2588026 * 2 ^ 59
def prefixEnd_2588026 : Nat := 4983230072969 + 3 ^ 40 * 2588026 * 2
def baseEnd_2588026 : Nat := 1328901284332996570072891

theorem tailTrace_2588026 : CollatzResearch.WordTrace tailWord_2588026 prefixEnd_2588026 1328901284332996570072891 := by
  unfold tailWord_2588026
  simp only [CollatzResearch.WordTrace]
  refine ⟨23598265730507819124129983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62928708614687517664346621 23598265730507819124129983)
  ·
    refine ⟨35397398595761728686194975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23598265730507819124129983 35397398595761728686194975)
    ·
      refine ⟨53096097893642593029292463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35397398595761728686194975 53096097893642593029292463)
      ·
        refine ⟨79644146840463889543938695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53096097893642593029292463 79644146840463889543938695)
        ·
          refine ⟨119466220260695834315908043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79644146840463889543938695 119466220260695834315908043)
          ·
            refine ⟨179199330391043751473862065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119466220260695834315908043 179199330391043751473862065)
            ·
              refine ⟨134399497793282813605396549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 179199330391043751473862065 134399497793282813605396549)
              ·
                refine ⟨25199905836240527551011853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 134399497793282813605396549 25199905836240527551011853)
                ·
                  refine ⟨9449964688590197831629445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25199905836240527551011853 9449964688590197831629445)
                  ·
                    refine ⟨1771868379110662093430521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9449964688590197831629445 1771868379110662093430521)
                    ·
                      refine ⟨1328901284332996570072891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1771868379110662093430521 1328901284332996570072891)
                      ·
                        rfl

theorem cell23_2588026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 3, 4, 2].length) (baseStart_2588026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2588026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2588026 prefixEnd_2588026 := by exact prefixLift 2588026
  have htrace : WordTrace (prefixWord ++ tailWord_2588026) baseStart_2588026 baseEnd_2588026 := by
    simpa [prefixWord, tailWord_2588026, baseEnd_2588026] using wordTrace_append hprefix tailTrace_2588026
  have hstable : (prefixWord ++ tailWord_2588026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2588026).length < 2 ^ (prefixWord ++ tailWord_2588026).sum := by decide
  have hdescent : baseEnd_2588026 < baseStart_2588026 := by decide
  rcases family_descends (prefixWord ++ tailWord_2588026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2588029 : List Nat := [1, 4, 1, 1, 2, 2, 1, 2, 1, 3, 5]
def baseStart_2588029 : Nat := 118140960795 + 2588029 * 2 ^ 59
def prefixEnd_2588029 : Nat := 4983230072969 + 3 ^ 40 * 2588029 * 2
def baseEnd_2588029 : Nat := 1328902824774960058335377

theorem tailTrace_2588029 : CollatzResearch.WordTrace tailWord_2588029 prefixEnd_2588029 1328902824774960058335377 := by
  unfold tailWord_2588029
  simp only [CollatzResearch.WordTrace]
  refine ⟨94393172341020408008879141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62928781560680272005919427 94393172341020408008879141)
  ·
    refine ⟨17698719813941326501664839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94393172341020408008879141 17698719813941326501664839)
    ·
      refine ⟨26548079720911989752497259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17698719813941326501664839 26548079720911989752497259)
      ·
        refine ⟨39822119581367984628745889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26548079720911989752497259 39822119581367984628745889)
        ·
          refine ⟨29866589686025988471559417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39822119581367984628745889 29866589686025988471559417)
          ·
            refine ⟨22399942264519491353669563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29866589686025988471559417 22399942264519491353669563)
            ·
              refine ⟨33599913396779237030504345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22399942264519491353669563 33599913396779237030504345)
              ·
                refine ⟨25199935047584427772878259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33599913396779237030504345 25199935047584427772878259)
                ·
                  refine ⟨37799902571376641659317389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25199935047584427772878259 37799902571376641659317389)
                  ·
                    refine ⟨14174963464266240622244021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37799902571376641659317389 14174963464266240622244021)
                    ·
                      refine ⟨1328902824774960058335377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14174963464266240622244021 1328902824774960058335377)
                      ·
                        rfl

theorem cell23_2588029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 3, 5].length) (baseStart_2588029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2588029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2588029 prefixEnd_2588029 := by exact prefixLift 2588029
  have htrace : WordTrace (prefixWord ++ tailWord_2588029) baseStart_2588029 baseEnd_2588029 := by
    simpa [prefixWord, tailWord_2588029, baseEnd_2588029] using wordTrace_append hprefix tailTrace_2588029
  have hstable : (prefixWord ++ tailWord_2588029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2588029).length < 2 ^ (prefixWord ++ tailWord_2588029).sum := by decide
  have hdescent : baseEnd_2588029 < baseStart_2588029 := by decide
  rcases family_descends (prefixWord ++ tailWord_2588029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2588077 : List Nat := [1, 5, 2, 2, 1, 1, 1, 4, 2, 2, 2]
def baseStart_2588077 : Nat := 118140960795 + 2588077 * 2 ^ 59
def prefixEnd_2588077 : Nat := 4983230072969 + 3 ^ 40 * 2588077 * 2
def baseEnd_2588077 : Nat := 1328927471846375870535157

theorem tailTrace_2588077 : CollatzResearch.WordTrace tailWord_2588077 prefixEnd_2588077 1328927471846375870535157 := by
  unfold tailWord_2588077
  simp only [CollatzResearch.WordTrace]
  refine ⟨94394923044846512206626485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62929948696564341471084323 94394923044846512206626485)
  ·
    refine ⟨8849524035454360519371233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 94394923044846512206626485 8849524035454360519371233)
    ·
      refine ⟨6637143026590770389528425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8849524035454360519371233 6637143026590770389528425)
      ·
        refine ⟨4977857269943077792146319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6637143026590770389528425 4977857269943077792146319)
        ·
          refine ⟨7466785904914616688219479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4977857269943077792146319 7466785904914616688219479)
          ·
            refine ⟨11200178857371925032329219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7466785904914616688219479 11200178857371925032329219)
            ·
              refine ⟨16800268286057887548493829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11200178857371925032329219 16800268286057887548493829)
              ·
                refine ⟨3150050303635853915342593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16800268286057887548493829 3150050303635853915342593)
                ·
                  refine ⟨2362537727726890436506945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3150050303635853915342593 2362537727726890436506945)
                  ·
                    refine ⟨1771903295795167827380209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2362537727726890436506945 1771903295795167827380209)
                    ·
                      refine ⟨1328927471846375870535157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1771903295795167827380209 1328927471846375870535157)
                      ·
                        rfl

theorem cell23_2588077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_2588077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2588077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2588077 prefixEnd_2588077 := by exact prefixLift 2588077
  have htrace : WordTrace (prefixWord ++ tailWord_2588077) baseStart_2588077 baseEnd_2588077 := by
    simpa [prefixWord, tailWord_2588077, baseEnd_2588077] using wordTrace_append hprefix tailTrace_2588077
  have hstable : (prefixWord ++ tailWord_2588077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2588077).length < 2 ^ (prefixWord ++ tailWord_2588077).sum := by decide
  have hdescent : baseEnd_2588077 < baseStart_2588077 := by decide
  rcases family_descends (prefixWord ++ tailWord_2588077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2588150 : List Nat := [5, 1, 1, 1, 2, 2, 2, 1, 2, 4, 2]
def baseStart_2588150 : Nat := 118140960795 + 2588150 * 2 ^ 59
def prefixEnd_2588150 : Nat := 4983230072969 + 3 ^ 40 * 2588150 * 2
def baseEnd_2588150 : Nat := 1328964955934154084922321

theorem tailTrace_2588150 : CollatzResearch.WordTrace tailWord_2588150 prefixEnd_2588150 1328964955934154084922321 := by
  unfold tailWord_2588150
  simp only [CollatzResearch.WordTrace]
  refine ⟨5899849098348877854627119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 62931723715721363782689269 5899849098348877854627119)
  ·
    refine ⟨8849773647523316781940679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5899849098348877854627119 8849773647523316781940679)
    ·
      refine ⟨13274660471284975172911019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8849773647523316781940679 13274660471284975172911019)
      ·
        refine ⟨19911990706927462759366529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13274660471284975172911019 19911990706927462759366529)
        ·
          refine ⟨14933993030195597069524897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19911990706927462759366529 14933993030195597069524897)
          ·
            refine ⟨11200494772646697802143673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14933993030195597069524897 11200494772646697802143673)
            ·
              refine ⟨8400371079485023351607755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11200494772646697802143673 8400371079485023351607755)
              ·
                refine ⟨12600556619227535027411633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8400371079485023351607755 12600556619227535027411633)
                ·
                  refine ⟨9450417464420651270558725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12600556619227535027411633 9450417464420651270558725)
                  ·
                    refine ⟨1771953274578872113229761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9450417464420651270558725 1771953274578872113229761)
                    ·
                      refine ⟨1328964955934154084922321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1771953274578872113229761 1328964955934154084922321)
                      ·
                        rfl

theorem cell23_2588150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 1, 2, 4, 2].length) (baseStart_2588150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2588150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2588150 prefixEnd_2588150 := by exact prefixLift 2588150
  have htrace : WordTrace (prefixWord ++ tailWord_2588150) baseStart_2588150 baseEnd_2588150 := by
    simpa [prefixWord, tailWord_2588150, baseEnd_2588150] using wordTrace_append hprefix tailTrace_2588150
  have hstable : (prefixWord ++ tailWord_2588150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2588150).length < 2 ^ (prefixWord ++ tailWord_2588150).sum := by decide
  have hdescent : baseEnd_2588150 < baseStart_2588150 := by decide
  rcases family_descends (prefixWord ++ tailWord_2588150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2588156 : List Nat := [2, 2, 2, 1, 2, 1, 2, 5, 6]
def baseStart_2588156 : Nat := 118140960795 + 2588156 * 2 ^ 59
def prefixEnd_2588156 : Nat := 4983230072969 + 3 ^ 40 * 2588156 * 2
def baseEnd_2588156 : Nat := 147663115202009006827477

theorem tailTrace_2588156 : CollatzResearch.WordTrace tailWord_2588156 prefixEnd_2588156 147663115202009006827477 := by
  unfold tailWord_2588156
  simp only [CollatzResearch.WordTrace]
  refine ⟨47198902205780154349376161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62931869607706872465834881 47198902205780154349376161)
  ·
    refine ⟨35399176654335115762032121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47198902205780154349376161 35399176654335115762032121)
    ·
      refine ⟨26549382490751336821524091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35399176654335115762032121 26549382490751336821524091)
      ·
        refine ⟨39824073736127005232286137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26549382490751336821524091 39824073736127005232286137)
        ·
          refine ⟨29868055302095253924214603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39824073736127005232286137 29868055302095253924214603)
          ·
            refine ⟨44802082953142880886321905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29868055302095253924214603 44802082953142880886321905)
            ·
              refine ⟨33601562214857160664741429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44802082953142880886321905 33601562214857160664741429)
              ·
                refine ⟨3150146457642858812319509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33601562214857160664741429 3150146457642858812319509)
                ·
                  refine ⟨147663115202009006827477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3150146457642858812319509 147663115202009006827477)
                  ·
                    rfl

theorem cell23_2588156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 5, 6].length) (baseStart_2588156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2588156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2588156 prefixEnd_2588156 := by exact prefixLift 2588156
  have htrace : WordTrace (prefixWord ++ tailWord_2588156) baseStart_2588156 baseEnd_2588156 := by
    simpa [prefixWord, tailWord_2588156, baseEnd_2588156] using wordTrace_append hprefix tailTrace_2588156
  have hstable : (prefixWord ++ tailWord_2588156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2588156).length < 2 ^ (prefixWord ++ tailWord_2588156).sum := by decide
  have hdescent : baseEnd_2588156 < baseStart_2588156 := by decide
  rcases family_descends (prefixWord ++ tailWord_2588156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2588186 : List Nat := [3, 1, 1, 3, 1, 1, 1, 2, 5, 5]
def baseStart_2588186 : Nat := 118140960795 + 2588186 * 2 ^ 59
def prefixEnd_2588186 : Nat := 4983230072969 + 3 ^ 40 * 2588186 * 2
def baseEnd_2588186 : Nat := 442994480412571981357385

theorem tailTrace_2588186 : CollatzResearch.WordTrace tailWord_2588186 prefixEnd_2588186 442994480412571981357385 := by
  unfold tailWord_2588186
  simp only [CollatzResearch.WordTrace]
  refine ⟨23599724650362905955586103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62932599067634415881562941 23599724650362905955586103)
  ·
    refine ⟨35399586975544358933379155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23599724650362905955586103 35399586975544358933379155)
    ·
      refine ⟨53099380463316538400068733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35399586975544358933379155 53099380463316538400068733)
      ·
        refine ⟨19912267673743701900025775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53099380463316538400068733 19912267673743701900025775)
        ·
          refine ⟨29868401510615552850038663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19912267673743701900025775 29868401510615552850038663)
          ·
            refine ⟨44802602265923329275057995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29868401510615552850038663 44802602265923329275057995)
            ·
              refine ⟨67203903398884993912586993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44802602265923329275057995 67203903398884993912586993)
              ·
                refine ⟨50402927549163745434440245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67203903398884993912586993 50402927549163745434440245)
                ·
                  refine ⟨4725274457734101134478773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50402927549163745434440245 4725274457734101134478773)
                  ·
                    refine ⟨442994480412571981357385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4725274457734101134478773 442994480412571981357385)
                    ·
                      rfl

theorem cell23_2588186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 5, 5].length) (baseStart_2588186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2588186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2588186 prefixEnd_2588186 := by exact prefixLift 2588186
  have htrace : WordTrace (prefixWord ++ tailWord_2588186) baseStart_2588186 baseEnd_2588186 := by
    simpa [prefixWord, tailWord_2588186, baseEnd_2588186] using wordTrace_append hprefix tailTrace_2588186
  have hstable : (prefixWord ++ tailWord_2588186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2588186).length < 2 ^ (prefixWord ++ tailWord_2588186).sum := by decide
  have hdescent : baseEnd_2588186 < baseStart_2588186 := by decide
  rcases family_descends (prefixWord ++ tailWord_2588186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2588223 : List Nat := [1, 1, 2, 2, 3, 4, 1, 1, 3, 1, 4]
def baseStart_2588223 : Nat := 118140960795 + 2588223 * 2 ^ 59
def prefixEnd_2588223 : Nat := 4983230072969 + 3 ^ 40 * 2588223 * 2
def baseEnd_2588223 : Nat := 1329002440021932299309485

theorem tailTrace_2588223 : CollatzResearch.WordTrace tailWord_2588223 prefixEnd_2588223 1329002440021932299309485 := by
  unfold tailWord_2588223
  simp only [CollatzResearch.WordTrace]
  refine ⟨94400248102317579141441323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62933498734878386094294215 94400248102317579141441323)
  ·
    refine ⟨141600372153476368712161985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94400248102317579141441323 141600372153476368712161985)
    ·
      refine ⟨106200279115107276534121489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141600372153476368712161985 106200279115107276534121489)
      ·
        refine ⟨79650209336330457400591117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106200279115107276534121489 79650209336330457400591117)
        ·
          refine ⟨29868828501123921525221669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79650209336330457400591117 29868828501123921525221669)
          ·
            refine ⟨5600405343960735285979063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29868828501123921525221669 5600405343960735285979063)
            ·
              refine ⟨8400608015941102928968595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5600405343960735285979063 8400608015941102928968595)
              ·
                refine ⟨12600912023911654393452893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8400608015941102928968595 12600912023911654393452893)
                ·
                  refine ⟨4725342008966870397544835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12600912023911654393452893 4725342008966870397544835)
                  ·
                    refine ⟨7088013013450305596317253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4725342008966870397544835 7088013013450305596317253)
                    ·
                      refine ⟨1329002440021932299309485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7088013013450305596317253 1329002440021932299309485)
                      ·
                        rfl

theorem cell23_2588223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 1, 3, 1, 4].length) (baseStart_2588223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2588223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2588223 prefixEnd_2588223 := by exact prefixLift 2588223
  have htrace : WordTrace (prefixWord ++ tailWord_2588223) baseStart_2588223 baseEnd_2588223 := by
    simpa [prefixWord, tailWord_2588223, baseEnd_2588223] using wordTrace_append hprefix tailTrace_2588223
  have hstable : (prefixWord ++ tailWord_2588223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2588223).length < 2 ^ (prefixWord ++ tailWord_2588223).sum := by decide
  have hdescent : baseEnd_2588223 < baseStart_2588223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2588223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2588240 : List Nat := [2, 1, 1, 1, 1, 3, 7, 1, 1, 1, 4]
def baseStart_2588240 : Nat := 118140960795 + 2588240 * 2 ^ 59
def prefixEnd_2588240 : Nat := 4983230072969 + 3 ^ 40 * 2588240 * 2
def baseEnd_2588240 : Nat := 1329011169193058732796907

theorem tailTrace_2588240 : CollatzResearch.WordTrace tailWord_2588240 prefixEnd_2588240 1329011169193058732796907 := by
  unfold tailWord_2588240
  simp only [CollatzResearch.WordTrace]
  refine ⟨47200434071627995522405087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62933912095503994029873449 47200434071627995522405087)
  ·
    refine ⟨70800651107441993283607631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47200434071627995522405087 70800651107441993283607631)
    ·
      refine ⟨106200976661162989925411447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70800651107441993283607631 106200976661162989925411447)
      ·
        refine ⟨159301464991744484888117171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106200976661162989925411447 159301464991744484888117171)
        ·
          refine ⟨238952197487616727332175757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159301464991744484888117171 238952197487616727332175757)
          ·
            refine ⟨89607074057856272749565909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 238952197487616727332175757 89607074057856272749565909)
            ·
              refine ⟨2100165798231006392567951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 89607074057856272749565909 2100165798231006392567951)
              ·
                refine ⟨3150248697346509588851927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2100165798231006392567951 3150248697346509588851927)
                ·
                  refine ⟨4725373046019764383277891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3150248697346509588851927 4725373046019764383277891)
                  ·
                    refine ⟨7088059569029646574916837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4725373046019764383277891 7088059569029646574916837)
                    ·
                      refine ⟨1329011169193058732796907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7088059569029646574916837 1329011169193058732796907)
                      ·
                        rfl

theorem cell23_2588240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 7, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 7, 1, 1, 1, 4].length) (baseStart_2588240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2588240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2588240 prefixEnd_2588240 := by exact prefixLift 2588240
  have htrace : WordTrace (prefixWord ++ tailWord_2588240) baseStart_2588240 baseEnd_2588240 := by
    simpa [prefixWord, tailWord_2588240, baseEnd_2588240] using wordTrace_append hprefix tailTrace_2588240
  have hstable : (prefixWord ++ tailWord_2588240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2588240).length < 2 ^ (prefixWord ++ tailWord_2588240).sum := by decide
  have hdescent : baseEnd_2588240 < baseStart_2588240 := by decide
  rcases family_descends (prefixWord ++ tailWord_2588240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2588324 : List Nat := [2, 3, 1, 2, 2, 3, 3, 1, 2, 1, 3]
def baseStart_2588324 : Nat := 118140960795 + 2588324 * 2 ^ 59
def prefixEnd_2588324 : Nat := 4983230072969 + 3 ^ 40 * 2588324 * 2
def baseEnd_2588324 : Nat := 1329054301568036404146521

theorem tailTrace_2588324 : CollatzResearch.WordTrace tailWord_2588324 prefixEnd_2588324 1329054301568036404146521 := by
  unfold tailWord_2588324
  simp only [CollatzResearch.WordTrace]
  refine ⟨47201965937475836695434013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62935954583301115593912017 47201965937475836695434013)
  ·
    refine ⟨17700737226553438760787755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47201965937475836695434013 17700737226553438760787755)
    ·
      refine ⟨26551105839830158141181633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17700737226553438760787755 26551105839830158141181633)
      ·
        refine ⟨19913329379872618605886225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26551105839830158141181633 19913329379872618605886225)
        ·
          refine ⟨14934997034904463954414669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19913329379872618605886225 14934997034904463954414669)
          ·
            refine ⟨5600623888089173982905501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14934997034904463954414669 5600623888089173982905501)
            ·
              refine ⟨2100233958033440243589563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5600623888089173982905501 2100233958033440243589563)
              ·
                refine ⟨3150350937050160365384345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2100233958033440243589563 3150350937050160365384345)
                ·
                  refine ⟨2362763202787620274038259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3150350937050160365384345 2362763202787620274038259)
                  ·
                    refine ⟨3544144804181430411057389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2362763202787620274038259 3544144804181430411057389)
                    ·
                      refine ⟨1329054301568036404146521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3544144804181430411057389 1329054301568036404146521)
                      ·
                        rfl

theorem cell23_2588324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 3, 1, 2, 1, 3].length) (baseStart_2588324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2588324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2588324 prefixEnd_2588324 := by exact prefixLift 2588324
  have htrace : WordTrace (prefixWord ++ tailWord_2588324) baseStart_2588324 baseEnd_2588324 := by
    simpa [prefixWord, tailWord_2588324, baseEnd_2588324] using wordTrace_append hprefix tailTrace_2588324
  have hstable : (prefixWord ++ tailWord_2588324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2588324).length < 2 ^ (prefixWord ++ tailWord_2588324).sum := by decide
  have hdescent : baseEnd_2588324 < baseStart_2588324 := by decide
  rcases family_descends (prefixWord ++ tailWord_2588324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2588350 : List Nat := [4, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5]
def baseStart_2588350 : Nat := 118140960795 + 2588350 * 2 ^ 59
def prefixEnd_2588350 : Nat := 4983230072969 + 3 ^ 40 * 2588350 * 2
def baseEnd_2588350 : Nat := 1329067652065053302421401

theorem tailTrace_2588350 : CollatzResearch.WordTrace tailWord_2588350 prefixEnd_2588350 1329067652065053302421401 := by
  unfold tailWord_2588350
  simp only [CollatzResearch.WordTrace]
  refine ⟨11800610021607184978914313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62936586781904986554209669 11800610021607184978914313)
  ·
    refine ⟨8850457516205388734185735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11800610021607184978914313 8850457516205388734185735)
    ·
      refine ⟨13275686274308083101278603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8850457516205388734185735 13275686274308083101278603)
      ·
        refine ⟨19913529411462124651917905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13275686274308083101278603 19913529411462124651917905)
        ·
          refine ⟨14935147058596593488938429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19913529411462124651917905 14935147058596593488938429)
          ·
            refine ⟨5600680146973722558351911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14935147058596593488938429 5600680146973722558351911)
            ·
              refine ⟨8401020220460583837527867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5600680146973722558351911 8401020220460583837527867)
              ·
                refine ⟨12601530330690875756291801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8401020220460583837527867 12601530330690875756291801)
                ·
                  refine ⟨9451147748018156817218851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12601530330690875756291801 9451147748018156817218851)
                  ·
                    refine ⟨14176721622027235225828277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9451147748018156817218851 14176721622027235225828277)
                    ·
                      refine ⟨1329067652065053302421401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14176721622027235225828277 1329067652065053302421401)
                      ·
                        rfl

theorem cell23_2588350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5].length) (baseStart_2588350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2588350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2588350 prefixEnd_2588350 := by exact prefixLift 2588350
  have htrace : WordTrace (prefixWord ++ tailWord_2588350) baseStart_2588350 baseEnd_2588350 := by
    simpa [prefixWord, tailWord_2588350, baseEnd_2588350] using wordTrace_append hprefix tailTrace_2588350
  have hstable : (prefixWord ++ tailWord_2588350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2588350).length < 2 ^ (prefixWord ++ tailWord_2588350).sum := by decide
  have hdescent : baseEnd_2588350 < baseStart_2588350 := by decide
  rcases family_descends (prefixWord ++ tailWord_2588350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2588363 : List Nat := [1, 1, 1, 1, 3, 2, 1, 3, 4, 3, 3]
def baseStart_2588363 : Nat := 118140960795 + 2588363 * 2 ^ 59
def prefixEnd_2588363 : Nat := 4983230072969 + 3 ^ 40 * 2588363 * 2
def baseEnd_2588363 : Nat := 1329074327313561751558841

theorem tailTrace_2588363 : CollatzResearch.WordTrace tailWord_2588363 prefixEnd_2588363 1329074327313561751558841 := by
  unfold tailWord_2588363
  simp only [CollatzResearch.WordTrace]
  refine ⟨94405354321810383051537743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62936902881206922034358495 94405354321810383051537743)
  ·
    refine ⟨141608031482715574577306615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94405354321810383051537743 141608031482715574577306615)
    ·
      refine ⟨212412047224073361865959923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141608031482715574577306615 212412047224073361865959923)
      ·
        refine ⟨318618070836110042798939885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212412047224073361865959923 318618070836110042798939885)
        ·
          refine ⟨119481776563541266049602457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 318618070836110042798939885 119481776563541266049602457)
          ·
            refine ⟨89611332422655949537201843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119481776563541266049602457 89611332422655949537201843)
            ·
              refine ⟨134416998633983924305802765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89611332422655949537201843 134416998633983924305802765)
              ·
                refine ⟨50406374487743971614676037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 134416998633983924305802765 50406374487743971614676037)
                ·
                  refine ⟨9451195216451994677751757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50406374487743971614676037 9451195216451994677751757)
                  ·
                    refine ⟨3544198206169498004156909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9451195216451994677751757 3544198206169498004156909)
                    ·
                      refine ⟨1329074327313561751558841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3544198206169498004156909 1329074327313561751558841)
                      ·
                        rfl

theorem cell23_2588363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 4, 3, 3].length) (baseStart_2588363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2588363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2588363 prefixEnd_2588363 := by exact prefixLift 2588363
  have htrace : WordTrace (prefixWord ++ tailWord_2588363) baseStart_2588363 baseEnd_2588363 := by
    simpa [prefixWord, tailWord_2588363, baseEnd_2588363] using wordTrace_append hprefix tailTrace_2588363
  have hstable : (prefixWord ++ tailWord_2588363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2588363).length < 2 ^ (prefixWord ++ tailWord_2588363).sum := by decide
  have hdescent : baseEnd_2588363 < baseStart_2588363 := by decide
  rcases family_descends (prefixWord ++ tailWord_2588363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2588370 : List Nat := [3, 2, 2, 2, 2, 1, 3, 1, 7]
def baseStart_2588370 : Nat := 118140960795 + 2588370 * 2 ^ 59
def prefixEnd_2588370 : Nat := 4983230072969 + 3 ^ 40 * 2588370 * 2
def baseEnd_2588370 : Nat := 147675324630904802685701

theorem tailTrace_2588370 : CollatzResearch.WordTrace tailWord_2588370 prefixEnd_2588370 147675324630904802685701 := by
  unfold tailWord_2588370
  simp only [CollatzResearch.WordTrace]
  refine ⟨23601402408196255811760641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62937073088523348831361709 23601402408196255811760641)
  ·
    refine ⟨17701051806147191858820481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23601402408196255811760641 17701051806147191858820481)
    ·
      refine ⟨13275788854610393894115361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17701051806147191858820481 13275788854610393894115361)
      ·
        refine ⟨9956841640957795420586521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13275788854610393894115361 9956841640957795420586521)
        ·
          refine ⟨7467631230718346565439891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9956841640957795420586521 7467631230718346565439891)
          ·
            refine ⟨11201446846077519848159837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7467631230718346565439891 11201446846077519848159837)
            ·
              refine ⟨4200542567279069943059939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11201446846077519848159837 4200542567279069943059939)
              ·
                refine ⟨6300813850918604914589909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4200542567279069943059939 6300813850918604914589909)
                ·
                  refine ⟨147675324630904802685701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6300813850918604914589909 147675324630904802685701)
                  ·
                    rfl

theorem cell23_2588370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 1, 7].length) (baseStart_2588370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2588370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2588370 prefixEnd_2588370 := by exact prefixLift 2588370
  have htrace : WordTrace (prefixWord ++ tailWord_2588370) baseStart_2588370 baseEnd_2588370 := by
    simpa [prefixWord, tailWord_2588370, baseEnd_2588370] using wordTrace_append hprefix tailTrace_2588370
  have hstable : (prefixWord ++ tailWord_2588370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2588370).length < 2 ^ (prefixWord ++ tailWord_2588370).sum := by decide
  have hdescent : baseEnd_2588370 < baseStart_2588370 := by decide
  rcases family_descends (prefixWord ++ tailWord_2588370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2588383 : List Nat := [1, 1, 2, 3, 2, 2, 1, 2, 4, 5]
def baseStart_2588383 : Nat := 118140960795 + 2588383 * 2 ^ 59
def prefixEnd_2588383 : Nat := 4983230072969 + 3 ^ 40 * 2588383 * 2
def baseEnd_2588383 : Nat := 443028198975550557769583

theorem tailTrace_2588383 : CollatzResearch.WordTrace tailWord_2588383 prefixEnd_2588383 443028198975550557769583 := by
  unfold tailWord_2588383
  simp only [CollatzResearch.WordTrace]
  refine ⟨94406083781737926467265803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62937389187825284311510535 94406083781737926467265803)
  ·
    refine ⟨141609125672606889700898705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94406083781737926467265803 141609125672606889700898705)
    ·
      refine ⟨106206844254455167275674029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141609125672606889700898705 106206844254455167275674029)
      ·
        refine ⟨39827566595420687728377761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106206844254455167275674029 39827566595420687728377761)
        ·
          refine ⟨29870674946565515796283321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39827566595420687728377761 29870674946565515796283321)
          ·
            refine ⟨22403006209924136847212491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29870674946565515796283321 22403006209924136847212491)
            ·
              refine ⟨33604509314886205270818737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22403006209924136847212491 33604509314886205270818737)
              ·
                refine ⟨25203381986164653953114053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33604509314886205270818737 25203381986164653953114053)
                ·
                  refine ⟨4725634122405872616208885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25203381986164653953114053 4725634122405872616208885)
                  ·
                    refine ⟨443028198975550557769583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4725634122405872616208885 443028198975550557769583)
                    ·
                      rfl

theorem cell23_2588383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 4, 5].length) (baseStart_2588383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2588383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2588383 prefixEnd_2588383 := by exact prefixLift 2588383
  have htrace : WordTrace (prefixWord ++ tailWord_2588383) baseStart_2588383 baseEnd_2588383 := by
    simpa [prefixWord, tailWord_2588383, baseEnd_2588383] using wordTrace_append hprefix tailTrace_2588383
  have hstable : (prefixWord ++ tailWord_2588383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2588383).length < 2 ^ (prefixWord ++ tailWord_2588383).sum := by decide
  have hdescent : baseEnd_2588383 < baseStart_2588383 := by decide
  rcases family_descends (prefixWord ++ tailWord_2588383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2588403 : List Nat := [1, 1, 1, 2, 2, 3, 2, 3, 1, 3, 4]
def baseStart_2588403 : Nat := 118140960795 + 2588403 * 2 ^ 59
def prefixEnd_2588403 : Nat := 4983230072969 + 3 ^ 40 * 2588403 * 2
def baseEnd_2588403 : Nat := 1329094866539741595058657

theorem tailTrace_2588403 : CollatzResearch.WordTrace tailWord_2588403 prefixEnd_2588403 1329094866539741595058657 := by
  unfold tailWord_2588403
  simp only [CollatzResearch.WordTrace]
  refine ⟨94406813241665469882993863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62937875494443646588662575 94406813241665469882993863)
  ·
    refine ⟨141610219862498204824490795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94406813241665469882993863 141610219862498204824490795)
    ·
      refine ⟨212415329793747307236736193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141610219862498204824490795 212415329793747307236736193)
      ·
        refine ⟨159311497345310480427552145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212415329793747307236736193 159311497345310480427552145)
        ·
          refine ⟨119483623008982860320664109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159311497345310480427552145 119483623008982860320664109)
          ·
            refine ⟨44806358628368572620249041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 119483623008982860320664109 44806358628368572620249041)
            ·
              refine ⟨33604768971276429465186781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44806358628368572620249041 33604768971276429465186781)
              ·
                refine ⟨12601788364228661049445043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33604768971276429465186781 12601788364228661049445043)
                ·
                  refine ⟨18902682546342991574167565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12601788364228661049445043 18902682546342991574167565)
                  ·
                    refine ⟨7088505954878621840312837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18902682546342991574167565 7088505954878621840312837)
                    ·
                      refine ⟨1329094866539741595058657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7088505954878621840312837 1329094866539741595058657)
                      ·
                        rfl

theorem cell23_2588403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 3, 1, 3, 4].length) (baseStart_2588403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2588403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2588403 prefixEnd_2588403 := by exact prefixLift 2588403
  have htrace : WordTrace (prefixWord ++ tailWord_2588403) baseStart_2588403 baseEnd_2588403 := by
    simpa [prefixWord, tailWord_2588403, baseEnd_2588403] using wordTrace_append hprefix tailTrace_2588403
  have hstable : (prefixWord ++ tailWord_2588403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2588403).length < 2 ^ (prefixWord ++ tailWord_2588403).sum := by decide
  have hdescent : baseEnd_2588403 < baseStart_2588403 := by decide
  rcases family_descends (prefixWord ++ tailWord_2588403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2588433 : List Nat := [1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 4]
def baseStart_2588433 : Nat := 118140960795 + 2588433 * 2 ^ 59
def prefixEnd_2588433 : Nat := 4983230072969 + 3 ^ 40 * 2588433 * 2
def baseEnd_2588433 : Nat := 1329110270959376477683519

theorem tailTrace_2588433 : CollatzResearch.WordTrace tailWord_2588433 prefixEnd_2588433 1329110270959376477683519 := by
  unfold tailWord_2588433
  simp only [CollatzResearch.WordTrace]
  refine ⟨94407907431556785006585953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62938604954371190004390635 94407907431556785006585953)
  ·
    refine ⟨70805930573667588754939465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94407907431556785006585953 70805930573667588754939465)
    ·
      refine ⟨53104447930250691566204599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70805930573667588754939465 53104447930250691566204599)
      ·
        refine ⟨79656671895376037349306899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53104447930250691566204599 79656671895376037349306899)
        ·
          refine ⟨119485007843064056023960349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79656671895376037349306899 119485007843064056023960349)
          ·
            refine ⟨44806877941149021008985131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 119485007843064056023960349 44806877941149021008985131)
            ·
              refine ⟨67210316911723531513477697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44806877941149021008985131 67210316911723531513477697)
              ·
                refine ⟨50407737683792648635108273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67210316911723531513477697 50407737683792648635108273)
                ·
                  refine ⟨37805803262844486476331205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50407737683792648635108273 37805803262844486476331205)
                  ·
                    refine ⟨7088588111783341214312101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37805803262844486476331205 7088588111783341214312101)
                    ·
                      refine ⟨1329110270959376477683519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7088588111783341214312101 1329110270959376477683519)
                      ·
                        rfl

theorem cell23_2588433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 4].length) (baseStart_2588433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2588433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2588433 prefixEnd_2588433 := by exact prefixLift 2588433
  have htrace : WordTrace (prefixWord ++ tailWord_2588433) baseStart_2588433 baseEnd_2588433 := by
    simpa [prefixWord, tailWord_2588433, baseEnd_2588433] using wordTrace_append hprefix tailTrace_2588433
  have hstable : (prefixWord ++ tailWord_2588433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2588433).length < 2 ^ (prefixWord ++ tailWord_2588433).sum := by decide
  have hdescent : baseEnd_2588433 < baseStart_2588433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2588433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2588437 : List Nat := [1, 3, 2, 1, 2, 4, 1, 1, 2, 4, 2]
def baseStart_2588437 : Nat := 118140960795 + 2588437 * 2 ^ 59
def prefixEnd_2588437 : Nat := 4983230072969 + 3 ^ 40 * 2588437 * 2
def baseEnd_2588437 : Nat := 1329112324881994462033501

theorem tailTrace_2588437 : CollatzResearch.WordTrace tailWord_2588437 prefixEnd_2588437 1329112324881994462033501 := by
  unfold tailWord_2588437
  simp only [CollatzResearch.WordTrace]
  refine ⟨94408053323542293689731565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62938702215694862459821043 94408053323542293689731565)
  ·
    refine ⟨35403019996328360133649337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94408053323542293689731565 35403019996328360133649337)
    ·
      refine ⟨26552264997246270100237003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35403019996328360133649337 26552264997246270100237003)
      ·
        refine ⟨39828397495869405150355505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26552264997246270100237003 39828397495869405150355505)
        ·
          refine ⟨29871298121902053862766629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39828397495869405150355505 29871298121902053862766629)
          ·
            refine ⟨5600868397856635099268743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29871298121902053862766629 5600868397856635099268743)
            ·
              refine ⟨8401302596784952648903115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5600868397856635099268743 8401302596784952648903115)
              ·
                refine ⟨12601953895177428973354673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8401302596784952648903115 12601953895177428973354673)
                ·
                  refine ⟨9451465421383071730016005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12601953895177428973354673 9451465421383071730016005)
                  ·
                    refine ⟨1772149766509325949378001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9451465421383071730016005 1772149766509325949378001)
                    ·
                      refine ⟨1329112324881994462033501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1772149766509325949378001 1329112324881994462033501)
                      ·
                        rfl

theorem cell23_2588437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 1, 2, 4, 2].length) (baseStart_2588437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2588437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2588437 prefixEnd_2588437 := by exact prefixLift 2588437
  have htrace : WordTrace (prefixWord ++ tailWord_2588437) baseStart_2588437 baseEnd_2588437 := by
    simpa [prefixWord, tailWord_2588437, baseEnd_2588437] using wordTrace_append hprefix tailTrace_2588437
  have hstable : (prefixWord ++ tailWord_2588437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2588437).length < 2 ^ (prefixWord ++ tailWord_2588437).sum := by decide
  have hdescent : baseEnd_2588437 < baseStart_2588437 := by decide
  rcases family_descends (prefixWord ++ tailWord_2588437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2588440 : List Nat := [2, 1, 2, 3, 1, 1, 2, 2, 4, 2, 3]
def baseStart_2588440 : Nat := 118140960795 + 2588440 * 2 ^ 59
def prefixEnd_2588440 : Nat := 4983230072969 + 3 ^ 40 * 2588440 * 2
def baseEnd_2588440 : Nat := 1329113865323957950295987

theorem tailTrace_2588440 : CollatzResearch.WordTrace tailWord_2588440 prefixEnd_2588440 1329113865323957950295987 := by
  unfold tailWord_2588440
  simp only [CollatzResearch.WordTrace]
  refine ⟨47204081371265712601045387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62938775161687616801393849 47204081371265712601045387)
  ·
    refine ⟨70806122056898568901568081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47204081371265712601045387 70806122056898568901568081)
    ·
      refine ⟨53104591542673926676176061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70806122056898568901568081 53104591542673926676176061)
      ·
        refine ⟨19914221828502722503566023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53104591542673926676176061 19914221828502722503566023)
        ·
          refine ⟨29871332742754083755349035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19914221828502722503566023 29871332742754083755349035)
          ·
            refine ⟨44806999114131125633023553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29871332742754083755349035 44806999114131125633023553)
            ·
              refine ⟨33605249335598344224767665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44806999114131125633023553 33605249335598344224767665)
              ·
                refine ⟨25203937001698758168575749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33605249335598344224767665 25203937001698758168575749)
                ·
                  refine ⟨4725738187818517156607953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25203937001698758168575749 4725738187818517156607953)
                  ·
                    refine ⟨3544303640863887867455965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4725738187818517156607953 3544303640863887867455965)
                    ·
                      refine ⟨1329113865323957950295987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3544303640863887867455965 1329113865323957950295987)
                      ·
                        rfl

theorem cell23_2588440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 4, 2, 3].length) (baseStart_2588440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2588440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2588440 prefixEnd_2588440 := by exact prefixLift 2588440
  have htrace : WordTrace (prefixWord ++ tailWord_2588440) baseStart_2588440 baseEnd_2588440 := by
    simpa [prefixWord, tailWord_2588440, baseEnd_2588440] using wordTrace_append hprefix tailTrace_2588440
  have hstable : (prefixWord ++ tailWord_2588440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2588440).length < 2 ^ (prefixWord ++ tailWord_2588440).sum := by decide
  have hdescent : baseEnd_2588440 < baseStart_2588440 := by decide
  rcases family_descends (prefixWord ++ tailWord_2588440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2588477 : List Nat := [1, 4, 1, 4, 1, 1, 3, 2, 6]
def baseStart_2588477 : Nat := 118140960795 + 2588477 * 2 ^ 59
def prefixEnd_2588477 : Nat := 4983230072969 + 3 ^ 40 * 2588477 * 2
def baseEnd_2588477 : Nat := 147681429345352700614813

theorem tailTrace_2588477 : CollatzResearch.WordTrace tailWord_2588477 prefixEnd_2588477 147681429345352700614813 := by
  unfold tailWord_2588477
  simp only [CollatzResearch.WordTrace]
  refine ⟨94409512243397380521187685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62939674828931587014125123 94409512243397380521187685)
  ·
    refine ⟨17701783545637008847722691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94409512243397380521187685 17701783545637008847722691)
    ·
      refine ⟨26552675318455513271584037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17701783545637008847722691 26552675318455513271584037)
      ·
        refine ⟨4978626622210408738422007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26552675318455513271584037 4978626622210408738422007)
        ·
          refine ⟨7467939933315613107633011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4978626622210408738422007 7467939933315613107633011)
          ·
            refine ⟨11201909899973419661449517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7467939933315613107633011 11201909899973419661449517)
            ·
              refine ⟨4200716212490032373043569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11201909899973419661449517 4200716212490032373043569)
              ·
                refine ⟨3150537159367524279782677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4200716212490032373043569 3150537159367524279782677)
                ·
                  refine ⟨147681429345352700614813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3150537159367524279782677 147681429345352700614813)
                  ·
                    rfl

theorem cell23_2588477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 2, 6].length) (baseStart_2588477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2588477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2588477 prefixEnd_2588477 := by exact prefixLift 2588477
  have htrace : WordTrace (prefixWord ++ tailWord_2588477) baseStart_2588477 baseEnd_2588477 := by
    simpa [prefixWord, tailWord_2588477, baseEnd_2588477] using wordTrace_append hprefix tailTrace_2588477
  have hstable : (prefixWord ++ tailWord_2588477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2588477).length < 2 ^ (prefixWord ++ tailWord_2588477).sum := by decide
  have hdescent : baseEnd_2588477 < baseStart_2588477 := by decide
  rcases family_descends (prefixWord ++ tailWord_2588477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2588487 : List Nat := [1, 1, 4, 1, 2, 1, 3, 3, 3, 1, 3]
def baseStart_2588487 : Nat := 118140960795 + 2588487 * 2 ^ 59
def prefixEnd_2588487 : Nat := 4983230072969 + 3 ^ 40 * 2588487 * 2
def baseEnd_2588487 : Nat := 1329137998914719266408271

theorem tailTrace_2588487 : CollatzResearch.WordTrace tailWord_2588487 prefixEnd_2588487 1329137998914719266408271 := by
  unfold tailWord_2588487
  simp only [CollatzResearch.WordTrace]
  refine ⟨94409876973361152229051715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62939917982240768152701143 94409876973361152229051715)
  ·
    refine ⟨141614815460041728343577573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94409876973361152229051715 141614815460041728343577573)
    ·
      refine ⟨26552777898757824064420795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 141614815460041728343577573 26552777898757824064420795)
      ·
        refine ⟨39829166848136736096631193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26552777898757824064420795 39829166848136736096631193)
        ·
          refine ⟨29871875136102552072473395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39829166848136736096631193 29871875136102552072473395)
          ·
            refine ⟨44807812704153828108710093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29871875136102552072473395 44807812704153828108710093)
            ·
              refine ⟨16802929764057685540766285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44807812704153828108710093 16802929764057685540766285)
              ·
                refine ⟨6301098661521632077787357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16802929764057685540766285 6301098661521632077787357)
                ·
                  refine ⟨2362911998070612029170259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6301098661521632077787357 2362911998070612029170259)
                  ·
                    refine ⟨3544367997105918043755389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2362911998070612029170259 3544367997105918043755389)
                    ·
                      refine ⟨1329137998914719266408271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3544367997105918043755389 1329137998914719266408271)
                      ·
                        rfl

theorem cell23_2588487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 3, 3, 1, 3].length) (baseStart_2588487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2588487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2588487 prefixEnd_2588487 := by exact prefixLift 2588487
  have htrace : WordTrace (prefixWord ++ tailWord_2588487) baseStart_2588487 baseEnd_2588487 := by
    simpa [prefixWord, tailWord_2588487, baseEnd_2588487] using wordTrace_append hprefix tailTrace_2588487
  have hstable : (prefixWord ++ tailWord_2588487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2588487).length < 2 ^ (prefixWord ++ tailWord_2588487).sum := by decide
  have hdescent : baseEnd_2588487 < baseStart_2588487 := by decide
  rcases family_descends (prefixWord ++ tailWord_2588487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2588497 : List Nat := [1, 2, 2, 1, 5, 1, 1, 2, 1, 5, 2]
def baseStart_2588497 : Nat := 118140960795 + 2588497 * 2 ^ 59
def prefixEnd_2588497 : Nat := 4983230072969 + 3 ^ 40 * 2588497 * 2
def baseEnd_2588497 : Nat := 1329143133721264227283225

theorem tailTrace_2588497 : CollatzResearch.WordTrace tailWord_2588497 prefixEnd_2588497 1329143133721264227283225 := by
  unfold tailWord_2588497
  simp only [CollatzResearch.WordTrace]
  refine ⟨94410241703324923936915745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62940161135549949291277163 94410241703324923936915745)
  ·
    refine ⟨70807681277493692952686809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94410241703324923936915745 70807681277493692952686809)
    ·
      refine ⟨53105760958120269714515107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70807681277493692952686809 53105760958120269714515107)
      ·
        refine ⟨79658641437180404571772661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53105760958120269714515107 79658641437180404571772661)
        ·
          refine ⟨7467997634735662928603687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 79658641437180404571772661 7467997634735662928603687)
          ·
            refine ⟨11201996452103494392905531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7467997634735662928603687 11201996452103494392905531)
            ·
              refine ⟨16802994678155241589358297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11201996452103494392905531 16802994678155241589358297)
              ·
                refine ⟨12602246008616431192018723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16802994678155241589358297 12602246008616431192018723)
                ·
                  refine ⟨18903369012924646788028085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12602246008616431192018723 18903369012924646788028085)
                  ·
                    refine ⟨1772190844961685636377633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18903369012924646788028085 1772190844961685636377633)
                    ·
                      refine ⟨1329143133721264227283225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1772190844961685636377633 1329143133721264227283225)
                      ·
                        rfl

theorem cell23_2588497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 2, 1, 5, 2].length) (baseStart_2588497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2588497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2588497 prefixEnd_2588497 := by exact prefixLift 2588497
  have htrace : WordTrace (prefixWord ++ tailWord_2588497) baseStart_2588497 baseEnd_2588497 := by
    simpa [prefixWord, tailWord_2588497, baseEnd_2588497] using wordTrace_append hprefix tailTrace_2588497
  have hstable : (prefixWord ++ tailWord_2588497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2588497).length < 2 ^ (prefixWord ++ tailWord_2588497).sum := by decide
  have hdescent : baseEnd_2588497 < baseStart_2588497 := by decide
  rcases family_descends (prefixWord ++ tailWord_2588497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2588514 : List Nat := [3, 3, 2, 1, 2, 1, 2, 1, 1, 5, 2]
def baseStart_2588514 : Nat := 118140960795 + 2588514 * 2 ^ 59
def prefixEnd_2588514 : Nat := 4983230072969 + 3 ^ 40 * 2588514 * 2
def baseEnd_2588514 : Nat := 1329151862892390660770647

theorem tailTrace_2588514 : CollatzResearch.WordTrace tailWord_2588514 prefixEnd_2588514 1329151862892390660770647 := by
  unfold tailWord_2588514
  simp only [CollatzResearch.WordTrace]
  refine ⟨23602715436065833960071149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62940574496175557226856397 23602715436065833960071149)
  ·
    refine ⟨8851018288524687735026681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23602715436065833960071149 8851018288524687735026681)
    ·
      refine ⟨6638263716393515801270011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8851018288524687735026681 6638263716393515801270011)
      ·
        refine ⟨9957395574590273701905017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6638263716393515801270011 9957395574590273701905017)
        ·
          refine ⟨7468046680942705276428763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9957395574590273701905017 7468046680942705276428763)
          ·
            refine ⟨11202070021414057914643145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7468046680942705276428763 11202070021414057914643145)
            ·
              refine ⟨8401552516060543435982359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11202070021414057914643145 8401552516060543435982359)
              ·
                refine ⟨12602328774090815153973539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8401552516060543435982359 12602328774090815153973539)
                ·
                  refine ⟨18903493161136222730960309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12602328774090815153973539 18903493161136222730960309)
                  ·
                    refine ⟨1772202483856520881027529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18903493161136222730960309 1772202483856520881027529)
                    ·
                      refine ⟨1329151862892390660770647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1772202483856520881027529 1329151862892390660770647)
                      ·
                        rfl

theorem cell23_2588514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 1, 1, 5, 2].length) (baseStart_2588514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2588514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2588514 prefixEnd_2588514 := by exact prefixLift 2588514
  have htrace : WordTrace (prefixWord ++ tailWord_2588514) baseStart_2588514 baseEnd_2588514 := by
    simpa [prefixWord, tailWord_2588514, baseEnd_2588514] using wordTrace_append hprefix tailTrace_2588514
  have hstable : (prefixWord ++ tailWord_2588514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2588514).length < 2 ^ (prefixWord ++ tailWord_2588514).sum := by decide
  have hdescent : baseEnd_2588514 < baseStart_2588514 := by decide
  rcases family_descends (prefixWord ++ tailWord_2588514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2588520 : List Nat := [2, 1, 4, 2, 1, 1, 2, 1, 3, 6]
def baseStart_2588520 : Nat := 118140960795 + 2588520 * 2 ^ 59
def prefixEnd_2588520 : Nat := 4983230072969 + 3 ^ 40 * 2588520 * 2
def baseEnd_2588520 : Nat := 443051647925439212431873

theorem tailTrace_2588520 : CollatzResearch.WordTrace tailWord_2588520 prefixEnd_2588520 443051647925439212431873 := by
  unfold tailWord_2588520
  simp only [CollatzResearch.WordTrace]
  refine ⟨47205540291120799432501507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62940720388161065910002009 47205540291120799432501507)
  ·
    refine ⟨70808310436681199148752261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47205540291120799432501507 70808310436681199148752261)
    ·
      refine ⟨13276558206877724840391049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70808310436681199148752261 13276558206877724840391049)
      ·
        refine ⟨9957418655158293630293287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13276558206877724840391049 9957418655158293630293287)
        ·
          refine ⟨14936127982737440445439931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9957418655158293630293287 14936127982737440445439931)
          ·
            refine ⟨22404191974106160668159897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14936127982737440445439931 22404191974106160668159897)
            ·
              refine ⟨16803143980579620501119923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22404191974106160668159897 16803143980579620501119923)
              ·
                refine ⟨25204715970869430751679885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16803143980579620501119923 25204715970869430751679885)
                ·
                  refine ⟨9451768489076036531879957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25204715970869430751679885 9451768489076036531879957)
                  ·
                    refine ⟨443051647925439212431873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9451768489076036531879957 443051647925439212431873)
                    ·
                      rfl

theorem cell23_2588520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 3, 6].length) (baseStart_2588520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2588520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2588520 prefixEnd_2588520 := by exact prefixLift 2588520
  have htrace : WordTrace (prefixWord ++ tailWord_2588520) baseStart_2588520 baseEnd_2588520 := by
    simpa [prefixWord, tailWord_2588520, baseEnd_2588520] using wordTrace_append hprefix tailTrace_2588520
  have hstable : (prefixWord ++ tailWord_2588520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2588520).length < 2 ^ (prefixWord ++ tailWord_2588520).sum := by decide
  have hdescent : baseEnd_2588520 < baseStart_2588520 := by decide
  rcases family_descends (prefixWord ++ tailWord_2588520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2588537 : List Nat := [1, 2, 1, 3, 2, 2, 2, 4, 2, 4]
def baseStart_2588537 : Nat := 118140960795 + 2588537 * 2 ^ 59
def prefixEnd_2588537 : Nat := 4983230072969 + 3 ^ 40 * 2588537 * 2
def baseEnd_2588537 : Nat := 443054557649148023594347

theorem tailTrace_2588537 : CollatzResearch.WordTrace tailWord_2588537 prefixEnd_2588537 443054557649148023594347 := by
  unfold tailWord_2588537
  simp only [CollatzResearch.WordTrace]
  refine ⟨94411700623180010768371865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62941133748786673845581243 94411700623180010768371865)
  ·
    refine ⟨70808775467385008076278899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94411700623180010768371865 70808775467385008076278899)
    ·
      refine ⟨106213163201077512114418349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70808775467385008076278899 106213163201077512114418349)
      ·
        refine ⟨39829936200404067042906881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106213163201077512114418349 39829936200404067042906881)
        ·
          refine ⟨29872452150303050282180161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39829936200404067042906881 29872452150303050282180161)
          ·
            refine ⟨22404339112727287711635121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29872452150303050282180161 22404339112727287711635121)
            ·
              refine ⟨16803254334545465783726341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22404339112727287711635121 16803254334545465783726341)
              ·
                refine ⟨3150610187727274834448689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16803254334545465783726341 3150610187727274834448689)
                ·
                  refine ⟨2362957640795456125836517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3150610187727274834448689 2362957640795456125836517)
                  ·
                    refine ⟨443054557649148023594347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2362957640795456125836517 443054557649148023594347)
                    ·
                      rfl

theorem cell23_2588537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 4, 2, 4].length) (baseStart_2588537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2588537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2588537 prefixEnd_2588537 := by exact prefixLift 2588537
  have htrace : WordTrace (prefixWord ++ tailWord_2588537) baseStart_2588537 baseEnd_2588537 := by
    simpa [prefixWord, tailWord_2588537, baseEnd_2588537] using wordTrace_append hprefix tailTrace_2588537
  have hstable : (prefixWord ++ tailWord_2588537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2588537).length < 2 ^ (prefixWord ++ tailWord_2588537).sum := by decide
  have hdescent : baseEnd_2588537 < baseStart_2588537 := by decide
  rcases family_descends (prefixWord ++ tailWord_2588537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2588558 : List Nat := [4, 1, 1, 5, 2, 1, 1, 2, 1, 5]
def baseStart_2588558 : Nat := 118140960795 + 2588558 * 2 ^ 59
def prefixEnd_2588558 : Nat := 4983230072969 + 3 ^ 40 * 2588558 * 2
def baseEnd_2588558 : Nat := 443058152013729496206815

theorem tailTrace_2588558 : CollatzResearch.WordTrace tailWord_2588558 prefixEnd_2588558 443058152013729496206815 := by
  unfold tailWord_2588558
  simp only [CollatzResearch.WordTrace]
  refine ⟨11801558319512991419360791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62941644370735954236590885 11801558319512991419360791)
  ·
    refine ⟨17702337479269487129041187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11801558319512991419360791 17702337479269487129041187)
    ·
      refine ⟨26553506218904230693561781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17702337479269487129041187 26553506218904230693561781)
      ·
        refine ⟨2489391208022271627521417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26553506218904230693561781 2489391208022271627521417)
        ·
          refine ⟨1867043406016703720641063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2489391208022271627521417 1867043406016703720641063)
          ·
            refine ⟨2800565109025055580961595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1867043406016703720641063 2800565109025055580961595)
            ·
              refine ⟨4200847663537583371442393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2800565109025055580961595 4200847663537583371442393)
              ·
                refine ⟨3150635747653187528581795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4200847663537583371442393 3150635747653187528581795)
                ·
                  refine ⟨4725953621479781292872693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3150635747653187528581795 4725953621479781292872693)
                  ·
                    refine ⟨443058152013729496206815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4725953621479781292872693 443058152013729496206815)
                    ·
                      rfl

theorem cell23_2588558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 2, 1, 5].length) (baseStart_2588558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2588558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2588558 prefixEnd_2588558 := by exact prefixLift 2588558
  have htrace : WordTrace (prefixWord ++ tailWord_2588558) baseStart_2588558 baseEnd_2588558 := by
    simpa [prefixWord, tailWord_2588558, baseEnd_2588558] using wordTrace_append hprefix tailTrace_2588558
  have hstable : (prefixWord ++ tailWord_2588558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2588558).length < 2 ^ (prefixWord ++ tailWord_2588558).sum := by decide
  have hdescent : baseEnd_2588558 < baseStart_2588558 := by decide
  rcases family_descends (prefixWord ++ tailWord_2588558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2588564 : List Nat := [2, 4, 2, 1, 1, 3, 1, 1, 3, 2, 3]
def baseStart_2588564 : Nat := 118140960795 + 2588564 * 2 ^ 59
def prefixEnd_2588564 : Nat := 4983230072969 + 3 ^ 40 * 2588564 * 2
def baseEnd_2588564 : Nat := 1329177536925115465145417

theorem tailTrace_2588564 : CollatzResearch.WordTrace tailWord_2588564 prefixEnd_2588564 1329177536925115465145417 := by
  unfold tailWord_2588564
  simp only [CollatzResearch.WordTrace]
  refine ⟨47206342697041097189802373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62941790262721462919736497 47206342697041097189802373)
  ·
    refine ⟨8851189255695205723087945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47206342697041097189802373 8851189255695205723087945)
    ·
      refine ⟨6638391941771404292315959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8851189255695205723087945 6638391941771404292315959)
      ·
        refine ⟨9957587912657106438473939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6638391941771404292315959 9957587912657106438473939)
        ·
          refine ⟨14936381868985659657710909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9957587912657106438473939 14936381868985659657710909)
          ·
            refine ⟨5601143200869622371641591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14936381868985659657710909 5601143200869622371641591)
            ·
              refine ⟨8401714801304433557462387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5601143200869622371641591 8401714801304433557462387)
              ·
                refine ⟨12602572201956650336193581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8401714801304433557462387 12602572201956650336193581)
                ·
                  refine ⟨4725964575733743876072593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12602572201956650336193581 4725964575733743876072593)
                  ·
                    refine ⟨3544473431800307907054445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4725964575733743876072593 3544473431800307907054445)
                    ·
                      refine ⟨1329177536925115465145417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3544473431800307907054445 1329177536925115465145417)
                      ·
                        rfl

theorem cell23_2588564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_2588564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2588564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2588564 prefixEnd_2588564 := by exact prefixLift 2588564
  have htrace : WordTrace (prefixWord ++ tailWord_2588564) baseStart_2588564 baseEnd_2588564 := by
    simpa [prefixWord, tailWord_2588564, baseEnd_2588564] using wordTrace_append hprefix tailTrace_2588564
  have hstable : (prefixWord ++ tailWord_2588564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2588564).length < 2 ^ (prefixWord ++ tailWord_2588564).sum := by decide
  have hdescent : baseEnd_2588564 < baseStart_2588564 := by decide
  rcases family_descends (prefixWord ++ tailWord_2588564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2588584 : List Nat := [2, 1, 6, 2, 2, 10]
def baseStart_2588584 : Nat := 118140960795 + 2588584 * 2 ^ 59
def prefixEnd_2588584 : Nat := 4983230072969 + 3 ^ 40 * 2588584 * 2
def baseEnd_2588584 : Nat := 5469908668881503649775

theorem tailTrace_2588584 : CollatzResearch.WordTrace tailWord_2588584 prefixEnd_2588584 5469908668881503649775 := by
  unfold tailWord_2588584
  simp only [CollatzResearch.WordTrace]
  refine ⟨47206707427004868897666403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62942276569339825196888537 47206707427004868897666403)
  ·
    refine ⟨70810061140507303346499605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47206707427004868897666403 70810061140507303346499605)
    ·
      refine ⟨3319221615961279844367169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 70810061140507303346499605 3319221615961279844367169)
      ·
        refine ⟨2489416211970959883275377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3319221615961279844367169 2489416211970959883275377)
        ·
          refine ⟨1867062158978219912456533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2489416211970959883275377 1867062158978219912456533)
          ·
            refine ⟨5469908668881503649775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1867062158978219912456533 5469908668881503649775)
            ·
              rfl

theorem cell23_2588584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 10].length) (baseStart_2588584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2588584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2588584 prefixEnd_2588584 := by exact prefixLift 2588584
  have htrace : WordTrace (prefixWord ++ tailWord_2588584) baseStart_2588584 baseEnd_2588584 := by
    simpa [prefixWord, tailWord_2588584, baseEnd_2588584] using wordTrace_append hprefix tailTrace_2588584
  have hstable : (prefixWord ++ tailWord_2588584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2588584).length < 2 ^ (prefixWord ++ tailWord_2588584).sum := by decide
  have hdescent : baseEnd_2588584 < baseStart_2588584 := by decide
  rcases family_descends (prefixWord ++ tailWord_2588584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2588587 : List Nat := [1, 1, 1, 1, 2, 1, 1, 3, 7, 3, 2]
def baseStart_2588587 : Nat := 118140960795 + 2588587 * 2 ^ 59
def prefixEnd_2588587 : Nat := 4983230072969 + 3 ^ 40 * 2588587 * 2
def baseEnd_2588587 : Nat := 1329189346980168875157811

theorem tailTrace_2588587 : CollatzResearch.WordTrace tailWord_2588587 prefixEnd_2588587 1329189346980168875157811 := by
  unfold tailWord_2588587
  simp only [CollatzResearch.WordTrace]
  refine ⟨94413524272998869307692015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62942349515332579538461343 94413524272998869307692015)
  ·
    refine ⟨141620286409498303961538023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94413524272998869307692015 141620286409498303961538023)
    ·
      refine ⟨212430429614247455942307035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141620286409498303961538023 212430429614247455942307035)
      ·
        refine ⟨318645644421371183913460553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212430429614247455942307035 318645644421371183913460553)
        ·
          refine ⟨238984233316028387935095415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 318645644421371183913460553 238984233316028387935095415)
          ·
            refine ⟨358476349974042581902643123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 238984233316028387935095415 358476349974042581902643123)
            ·
              refine ⟨537714524961063872853964685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 358476349974042581902643123 537714524961063872853964685)
              ·
                refine ⟨201642946860398952320236757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 537714524961063872853964685 201642946860398952320236757)
                ·
                  refine ⟨4726006567040600445005549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 201642946860398952320236757 4726006567040600445005549)
                  ·
                    refine ⟨1772252462640225166877081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4726006567040600445005549 1772252462640225166877081)
                    ·
                      refine ⟨1329189346980168875157811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1772252462640225166877081 1329189346980168875157811)
                      ·
                        rfl

theorem cell23_2588587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 7, 3, 2].length) (baseStart_2588587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2588587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2588587 prefixEnd_2588587 := by exact prefixLift 2588587
  have htrace : WordTrace (prefixWord ++ tailWord_2588587) baseStart_2588587 baseEnd_2588587 := by
    simpa [prefixWord, tailWord_2588587, baseEnd_2588587] using wordTrace_append hprefix tailTrace_2588587
  have hstable : (prefixWord ++ tailWord_2588587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2588587).length < 2 ^ (prefixWord ++ tailWord_2588587).sum := by decide
  have hdescent : baseEnd_2588587 < baseStart_2588587 := by decide
  rcases family_descends (prefixWord ++ tailWord_2588587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2588600 : List Nat := [2, 1, 2, 1, 2, 3, 1, 1, 1, 5, 4]
def baseStart_2588600 : Nat := 118140960795 + 2588600 * 2 ^ 59
def prefixEnd_2588600 : Nat := 4983230072969 + 3 ^ 40 * 2588600 * 2
def baseEnd_2588600 : Nat := 1329196022228677324295251

theorem tailTrace_2588600 : CollatzResearch.WordTrace tailWord_2588600 prefixEnd_2588600 1329196022228677324295251 := by
  unfold tailWord_2588600
  simp only [CollatzResearch.WordTrace]
  refine ⟨47206999210975886263957627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62942665614634515018610169 47206999210975886263957627)
  ·
    refine ⟨70810498816463829395936441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47206999210975886263957627 70810498816463829395936441)
    ·
      refine ⟨53107874112347872046952331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70810498816463829395936441 53107874112347872046952331)
      ·
        refine ⟨79661811168521808070428497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53107874112347872046952331 79661811168521808070428497)
        ·
          refine ⟨59746358376391356052821373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79661811168521808070428497 59746358376391356052821373)
          ·
            refine ⟨22404884391146758519808015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59746358376391356052821373 22404884391146758519808015)
            ·
              refine ⟨33607326586720137779712023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22404884391146758519808015 33607326586720137779712023)
              ·
                refine ⟨50410989880080206669568035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33607326586720137779712023 50410989880080206669568035)
                ·
                  refine ⟨75616484820120310004352053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50410989880080206669568035 75616484820120310004352053)
                  ·
                    refine ⟨7089045451886279062908005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 75616484820120310004352053 7089045451886279062908005)
                    ·
                      refine ⟨1329196022228677324295251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7089045451886279062908005 1329196022228677324295251)
                      ·
                        rfl

theorem cell23_2588600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 1, 5, 4].length) (baseStart_2588600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2588600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2588600 prefixEnd_2588600 := by exact prefixLift 2588600
  have htrace : WordTrace (prefixWord ++ tailWord_2588600) baseStart_2588600 baseEnd_2588600 := by
    simpa [prefixWord, tailWord_2588600, baseEnd_2588600] using wordTrace_append hprefix tailTrace_2588600
  have hstable : (prefixWord ++ tailWord_2588600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2588600).length < 2 ^ (prefixWord ++ tailWord_2588600).sum := by decide
  have hdescent : baseEnd_2588600 < baseStart_2588600 := by decide
  rcases family_descends (prefixWord ++ tailWord_2588600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2588617 : List Nat := [1, 2, 1, 1, 2, 1, 2, 2, 5, 4, 2]
def baseStart_2588617 : Nat := 118140960795 + 2588617 * 2 ^ 59
def prefixEnd_2588617 : Nat := 4983230072969 + 3 ^ 40 * 2588617 * 2
def baseEnd_2588617 : Nat := 1329204751399803757782673

theorem tailTrace_2588617 : CollatzResearch.WordTrace tailWord_2588617 prefixEnd_2588617 1329204751399803757782673 := by
  unfold tailWord_2588617
  simp only [CollatzResearch.WordTrace]
  refine ⟨94414618462890184431284105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62943078975260122954189403 94414618462890184431284105)
  ·
    refine ⟨70810963847167638323463079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94414618462890184431284105 70810963847167638323463079)
    ·
      refine ⟨106216445770751457485194619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70810963847167638323463079 106216445770751457485194619)
      ·
        refine ⟨159324668656127186227791929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106216445770751457485194619 159324668656127186227791929)
        ·
          refine ⟨119493501492095389670843947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159324668656127186227791929 119493501492095389670843947)
          ·
            refine ⟨179240252238143084506265921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119493501492095389670843947 179240252238143084506265921)
            ·
              refine ⟨134430189178607313379699441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 179240252238143084506265921 134430189178607313379699441)
              ·
                refine ⟨100822641883955485034774581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 134430189178607313379699441 100822641883955485034774581)
                ·
                  refine ⟨9452122676620826722010117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 100822641883955485034774581 9452122676620826722010117)
                  ·
                    refine ⟨1772273001866405010376897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9452122676620826722010117 1772273001866405010376897)
                    ·
                      refine ⟨1329204751399803757782673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1772273001866405010376897 1329204751399803757782673)
                      ·
                        rfl

theorem cell23_2588617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 5, 4, 2].length) (baseStart_2588617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2588617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2588617 prefixEnd_2588617 := by exact prefixLift 2588617
  have htrace : WordTrace (prefixWord ++ tailWord_2588617) baseStart_2588617 baseEnd_2588617 := by
    simpa [prefixWord, tailWord_2588617, baseEnd_2588617] using wordTrace_append hprefix tailTrace_2588617
  have hstable : (prefixWord ++ tailWord_2588617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2588617).length < 2 ^ (prefixWord ++ tailWord_2588617).sum := by decide
  have hdescent : baseEnd_2588617 < baseStart_2588617 := by decide
  rcases family_descends (prefixWord ++ tailWord_2588617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2588667 : List Nat := [1, 1, 1, 1, 1, 3, 6, 1, 2, 3, 3]
def baseStart_2588667 : Nat := 118140960795 + 2588667 * 2 ^ 59
def prefixEnd_2588667 : Nat := 4983230072969 + 3 ^ 40 * 2588667 * 2
def baseEnd_2588667 : Nat := 1329230425432528562157443

theorem tailTrace_2588667 : CollatzResearch.WordTrace tailWord_2588667 prefixEnd_2588667 1329230425432528562157443 := by
  unfold tailWord_2588667
  simp only [CollatzResearch.WordTrace]
  refine ⟨94416442112709042970604255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62944294741806028647069503 94416442112709042970604255)
  ·
    refine ⟨141624663169063564455906383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94416442112709042970604255 141624663169063564455906383)
    ·
      refine ⟨212436994753595346683859575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141624663169063564455906383 212436994753595346683859575)
      ·
        refine ⟨318655492130393020025789363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212436994753595346683859575 318655492130393020025789363)
        ·
          refine ⟨477983238195589530038684045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 318655492130393020025789363 477983238195589530038684045)
          ·
            refine ⟨179243714323346073764506517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 477983238195589530038684045 179243714323346073764506517)
            ·
              refine ⟨8402049108906847207711243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 179243714323346073764506517 8402049108906847207711243)
              ·
                refine ⟨12603073663360270811566865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8402049108906847207711243 12603073663360270811566865)
                ·
                  refine ⟨9452305247520203108675149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12603073663360270811566865 9452305247520203108675149)
                  ·
                    refine ⟨3544614467820076165753181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9452305247520203108675149 3544614467820076165753181)
                    ·
                      refine ⟨1329230425432528562157443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3544614467820076165753181 1329230425432528562157443)
                      ·
                        rfl

theorem cell23_2588667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 1, 2, 3, 3].length) (baseStart_2588667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2588667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2588667 prefixEnd_2588667 := by exact prefixLift 2588667
  have htrace : WordTrace (prefixWord ++ tailWord_2588667) baseStart_2588667 baseEnd_2588667 := by
    simpa [prefixWord, tailWord_2588667, baseEnd_2588667] using wordTrace_append hprefix tailTrace_2588667
  have hstable : (prefixWord ++ tailWord_2588667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2588667).length < 2 ^ (prefixWord ++ tailWord_2588667).sum := by decide
  have hdescent : baseEnd_2588667 < baseStart_2588667 := by decide
  rcases family_descends (prefixWord ++ tailWord_2588667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2588668 : List Nat := [2, 2, 2, 1, 2, 2, 5, 1, 2, 2, 2]
def baseStart_2588668 : Nat := 118140960795 + 2588668 * 2 ^ 59
def prefixEnd_2588668 : Nat := 4983230072969 + 3 ^ 40 * 2588668 * 2
def baseEnd_2588668 : Nat := 1329230938913183058244939

theorem tailTrace_2588668 : CollatzResearch.WordTrace tailWord_2588668 prefixEnd_2588668 1329230938913183058244939 := by
  unfold tailWord_2588668
  simp only [CollatzResearch.WordTrace]
  refine ⟨47208239292852710070695329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62944319057136946760927105 47208239292852710070695329)
  ·
    refine ⟨35406179469639532553021497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47208239292852710070695329 35406179469639532553021497)
    ·
      refine ⟨26554634602229649414766123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35406179469639532553021497 26554634602229649414766123)
      ·
        refine ⟨39831951903344474122149185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26554634602229649414766123 39831951903344474122149185)
        ·
          refine ⟨29873963927508355591611889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39831951903344474122149185 29873963927508355591611889)
          ·
            refine ⟨22405472945631266693708917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29873963927508355591611889 22405472945631266693708917)
            ·
              refine ⟨2100513088652931252535211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22405472945631266693708917 2100513088652931252535211)
              ·
                refine ⟨3150769632979396878802817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2100513088652931252535211 3150769632979396878802817)
                ·
                  refine ⟨2363077224734547659102113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3150769632979396878802817 2363077224734547659102113)
                  ·
                    refine ⟨1772307918550910744326585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2363077224734547659102113 1772307918550910744326585)
                    ·
                      refine ⟨1329230938913183058244939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1772307918550910744326585 1329230938913183058244939)
                      ·
                        rfl

theorem cell23_2588668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 5, 1, 2, 2, 2].length) (baseStart_2588668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2588668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2588668 prefixEnd_2588668 := by exact prefixLift 2588668
  have htrace : WordTrace (prefixWord ++ tailWord_2588668) baseStart_2588668 baseEnd_2588668 := by
    simpa [prefixWord, tailWord_2588668, baseEnd_2588668] using wordTrace_append hprefix tailTrace_2588668
  have hstable : (prefixWord ++ tailWord_2588668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2588668).length < 2 ^ (prefixWord ++ tailWord_2588668).sum := by decide
  have hdescent : baseEnd_2588668 < baseStart_2588668 := by decide
  rcases family_descends (prefixWord ++ tailWord_2588668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2588708 : List Nat := [2, 3, 1, 4, 2, 1, 3, 2, 5]
def baseStart_2588708 : Nat := 118140960795 + 2588708 * 2 ^ 59
def prefixEnd_2588708 : Nat := 4983230072969 + 3 ^ 40 * 2588708 * 2
def baseEnd_2588708 : Nat := 147694608682151433527195

theorem tailTrace_2588708 : CollatzResearch.WordTrace tailWord_2588708 prefixEnd_2588708 147694608682151433527195 := by
  unfold tailWord_2588708
  simp only [CollatzResearch.WordTrace]
  refine ⟨47208968752780253486423389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62945291670373671315231185 47208968752780253486423389)
  ·
    refine ⟨17703363282292595057408771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47208968752780253486423389 17703363282292595057408771)
    ·
      refine ⟨26555044923438892586113157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17703363282292595057408771 26555044923438892586113157)
      ·
        refine ⟨4979070923144792359896217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26555044923438892586113157 4979070923144792359896217)
        ·
          refine ⟨3734303192358594269922163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4979070923144792359896217 3734303192358594269922163)
          ·
            refine ⟨5601454788537891404883245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3734303192358594269922163 5601454788537891404883245)
            ·
              refine ⟨2100545545701709276831217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5601454788537891404883245 2100545545701709276831217)
              ·
                refine ⟨1575409159276281957623413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2100545545701709276831217 1575409159276281957623413)
                ·
                  refine ⟨147694608682151433527195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1575409159276281957623413 147694608682151433527195)
                  ·
                    rfl

theorem cell23_2588708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 3, 2, 5].length) (baseStart_2588708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2588708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2588708 prefixEnd_2588708 := by exact prefixLift 2588708
  have htrace : WordTrace (prefixWord ++ tailWord_2588708) baseStart_2588708 baseEnd_2588708 := by
    simpa [prefixWord, tailWord_2588708, baseEnd_2588708] using wordTrace_append hprefix tailTrace_2588708
  have hstable : (prefixWord ++ tailWord_2588708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2588708).length < 2 ^ (prefixWord ++ tailWord_2588708).sum := by decide
  have hdescent : baseEnd_2588708 < baseStart_2588708 := by decide
  rcases family_descends (prefixWord ++ tailWord_2588708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2588714 : List Nat := [3, 1, 4, 1, 2, 2, 1, 1, 1, 2, 5]
def baseStart_2588714 : Nat := 118140960795 + 2588714 * 2 ^ 59
def prefixEnd_2588714 : Nat := 4983230072969 + 3 ^ 40 * 2588714 * 2
def baseEnd_2588714 : Nat := 1329254559023289878269727

theorem tailTrace_2588714 : CollatzResearch.WordTrace tailWord_2588714 prefixEnd_2588714 1329254559023289878269727 := by
  unfold tailWord_2588714
  simp only [CollatzResearch.WordTrace]
  refine ⟨23604539085884692499391299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62945437562359179998376797 23604539085884692499391299)
  ·
    refine ⟨35406808628827038749086949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23604539085884692499391299 35406808628827038749086949)
    ·
      refine ⟨6638776617905069765453803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35406808628827038749086949 6638776617905069765453803)
      ·
        refine ⟨9958164926857604648180705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6638776617905069765453803 9958164926857604648180705)
        ·
          refine ⟨7468623695143203486135529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9958164926857604648180705 7468623695143203486135529)
          ·
            refine ⟨5601467771357402614601647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7468623695143203486135529 5601467771357402614601647)
            ·
              refine ⟨8402201657036103921902471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5601467771357402614601647 8402201657036103921902471)
              ·
                refine ⟨12603302485554155882853707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8402201657036103921902471 12603302485554155882853707)
                ·
                  refine ⟨18904953728331233824280561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12603302485554155882853707 18904953728331233824280561)
                  ·
                    refine ⟨14178715296248425368210421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18904953728331233824280561 14178715296248425368210421)
                    ·
                      refine ⟨1329254559023289878269727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14178715296248425368210421 1329254559023289878269727)
                      ·
                        rfl

theorem cell23_2588714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_2588714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2588714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2588714 prefixEnd_2588714 := by exact prefixLift 2588714
  have htrace : WordTrace (prefixWord ++ tailWord_2588714) baseStart_2588714 baseEnd_2588714 := by
    simpa [prefixWord, tailWord_2588714, baseEnd_2588714] using wordTrace_append hprefix tailTrace_2588714
  have hstable : (prefixWord ++ tailWord_2588714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2588714).length < 2 ^ (prefixWord ++ tailWord_2588714).sum := by decide
  have hdescent : baseEnd_2588714 < baseStart_2588714 := by decide
  rcases family_descends (prefixWord ++ tailWord_2588714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2588727 : List Nat := [1, 1, 3, 1, 2, 2, 2, 1, 3, 4, 3]
def baseStart_2588727 : Nat := 118140960795 + 2588727 * 2 ^ 59
def prefixEnd_2588727 : Nat := 4983230072969 + 3 ^ 40 * 2588727 * 2
def baseEnd_2588727 : Nat := 1329261234271798327407167

theorem tailTrace_2588727 : CollatzResearch.WordTrace tailWord_2588727 prefixEnd_2588727 1329261234271798327407167 := by
  unfold tailWord_2588727
  simp only [CollatzResearch.WordTrace]
  refine ⟨94418630492491673217788435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62945753661661115478525623 94418630492491673217788435)
  ·
    refine ⟨141627945738737509826682653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94418630492491673217788435 141627945738737509826682653)
    ·
      refine ⟨53110479652026566185005995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141627945738737509826682653 53110479652026566185005995)
      ·
        refine ⟨79665719478039849277508993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53110479652026566185005995 79665719478039849277508993)
        ·
          refine ⟨59749289608529886958131745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79665719478039849277508993 59749289608529886958131745)
          ·
            refine ⟨44811967206397415218598809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59749289608529886958131745 44811967206397415218598809)
            ·
              refine ⟨33608975404798061413949107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44811967206397415218598809 33608975404798061413949107)
              ·
                refine ⟨50413463107197092120923661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33608975404798061413949107 50413463107197092120923661)
                ·
                  refine ⟨18905048665198909545346373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50413463107197092120923661 18905048665198909545346373)
                  ·
                    refine ⟨3544696624724795539752445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18905048665198909545346373 3544696624724795539752445)
                    ·
                      refine ⟨1329261234271798327407167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3544696624724795539752445 1329261234271798327407167)
                      ·
                        rfl

theorem cell23_2588727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 3, 4, 3].length) (baseStart_2588727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2588727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2588727 prefixEnd_2588727 := by exact prefixLift 2588727
  have htrace : WordTrace (prefixWord ++ tailWord_2588727) baseStart_2588727 baseEnd_2588727 := by
    simpa [prefixWord, tailWord_2588727, baseEnd_2588727] using wordTrace_append hprefix tailTrace_2588727
  have hstable : (prefixWord ++ tailWord_2588727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2588727).length < 2 ^ (prefixWord ++ tailWord_2588727).sum := by decide
  have hdescent : baseEnd_2588727 < baseStart_2588727 := by decide
  rcases family_descends (prefixWord ++ tailWord_2588727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2588758 : List Nat := [5, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4]
def baseStart_2588758 : Nat := 118140960795 + 2588758 * 2 ^ 59
def prefixEnd_2588758 : Nat := 4983230072969 + 3 ^ 40 * 2588758 * 2
def baseEnd_2588758 : Nat := 1329277152172087706119525

theorem tailTrace_2588758 : CollatzResearch.WordTrace tailWord_2588758 prefixEnd_2588758 1329277152172087706119525 := by
  unfold tailWord_2588758
  simp only [CollatzResearch.WordTrace]
  refine ⟨5901235072211210344510433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 62946507436919577008111285 5901235072211210344510433)
  ·
    refine ⟨4425926304158407758382825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5901235072211210344510433 4425926304158407758382825)
    ·
      refine ⟨3319444728118805818787119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4425926304158407758382825 3319444728118805818787119)
      ·
        refine ⟨4979167092178208728180679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3319444728118805818787119 4979167092178208728180679)
        ·
          refine ⟨7468750638267313092271019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4979167092178208728180679 7468750638267313092271019)
          ·
            refine ⟨11203125957400969638406529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7468750638267313092271019 11203125957400969638406529)
            ·
              refine ⟨8402344468050727228804897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11203125957400969638406529 8402344468050727228804897)
              ·
                refine ⟨6301758351038045421603673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8402344468050727228804897 6301758351038045421603673)
                ·
                  refine ⟨4726318763278534066202755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6301758351038045421603673 4726318763278534066202755)
                  ·
                    refine ⟨7089478144917801099304133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4726318763278534066202755 7089478144917801099304133)
                    ·
                      refine ⟨1329277152172087706119525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7089478144917801099304133 1329277152172087706119525)
                      ·
                        rfl

theorem cell23_2588758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_2588758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2588758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2588758 prefixEnd_2588758 := by exact prefixLift 2588758
  have htrace : WordTrace (prefixWord ++ tailWord_2588758) baseStart_2588758 baseEnd_2588758 := by
    simpa [prefixWord, tailWord_2588758, baseEnd_2588758] using wordTrace_append hprefix tailTrace_2588758
  have hstable : (prefixWord ++ tailWord_2588758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2588758).length < 2 ^ (prefixWord ++ tailWord_2588758).sum := by decide
  have hdescent : baseEnd_2588758 < baseStart_2588758 := by decide
  rcases family_descends (prefixWord ++ tailWord_2588758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2588764 : List Nat := [2, 2, 4, 1, 1, 2, 1, 4, 6]
def baseStart_2588764 : Nat := 118140960795 + 2588764 * 2 ^ 59
def prefixEnd_2588764 : Nat := 4983230072969 + 3 ^ 40 * 2588764 * 2
def baseEnd_2588764 : Nat := 147697803672890520293833

theorem tailTrace_2588764 : CollatzResearch.WordTrace tailWord_2588764 prefixEnd_2588764 147697803672890520293833 := by
  unfold tailWord_2588764
  simp only [CollatzResearch.WordTrace]
  refine ⟨47209989996678814268442673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62946653328905085691256897 47209989996678814268442673)
  ·
    refine ⟨35407492497509110701332005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47209989996678814268442673 35407492497509110701332005)
    ·
      refine ⟨6638904843282958256499751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35407492497509110701332005 6638904843282958256499751)
      ·
        refine ⟨9958357264924437384749627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6638904843282958256499751 9958357264924437384749627)
        ·
          refine ⟨14937535897386656077124441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9958357264924437384749627 14937535897386656077124441)
          ·
            refine ⟨11203151923039992057843331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14937535897386656077124441 11203151923039992057843331)
            ·
              refine ⟨16804727884559988086764997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11203151923039992057843331 16804727884559988086764997)
              ·
                refine ⟨3150886478354997766268437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16804727884559988086764997 3150886478354997766268437)
                ·
                  refine ⟨147697803672890520293833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3150886478354997766268437 147697803672890520293833)
                  ·
                    rfl

theorem cell23_2588764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 4, 6].length) (baseStart_2588764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2588764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2588764 prefixEnd_2588764 := by exact prefixLift 2588764
  have htrace : WordTrace (prefixWord ++ tailWord_2588764) baseStart_2588764 baseEnd_2588764 := by
    simpa [prefixWord, tailWord_2588764, baseEnd_2588764] using wordTrace_append hprefix tailTrace_2588764
  have hstable : (prefixWord ++ tailWord_2588764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2588764).length < 2 ^ (prefixWord ++ tailWord_2588764).sum := by decide
  have hdescent : baseEnd_2588764 < baseStart_2588764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2588764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2588768 : List Nat := [2, 1, 1, 3, 2, 3, 4, 2, 1, 4]
def baseStart_2588768 : Nat := 118140960795 + 2588768 * 2 ^ 59
def prefixEnd_2588768 : Nat := 4983230072969 + 3 ^ 40 * 2588768 * 2
def baseEnd_2588768 : Nat := 443094095659544222331493

theorem tailTrace_2588768 : CollatzResearch.WordTrace tailWord_2588768 prefixEnd_2588768 443094095659544222331493 := by
  unfold tailWord_2588768
  simp only [CollatzResearch.WordTrace]
  refine ⟨47210062942671568610015479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62946750590228758146687305 47210062942671568610015479)
  ·
    refine ⟨70815094414007352915023219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47210062942671568610015479 70815094414007352915023219)
    ·
      refine ⟨106222641621011029372534829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70815094414007352915023219 106222641621011029372534829)
      ·
        refine ⟨39833490607879136014700561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106222641621011029372534829 39833490607879136014700561)
        ·
          refine ⟨29875117955909352011025421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39833490607879136014700561 29875117955909352011025421)
          ·
            refine ⟨11203169233466007004134533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29875117955909352011025421 11203169233466007004134533)
            ·
              refine ⟨2100594231274876313275225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11203169233466007004134533 2100594231274876313275225)
              ·
                refine ⟨1575445673456157234956419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2100594231274876313275225 1575445673456157234956419)
                ·
                  refine ⟨2363168510184235852434629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1575445673456157234956419 2363168510184235852434629)
                  ·
                    refine ⟨443094095659544222331493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2363168510184235852434629 443094095659544222331493)
                    ·
                      rfl

theorem cell23_2588768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 4, 2, 1, 4].length) (baseStart_2588768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2588768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2588768 prefixEnd_2588768 := by exact prefixLift 2588768
  have htrace : WordTrace (prefixWord ++ tailWord_2588768) baseStart_2588768 baseEnd_2588768 := by
    simpa [prefixWord, tailWord_2588768, baseEnd_2588768] using wordTrace_append hprefix tailTrace_2588768
  have hstable : (prefixWord ++ tailWord_2588768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2588768).length < 2 ^ (prefixWord ++ tailWord_2588768).sum := by decide
  have hdescent : baseEnd_2588768 < baseStart_2588768 := by decide
  rcases family_descends (prefixWord ++ tailWord_2588768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2588777 : List Nat := [1, 2, 1, 1, 1, 5, 1, 1, 5, 5]
def baseStart_2588777 : Nat := 118140960795 + 2588777 * 2 ^ 59
def prefixEnd_2588777 : Nat := 4983230072969 + 3 ^ 40 * 2588777 * 2
def baseEnd_2588777 : Nat := 443095636101507710593979

theorem tailTrace_2588777 : CollatzResearch.WordTrace tailWord_2588777 prefixEnd_2588777 443095636101507710593979 := by
  unfold tailWord_2588777
  simp only [CollatzResearch.WordTrace]
  refine ⟨94420454142310531757108585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62946969428207021171405723 94420454142310531757108585)
  ·
    refine ⟨70815340606732898817831439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94420454142310531757108585 70815340606732898817831439)
    ·
      refine ⟨106223010910099348226747159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70815340606732898817831439 106223010910099348226747159)
      ·
        refine ⟨159334516365149022340120739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106223010910099348226747159 159334516365149022340120739)
        ·
          refine ⟨239001774547723533510181109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159334516365149022340120739 239001774547723533510181109)
          ·
            refine ⟨22406416363849081266579479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 239001774547723533510181109 22406416363849081266579479)
            ·
              refine ⟨33609624545773621899869219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22406416363849081266579479 33609624545773621899869219)
              ·
                refine ⟨50414436818660432849803829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33609624545773621899869219 50414436818660432849803829)
                ·
                  refine ⟨4726353451749415579669109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50414436818660432849803829 4726353451749415579669109)
                  ·
                    refine ⟨443095636101507710593979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4726353451749415579669109 443095636101507710593979)
                    ·
                      rfl

theorem cell23_2588777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 5, 5].length) (baseStart_2588777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2588777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2588777 prefixEnd_2588777 := by exact prefixLift 2588777
  have htrace : WordTrace (prefixWord ++ tailWord_2588777) baseStart_2588777 baseEnd_2588777 := by
    simpa [prefixWord, tailWord_2588777, baseEnd_2588777] using wordTrace_append hprefix tailTrace_2588777
  have hstable : (prefixWord ++ tailWord_2588777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2588777).length < 2 ^ (prefixWord ++ tailWord_2588777).sum := by decide
  have hdescent : baseEnd_2588777 < baseStart_2588777 := by decide
  rcases family_descends (prefixWord ++ tailWord_2588777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2588791 : List Nat := [1, 1, 3, 1, 1, 6, 1, 2, 3, 1, 3]
def baseStart_2588791 : Nat := 118140960795 + 2588791 * 2 ^ 59
def prefixEnd_2588791 : Nat := 4983230072969 + 3 ^ 40 * 2588791 * 2
def baseEnd_2588791 : Nat := 1329294097033686077006873

theorem tailTrace_2588791 : CollatzResearch.WordTrace tailWord_2588791 prefixEnd_2588791 1329294097033686077006873 := by
  unfold tailWord_2588791
  simp only [CollatzResearch.WordTrace]
  refine ⟨94420964764259812148118227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62947309842839874765412151 94420964764259812148118227)
  ·
    refine ⟨141631447146389718222177341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94420964764259812148118227 141631447146389718222177341)
    ·
      refine ⟨53111792679896144333316503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141631447146389718222177341 53111792679896144333316503)
      ·
        refine ⟨79667689019844216499974755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53111792679896144333316503 79667689019844216499974755)
        ·
          refine ⟨119501533529766324749962133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79667689019844216499974755 119501533529766324749962133)
          ·
            refine ⟨5601634384207796472654475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 119501533529766324749962133 5601634384207796472654475)
            ·
              refine ⟨8402451576311694708981713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5601634384207796472654475 8402451576311694708981713)
              ·
                refine ⟨6301838682233771031736285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8402451576311694708981713 6301838682233771031736285)
                ·
                  refine ⟨2363189505837664136901107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6301838682233771031736285 2363189505837664136901107)
                  ·
                    refine ⟨3544784258756496205351661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2363189505837664136901107 3544784258756496205351661)
                    ·
                      refine ⟨1329294097033686077006873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3544784258756496205351661 1329294097033686077006873)
                      ·
                        rfl

theorem cell23_2588791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 2, 3, 1, 3].length) (baseStart_2588791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2588791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2588791 prefixEnd_2588791 := by exact prefixLift 2588791
  have htrace : WordTrace (prefixWord ++ tailWord_2588791) baseStart_2588791 baseEnd_2588791 := by
    simpa [prefixWord, tailWord_2588791, baseEnd_2588791] using wordTrace_append hprefix tailTrace_2588791
  have hstable : (prefixWord ++ tailWord_2588791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2588791).length < 2 ^ (prefixWord ++ tailWord_2588791).sum := by decide
  have hdescent : baseEnd_2588791 < baseStart_2588791 := by decide
  rcases family_descends (prefixWord ++ tailWord_2588791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2588817 : List Nat := [1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 5]
def baseStart_2588817 : Nat := 118140960795 + 2588817 * 2 ^ 59
def prefixEnd_2588817 : Nat := 4983230072969 + 3 ^ 40 * 2588817 * 2
def baseEnd_2588817 : Nat := 1329307447530702975281753

theorem tailTrace_2588817 : CollatzResearch.WordTrace tailWord_2588817 prefixEnd_2588817 1329307447530702975281753 := by
  unfold tailWord_2588817
  simp only [CollatzResearch.WordTrace]
  refine ⟨94421913062165618588564705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62947942041443745725709803 94421913062165618588564705)
  ·
    refine ⟨70816434796624213941423529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94421913062165618588564705 70816434796624213941423529)
    ·
      refine ⟨53112326097468160456067647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70816434796624213941423529 53112326097468160456067647)
      ·
        refine ⟨79668489146202240684101471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53112326097468160456067647 79668489146202240684101471)
        ·
          refine ⟨119502733719303361026152207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79668489146202240684101471 119502733719303361026152207)
          ·
            refine ⟨179254100578955041539228311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119502733719303361026152207 179254100578955041539228311)
            ·
              refine ⟨268881150868432562308842467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 179254100578955041539228311 268881150868432562308842467)
              ·
                refine ⟨403321726302648843463263701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 268881150868432562308842467 403321726302648843463263701)
                ·
                  refine ⟨9452852960218332268670243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 403321726302648843463263701 9452852960218332268670243)
                  ·
                    refine ⟨14179279440327498403005365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9452852960218332268670243 14179279440327498403005365)
                    ·
                      refine ⟨1329307447530702975281753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14179279440327498403005365 1329307447530702975281753)
                      ·
                        rfl

theorem cell23_2588817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 5].length) (baseStart_2588817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2588817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2588817 prefixEnd_2588817 := by exact prefixLift 2588817
  have htrace : WordTrace (prefixWord ++ tailWord_2588817) baseStart_2588817 baseEnd_2588817 := by
    simpa [prefixWord, tailWord_2588817, baseEnd_2588817] using wordTrace_append hprefix tailTrace_2588817
  have hstable : (prefixWord ++ tailWord_2588817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2588817).length < 2 ^ (prefixWord ++ tailWord_2588817).sum := by decide
  have hdescent : baseEnd_2588817 < baseStart_2588817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2588817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2588837 : List Nat := [1, 3, 1, 2, 1, 3, 2, 10]
def baseStart_2588837 : Nat := 118140960795 + 2588837 * 2 ^ 59
def prefixEnd_2588837 : Nat := 4983230072969 + 3 ^ 40 * 2588837 * 2
def baseEnd_2588837 : Nat := 49233989523844181371543

theorem tailTrace_2588837 : CollatzResearch.WordTrace tailWord_2588837 prefixEnd_2588837 49233989523844181371543 := by
  unfold tailWord_2588837
  simp only [CollatzResearch.WordTrace]
  refine ⟨94422642522093162004292765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62948428348062108002861843 94422642522093162004292765)
  ·
    refine ⟨35408490945784935751609787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94422642522093162004292765 35408490945784935751609787)
    ·
      refine ⟨53112736418677403627414681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35408490945784935751609787 53112736418677403627414681)
      ·
        refine ⟨39834552314008052720561011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53112736418677403627414681 39834552314008052720561011)
        ·
          refine ⟨59751828471012079080841517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39834552314008052720561011 59751828471012079080841517)
          ·
            refine ⟨22406935676629529655315569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59751828471012079080841517 22406935676629529655315569)
            ·
              refine ⟨16805201757472147241486677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22406935676629529655315569 16805201757472147241486677)
              ·
                refine ⟨49233989523844181371543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 16805201757472147241486677 49233989523844181371543)
                ·
                  rfl

theorem cell23_2588837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 10].length) (baseStart_2588837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2588837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2588837 prefixEnd_2588837 := by exact prefixLift 2588837
  have htrace : WordTrace (prefixWord ++ tailWord_2588837) baseStart_2588837 baseEnd_2588837 := by
    simpa [prefixWord, tailWord_2588837, baseEnd_2588837] using wordTrace_append hprefix tailTrace_2588837
  have hstable : (prefixWord ++ tailWord_2588837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2588837).length < 2 ^ (prefixWord ++ tailWord_2588837).sum := by decide
  have hdescent : baseEnd_2588837 < baseStart_2588837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2588837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2588868 : List Nat := [2, 3, 3, 1, 2, 1, 2, 3, 1, 2, 3]
def baseStart_2588868 : Nat := 118140960795 + 2588868 * 2 ^ 59
def prefixEnd_2588868 : Nat := 4983230072969 + 3 ^ 40 * 2588868 * 2
def baseEnd_2588868 : Nat := 1329333635044082275744019

theorem tailTrace_2588868 : CollatzResearch.WordTrace tailWord_2588868 prefixEnd_2588868 1329333635044082275744019 := by
  unfold tailWord_2588868
  simp only [CollatzResearch.WordTrace]
  refine ⟨47211886592490427149335629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62949182123320569532447505 47211886592490427149335629)
  ·
    refine ⟨17704457472183910181000861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47211886592490427149335629 17704457472183910181000861)
    ·
      refine ⟨6639171552068966317875323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17704457472183910181000861 6639171552068966317875323)
      ·
        refine ⟨9958757328103449476812985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6639171552068966317875323 9958757328103449476812985)
        ·
          refine ⟨7469067996077587107609739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9958757328103449476812985 7469067996077587107609739)
          ·
            refine ⟨11203601994116380661414609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7469067996077587107609739 11203601994116380661414609)
            ·
              refine ⟨8402701495587285496060957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11203601994116380661414609 8402701495587285496060957)
              ·
                refine ⟨3151013060845232061022859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8402701495587285496060957 3151013060845232061022859)
                ·
                  refine ⟨4726519591267848091534289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3151013060845232061022859 4726519591267848091534289)
                  ·
                    refine ⟨3544889693450886068650717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4726519591267848091534289 3544889693450886068650717)
                    ·
                      refine ⟨1329333635044082275744019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3544889693450886068650717 1329333635044082275744019)
                      ·
                        rfl

theorem cell23_2588868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 3, 1, 2, 3].length) (baseStart_2588868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2588868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2588868 prefixEnd_2588868 := by exact prefixLift 2588868
  have htrace : WordTrace (prefixWord ++ tailWord_2588868) baseStart_2588868 baseEnd_2588868 := by
    simpa [prefixWord, tailWord_2588868, baseEnd_2588868] using wordTrace_append hprefix tailTrace_2588868
  have hstable : (prefixWord ++ tailWord_2588868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2588868).length < 2 ^ (prefixWord ++ tailWord_2588868).sum := by decide
  have hdescent : baseEnd_2588868 < baseStart_2588868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2588868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2588881 : List Nat := [1, 2, 2, 1, 2, 2, 4, 1, 4, 1, 3]
def baseStart_2588881 : Nat := 118140960795 + 2588881 * 2 ^ 59
def prefixEnd_2588881 : Nat := 4983230072969 + 3 ^ 40 * 2588881 * 2
def baseEnd_2588881 : Nat := 1329340310292590724881459

theorem tailTrace_2588881 : CollatzResearch.WordTrace tailWord_2588881 prefixEnd_2588881 1329340310292590724881459 := by
  unfold tailWord_2588881
  simp only [CollatzResearch.WordTrace]
  refine ⟨94424247333933757518894497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62949498222622505012596331 94424247333933757518894497)
  ·
    refine ⟨70818185500450318139170873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94424247333933757518894497 70818185500450318139170873)
    ·
      refine ⟨53113639125337738604378155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70818185500450318139170873 53113639125337738604378155)
      ·
        refine ⟨79670458688006607906567233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53113639125337738604378155 79670458688006607906567233)
        ·
          refine ⟨59752844016004955929925425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79670458688006607906567233 59752844016004955929925425)
          ·
            refine ⟨44814633012003716947444069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59752844016004955929925425 44814633012003716947444069)
            ·
              refine ⟨8402743689750696927645763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44814633012003716947444069 8402743689750696927645763)
              ·
                refine ⟨12604115534626045391468645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8402743689750696927645763 12604115534626045391468645)
                ·
                  refine ⟨2363271662742383510900371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12604115534626045391468645 2363271662742383510900371)
                  ·
                    refine ⟨3544907494113575266350557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2363271662742383510900371 3544907494113575266350557)
                    ·
                      refine ⟨1329340310292590724881459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3544907494113575266350557 1329340310292590724881459)
                      ·
                        rfl

theorem cell23_2588881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 1, 4, 1, 3].length) (baseStart_2588881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2588881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2588881 prefixEnd_2588881 := by exact prefixLift 2588881
  have htrace : WordTrace (prefixWord ++ tailWord_2588881) baseStart_2588881 baseEnd_2588881 := by
    simpa [prefixWord, tailWord_2588881, baseEnd_2588881] using wordTrace_append hprefix tailTrace_2588881
  have hstable : (prefixWord ++ tailWord_2588881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2588881).length < 2 ^ (prefixWord ++ tailWord_2588881).sum := by decide
  have hdescent : baseEnd_2588881 < baseStart_2588881 := by decide
  rcases family_descends (prefixWord ++ tailWord_2588881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2588938 : List Nat := [3, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2]
def baseStart_2588938 : Nat := 118140960795 + 2588938 * 2 ^ 59
def prefixEnd_2588938 : Nat := 4983230072969 + 3 ^ 40 * 2588938 * 2
def baseEnd_2588938 : Nat := 1329369578689897001868697

theorem tailTrace_2588938 : CollatzResearch.WordTrace tailWord_2588938 prefixEnd_2588938 1329369578689897001868697 := by
  unfold tailWord_2588938
  simp only [CollatzResearch.WordTrace]
  refine ⟨23606581573681814063429867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62950884196484837502479645 23606581573681814063429867)
  ·
    refine ⟨35409872360522721095144801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23606581573681814063429867 35409872360522721095144801)
    ·
      refine ⟨26557404270392040821358601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35409872360522721095144801 26557404270392040821358601)
      ·
        refine ⟨19918053202794030616018951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26557404270392040821358601 19918053202794030616018951)
        ·
          refine ⟨29877079804191045924028427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19918053202794030616018951 29877079804191045924028427)
          ·
            refine ⟨44815619706286568886042641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29877079804191045924028427 44815619706286568886042641)
            ·
              refine ⟨33611714779714926664531981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44815619706286568886042641 33611714779714926664531981)
              ·
                refine ⟨12604393042393097499199493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33611714779714926664531981 12604393042393097499199493)
                ·
                  refine ⟨2363323695448705781099905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12604393042393097499199493 2363323695448705781099905)
                  ·
                    refine ⟨1772492771586529335824929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2363323695448705781099905 1772492771586529335824929)
                    ·
                      refine ⟨1329369578689897001868697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1772492771586529335824929 1329369578689897001868697)
                      ·
                        rfl

theorem cell23_2588938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2].length) (baseStart_2588938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2588938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2588938 prefixEnd_2588938 := by exact prefixLift 2588938
  have htrace : WordTrace (prefixWord ++ tailWord_2588938) baseStart_2588938 baseEnd_2588938 := by
    simpa [prefixWord, tailWord_2588938, baseEnd_2588938] using wordTrace_append hprefix tailTrace_2588938
  have hstable : (prefixWord ++ tailWord_2588938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2588938).length < 2 ^ (prefixWord ++ tailWord_2588938).sum := by decide
  have hdescent : baseEnd_2588938 < baseStart_2588938 := by decide
  rcases family_descends (prefixWord ++ tailWord_2588938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2588951 : List Nat := [1, 1, 3, 4, 1, 3, 1, 1, 2, 2, 4]
def baseStart_2588951 : Nat := 118140960795 + 2588951 * 2 ^ 59
def prefixEnd_2588951 : Nat := 4983230072969 + 3 ^ 40 * 2588951 * 2
def baseEnd_2588951 : Nat := 1329376253938405451006137

theorem tailTrace_2588951 : CollatzResearch.WordTrace tailWord_2588951 prefixEnd_2588951 1329376253938405451006137 := by
  unfold tailWord_2588951
  simp only [CollatzResearch.WordTrace]
  refine ⟨94426800443680159473942707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62951200295786772982628471 94426800443680159473942707)
  ·
    refine ⟨141640200665520239210914061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94426800443680159473942707 141640200665520239210914061)
    ·
      refine ⟨53115075249570089704092773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141640200665520239210914061 53115075249570089704092773)
      ·
        refine ⟨9959076609294391819517395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53115075249570089704092773 9959076609294391819517395)
        ·
          refine ⟨14938614913941587729276093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9959076609294391819517395 14938614913941587729276093)
          ·
            refine ⟨5601980592728095398478535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14938614913941587729276093 5601980592728095398478535)
            ·
              refine ⟨8402970889092143097717803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5601980592728095398478535 8402970889092143097717803)
              ·
                refine ⟨12604456333638214646576705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8402970889092143097717803 12604456333638214646576705)
                ·
                  refine ⟨9453342250228660984932529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12604456333638214646576705 9453342250228660984932529)
                  ·
                    refine ⟨7090006687671495738699397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9453342250228660984932529 7090006687671495738699397)
                    ·
                      refine ⟨1329376253938405451006137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7090006687671495738699397 1329376253938405451006137)
                      ·
                        rfl

theorem cell23_2588951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_2588951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2588951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2588951 prefixEnd_2588951 := by exact prefixLift 2588951
  have htrace : WordTrace (prefixWord ++ tailWord_2588951) baseStart_2588951 baseEnd_2588951 := by
    simpa [prefixWord, tailWord_2588951, baseEnd_2588951] using wordTrace_append hprefix tailTrace_2588951
  have hstable : (prefixWord ++ tailWord_2588951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2588951).length < 2 ^ (prefixWord ++ tailWord_2588951).sum := by decide
  have hdescent : baseEnd_2588951 < baseStart_2588951 := by decide
  rcases family_descends (prefixWord ++ tailWord_2588951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2588984 : List Nat := [2, 1, 2, 1, 3, 1, 2, 1, 3, 2, 5]
def baseStart_2588984 : Nat := 118140960795 + 2588984 * 2 ^ 59
def prefixEnd_2588984 : Nat := 4983230072969 + 3 ^ 40 * 2588984 * 2
def baseEnd_2588984 : Nat := 1329393198800003821893485

theorem tailTrace_2588984 : CollatzResearch.WordTrace tailWord_2588984 prefixEnd_2588984 1329393198800003821893485 := by
  unfold tailWord_2588984
  simp only [CollatzResearch.WordTrace]
  refine ⟨47214002026280303054947003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62952002701707070739929337 47214002026280303054947003)
  ·
    refine ⟨70821003039420454582420505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47214002026280303054947003 70821003039420454582420505)
    ·
      refine ⟨53115752279565340936815379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70821003039420454582420505 53115752279565340936815379)
      ·
        refine ⟨79673628419348011405223069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53115752279565340936815379 79673628419348011405223069)
        ·
          refine ⟨29877610657255504276958651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79673628419348011405223069 29877610657255504276958651)
          ·
            refine ⟨44816415985883256415437977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29877610657255504276958651 44816415985883256415437977)
            ·
              refine ⟨33612311989412442311578483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44816415985883256415437977 33612311989412442311578483)
              ·
                refine ⟨50418467984118663467367725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33612311989412442311578483 50418467984118663467367725)
                ·
                  refine ⟨18906925494044498800262897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50418467984118663467367725 18906925494044498800262897)
                  ·
                    refine ⟨14180194120533374100197173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18906925494044498800262897 14180194120533374100197173)
                    ·
                      refine ⟨1329393198800003821893485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14180194120533374100197173 1329393198800003821893485)
                      ·
                        rfl

theorem cell23_2588984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 3, 2, 5].length) (baseStart_2588984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2588984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2588984 prefixEnd_2588984 := by exact prefixLift 2588984
  have htrace : WordTrace (prefixWord ++ tailWord_2588984) baseStart_2588984 baseEnd_2588984 := by
    simpa [prefixWord, tailWord_2588984, baseEnd_2588984] using wordTrace_append hprefix tailTrace_2588984
  have hstable : (prefixWord ++ tailWord_2588984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2588984).length < 2 ^ (prefixWord ++ tailWord_2588984).sum := by decide
  have hdescent : baseEnd_2588984 < baseStart_2588984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2588984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2589011 : List Nat := [1, 1, 1, 2, 1, 1, 4, 3, 1, 6, 2]
def baseStart_2589011 : Nat := 118140960795 + 2589011 * 2 ^ 59
def prefixEnd_2589011 : Nat := 4983230072969 + 3 ^ 40 * 2589011 * 2
def baseEnd_2589011 : Nat := 1329407062777675216255861

theorem tailTrace_2589011 : CollatzResearch.WordTrace tailWord_2589011 prefixEnd_2589011 1329407062777675216255861 := by
  unfold tailWord_2589011
  simp only [CollatzResearch.WordTrace]
  refine ⟨94428988823462789721126887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62952659215641859814084591 94428988823462789721126887)
  ·
    refine ⟨141643483235194184581690331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94428988823462789721126887 141643483235194184581690331)
    ·
      refine ⟨212465224852791276872535497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141643483235194184581690331 212465224852791276872535497)
      ·
        refine ⟨159348918639593457654401623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212465224852791276872535497 159348918639593457654401623)
        ·
          refine ⟨239023377959390186481602435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159348918639593457654401623 239023377959390186481602435)
          ·
            refine ⟨358535066939085279722403653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 239023377959390186481602435 358535066939085279722403653)
            ·
              refine ⟨67225325051078489947950685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 358535066939085279722403653 67225325051078489947950685)
              ·
                refine ⟨25209496894154433730481507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67225325051078489947950685 25209496894154433730481507)
                ·
                  refine ⟨37814245341231650595722261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25209496894154433730481507 37814245341231650595722261)
                  ·
                    refine ⟨1772542750370233621674481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 37814245341231650595722261 1772542750370233621674481)
                    ·
                      refine ⟨1329407062777675216255861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1772542750370233621674481 1329407062777675216255861)
                      ·
                        rfl

theorem cell23_2589011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 6, 2].length) (baseStart_2589011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2589011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2589011 prefixEnd_2589011 := by exact prefixLift 2589011
  have htrace : WordTrace (prefixWord ++ tailWord_2589011) baseStart_2589011 baseEnd_2589011 := by
    simpa [prefixWord, tailWord_2589011, baseEnd_2589011] using wordTrace_append hprefix tailTrace_2589011
  have hstable : (prefixWord ++ tailWord_2589011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2589011).length < 2 ^ (prefixWord ++ tailWord_2589011).sum := by decide
  have hdescent : baseEnd_2589011 < baseStart_2589011 := by decide
  rcases family_descends (prefixWord ++ tailWord_2589011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2589068 : List Nat := [2, 2, 1, 2, 1, 4, 4, 1, 6]
def baseStart_2589068 : Nat := 118140960795 + 2589068 * 2 ^ 59
def prefixEnd_2589068 : Nat := 4983230072969 + 3 ^ 40 * 2589068 * 2
def baseEnd_2589068 : Nat := 147715147908331277027011

theorem tailTrace_2589068 : CollatzResearch.WordTrace tailWord_2589068 prefixEnd_2589068 147715147908331277027011 := by
  unfold tailWord_2589068
  simp only [CollatzResearch.WordTrace]
  refine ⟨47215533892128144227975929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62954045189504192303967905 47215533892128144227975929)
  ·
    refine ⟨35411650419096108170981947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47215533892128144227975929 35411650419096108170981947)
    ·
      refine ⟨53117475628644162256472921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35411650419096108170981947 53117475628644162256472921)
      ·
        refine ⟨39838106721483121692354691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53117475628644162256472921 39838106721483121692354691)
        ·
          refine ⟨59757160082224682538532037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39838106721483121692354691 59757160082224682538532037)
          ·
            refine ⟨11204467515417127975974757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59757160082224682538532037 11204467515417127975974757)
            ·
              refine ⟨2100837659140711495495267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11204467515417127975974757 2100837659140711495495267)
              ·
                refine ⟨3151256488711067243242901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2100837659140711495495267 3151256488711067243242901)
                ·
                  refine ⟨147715147908331277027011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3151256488711067243242901 147715147908331277027011)
                  ·
                    rfl

theorem cell23_2589068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 4, 1, 6].length) (baseStart_2589068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2589068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2589068 prefixEnd_2589068 := by exact prefixLift 2589068
  have htrace : WordTrace (prefixWord ++ tailWord_2589068) baseStart_2589068 baseEnd_2589068 := by
    simpa [prefixWord, tailWord_2589068, baseEnd_2589068] using wordTrace_append hprefix tailTrace_2589068
  have hstable : (prefixWord ++ tailWord_2589068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2589068).length < 2 ^ (prefixWord ++ tailWord_2589068).sum := by decide
  have hdescent : baseEnd_2589068 < baseStart_2589068 := by decide
  rcases family_descends (prefixWord ++ tailWord_2589068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2589081 : List Nat := [1, 2, 1, 2, 1, 4, 3, 1, 3, 5]
def baseStart_2589081 : Nat := 118140960795 + 2589081 * 2 ^ 59
def prefixEnd_2589081 : Nat := 4983230072969 + 3 ^ 40 * 2589081 * 2
def baseEnd_2589081 : Nat := 443147668807829980793513

theorem tailTrace_2589081 : CollatzResearch.WordTrace tailWord_2589081 prefixEnd_2589081 443147668807829980793513 := by
  unfold tailWord_2589081
  simp only [CollatzResearch.WordTrace]
  refine ⟨94431541933209191676175097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62954361288806127784116731 94431541933209191676175097)
  ·
    refine ⟨70823656449906893757131323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94431541933209191676175097 70823656449906893757131323)
    ·
      refine ⟨106235484674860340635696985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70823656449906893757131323 106235484674860340635696985)
      ·
        refine ⟨79676613506145255476772739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106235484674860340635696985 79676613506145255476772739)
        ·
          refine ⟨119514920259217883215159109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79676613506145255476772739 119514920259217883215159109)
          ·
            refine ⟨22409047548603353102842333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 119514920259217883215159109 22409047548603353102842333)
            ·
              refine ⟨8403392830726257413565875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22409047548603353102842333 8403392830726257413565875)
              ·
                refine ⟨12605089246089386120348813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8403392830726257413565875 12605089246089386120348813)
                ·
                  refine ⟨4726908467283519795130805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12605089246089386120348813 4726908467283519795130805)
                  ·
                    refine ⟨443147668807829980793513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4726908467283519795130805 443147668807829980793513)
                    ·
                      rfl

theorem cell23_2589081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 1, 3, 5].length) (baseStart_2589081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2589081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2589081 prefixEnd_2589081 := by exact prefixLift 2589081
  have htrace : WordTrace (prefixWord ++ tailWord_2589081) baseStart_2589081 baseEnd_2589081 := by
    simpa [prefixWord, tailWord_2589081, baseEnd_2589081] using wordTrace_append hprefix tailTrace_2589081
  have hstable : (prefixWord ++ tailWord_2589081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2589081).length < 2 ^ (prefixWord ++ tailWord_2589081).sum := by decide
  have hdescent : baseEnd_2589081 < baseStart_2589081 := by decide
  rcases family_descends (prefixWord ++ tailWord_2589081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2589105 : List Nat := [1, 2, 2, 4, 1, 2, 2, 2, 2, 3, 2]
def baseStart_2589105 : Nat := 118140960795 + 2589105 * 2 ^ 59
def prefixEnd_2589105 : Nat := 4983230072969 + 3 ^ 40 * 2589105 * 2
def baseEnd_2589105 : Nat := 1329455329959197848480429

theorem tailTrace_2589105 : CollatzResearch.WordTrace tailWord_2589105 prefixEnd_2589105 1329455329959197848480429 := by
  unfold tailWord_2589105
  simp only [CollatzResearch.WordTrace]
  refine ⟨94432417285122243775048769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62954944856748162516699179 94432417285122243775048769)
  ·
    refine ⟨70824312963841682831286577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94432417285122243775048769 70824312963841682831286577)
    ·
      refine ⟨53118234722881262123464933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70824312963841682831286577 53118234722881262123464933)
      ·
        refine ⟨9959669010540236648149675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53118234722881262123464933 9959669010540236648149675)
        ·
          refine ⟨14939503515810354972224513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9959669010540236648149675 14939503515810354972224513)
          ·
            refine ⟨11204627636857766229168385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14939503515810354972224513 11204627636857766229168385)
            ·
              refine ⟨8403470727643324671876289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11204627636857766229168385 8403470727643324671876289)
              ·
                refine ⟨6302603045732493503907217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8403470727643324671876289 6302603045732493503907217)
                ·
                  refine ⟨4726952284299370127930413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6302603045732493503907217 4726952284299370127930413)
                  ·
                    refine ⟨1772607106612263797973905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4726952284299370127930413 1772607106612263797973905)
                    ·
                      refine ⟨1329455329959197848480429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1772607106612263797973905 1329455329959197848480429)
                      ·
                        rfl

theorem cell23_2589105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 2, 2, 3, 2].length) (baseStart_2589105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2589105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2589105 prefixEnd_2589105 := by exact prefixLift 2589105
  have htrace : WordTrace (prefixWord ++ tailWord_2589105) baseStart_2589105 baseEnd_2589105 := by
    simpa [prefixWord, tailWord_2589105, baseEnd_2589105] using wordTrace_append hprefix tailTrace_2589105
  have hstable : (prefixWord ++ tailWord_2589105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2589105).length < 2 ^ (prefixWord ++ tailWord_2589105).sum := by decide
  have hdescent : baseEnd_2589105 < baseStart_2589105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2589105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2589118 : List Nat := [4, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4]
def baseStart_2589118 : Nat := 118140960795 + 2589118 * 2 ^ 59
def prefixEnd_2589118 : Nat := 4983230072969 + 3 ^ 40 * 2589118 * 2
def baseEnd_2589118 : Nat := 1329462005207706297617869

theorem tailTrace_2589118 : CollatzResearch.WordTrace tailWord_2589118 prefixEnd_2589118 1329462005207706297617869 := by
  unfold tailWord_2589118
  simp only [CollatzResearch.WordTrace]
  refine ⟨11804111429259393374409001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62955260956050097996848005 11804111429259393374409001)
  ·
    refine ⟨8853083571944545030806751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11804111429259393374409001 8853083571944545030806751)
    ·
      refine ⟨13279625357916817546210127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8853083571944545030806751 13279625357916817546210127)
      ·
        refine ⟨19919438036875226319315191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13279625357916817546210127 19919438036875226319315191)
        ·
          refine ⟨29879157055312839478972787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19919438036875226319315191 29879157055312839478972787)
          ·
            refine ⟨44818735582969259218459181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29879157055312839478972787 44818735582969259218459181)
            ·
              refine ⟨16807025843613472206922193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44818735582969259218459181 16807025843613472206922193)
              ·
                refine ⟨12605269382710104155191645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16807025843613472206922193 12605269382710104155191645)
                ·
                  refine ⟨4726976018516289058196867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12605269382710104155191645 4726976018516289058196867)
                  ·
                    refine ⟨7090464027774433587295301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4726976018516289058196867 7090464027774433587295301)
                    ·
                      refine ⟨1329462005207706297617869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7090464027774433587295301 1329462005207706297617869)
                      ·
                        rfl

theorem cell23_2589118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4].length) (baseStart_2589118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2589118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2589118 prefixEnd_2589118 := by exact prefixLift 2589118
  have htrace : WordTrace (prefixWord ++ tailWord_2589118) baseStart_2589118 baseEnd_2589118 := by
    simpa [prefixWord, tailWord_2589118, baseEnd_2589118] using wordTrace_append hprefix tailTrace_2589118
  have hstable : (prefixWord ++ tailWord_2589118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2589118).length < 2 ^ (prefixWord ++ tailWord_2589118).sum := by decide
  have hdescent : baseEnd_2589118 < baseStart_2589118 := by decide
  rcases family_descends (prefixWord ++ tailWord_2589118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2589128 : List Nat := [2, 1, 3, 1, 3, 3, 2, 1, 1, 6]
def baseStart_2589128 : Nat := 118140960795 + 2589128 * 2 ^ 59
def prefixEnd_2589128 : Nat := 4983230072969 + 3 ^ 40 * 2589128 * 2
def baseEnd_2589128 : Nat := 443155713338083752830941

theorem tailTrace_2589128 : CollatzResearch.WordTrace tailWord_2589128 prefixEnd_2589128 443155713338083752830941 := by
  unfold tailWord_2589128
  simp only [CollatzResearch.WordTrace]
  refine ⟨47216628082019459351568019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62955504109359279135424025 47216628082019459351568019)
  ·
    refine ⟨70824942123029189027352029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47216628082019459351568019 70824942123029189027352029)
    ·
      refine ⟨26559353296135945885257011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70824942123029189027352029 26559353296135945885257011)
      ·
        refine ⟨39839029944203918827885517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26559353296135945885257011 39839029944203918827885517)
        ·
          refine ⟨14939636229076469560457069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39839029944203918827885517 14939636229076469560457069)
          ·
            refine ⟨5602363585903676085171401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14939636229076469560457069 5602363585903676085171401)
            ·
              refine ⟨4201772689427757063878551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5602363585903676085171401 4201772689427757063878551)
              ·
                refine ⟨6302659034141635595817827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4201772689427757063878551 6302659034141635595817827)
                ·
                  refine ⟨9453988551212453393726741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6302659034141635595817827 9453988551212453393726741)
                  ·
                    refine ⟨443155713338083752830941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9453988551212453393726741 443155713338083752830941)
                    ·
                      rfl

theorem cell23_2589128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 1, 1, 6].length) (baseStart_2589128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2589128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2589128 prefixEnd_2589128 := by exact prefixLift 2589128
  have htrace : WordTrace (prefixWord ++ tailWord_2589128) baseStart_2589128 baseEnd_2589128 := by
    simpa [prefixWord, tailWord_2589128, baseEnd_2589128] using wordTrace_append hprefix tailTrace_2589128
  have hstable : (prefixWord ++ tailWord_2589128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2589128).length < 2 ^ (prefixWord ++ tailWord_2589128).sum := by decide
  have hdescent : baseEnd_2589128 < baseStart_2589128 := by decide
  rcases family_descends (prefixWord ++ tailWord_2589128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2589162 : List Nat := [3, 1, 3, 1, 3, 3, 1, 2, 2, 4]
def baseStart_2589162 : Nat := 118140960795 + 2589162 * 2 ^ 59
def prefixEnd_2589162 : Nat := 4983230072969 + 3 ^ 40 * 2589162 * 2
def baseEnd_2589162 : Nat := 443161532785501375155889

theorem tailTrace_2589162 : CollatzResearch.WordTrace tailWord_2589162 prefixEnd_2589162 443161532785501375155889 := by
  unfold tailWord_2589162
  simp only [CollatzResearch.WordTrace]
  refine ⟨23608624061478935627468435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62956330830610495006582493 23608624061478935627468435)
  ·
    refine ⟨35412936092218403441202653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23608624061478935627468435 35412936092218403441202653)
    ·
      refine ⟨13279851034581901290450995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35412936092218403441202653 13279851034581901290450995)
      ·
        refine ⟨19919776551872851935676493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13279851034581901290450995 19919776551872851935676493)
        ·
          refine ⟨7469916206952319475878685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19919776551872851935676493 7469916206952319475878685)
          ·
            refine ⟨2801218577607119803454507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7469916206952319475878685 2801218577607119803454507)
            ·
              refine ⟨4201827866410679705181761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2801218577607119803454507 4201827866410679705181761)
              ·
                refine ⟨3151370899808009778886321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4201827866410679705181761 3151370899808009778886321)
                ·
                  refine ⟨2363528174856007334164741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3151370899808009778886321 2363528174856007334164741)
                  ·
                    refine ⟨443161532785501375155889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2363528174856007334164741 443161532785501375155889)
                    ·
                      rfl

theorem cell23_2589162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 2, 2, 4].length) (baseStart_2589162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2589162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2589162 prefixEnd_2589162 := by exact prefixLift 2589162
  have htrace : WordTrace (prefixWord ++ tailWord_2589162) baseStart_2589162 baseEnd_2589162 := by
    simpa [prefixWord, tailWord_2589162, baseEnd_2589162] using wordTrace_append hprefix tailTrace_2589162
  have hstable : (prefixWord ++ tailWord_2589162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2589162).length < 2 ^ (prefixWord ++ tailWord_2589162).sum := by decide
  have hdescent : baseEnd_2589162 < baseStart_2589162 := by decide
  rcases family_descends (prefixWord ++ tailWord_2589162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2589178 : List Nat := [3, 1, 1, 1, 1, 2, 2, 1, 2, 7, 2]
def baseStart_2589178 : Nat := 118140960795 + 2589178 * 2 ^ 59
def prefixEnd_2589178 : Nat := 4983230072969 + 3 ^ 40 * 2589178 * 2
def baseEnd_2589178 : Nat := 1329492814046976062867593

theorem tailTrace_2589178 : CollatzResearch.WordTrace tailWord_2589178 prefixEnd_2589178 1329492814046976062867593 := by
  unfold tailWord_2589178
  simp only [CollatzResearch.WordTrace]
  refine ⟨23608769953464444310614047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62956719875905184828304125 23608769953464444310614047)
  ·
    refine ⟨35413154930196666465921071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23608769953464444310614047 35413154930196666465921071)
    ·
      refine ⟨53119732395294999698881607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35413154930196666465921071 53119732395294999698881607)
      ·
        refine ⟨79679598592942499548322411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53119732395294999698881607 79679598592942499548322411)
        ·
          refine ⟨119519397889413749322483617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79679598592942499548322411 119519397889413749322483617)
          ·
            refine ⟨89639548417060311991862713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119519397889413749322483617 89639548417060311991862713)
            ·
              refine ⟨67229661312795233993897035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89639548417060311991862713 67229661312795233993897035)
              ·
                refine ⟨100844491969192850990845553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67229661312795233993897035 100844491969192850990845553)
                ·
                  refine ⟨75633368976894638243134165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 100844491969192850990845553 75633368976894638243134165)
                  ·
                    refine ⟨1772657085395968083823457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 75633368976894638243134165 1772657085395968083823457)
                    ·
                      refine ⟨1329492814046976062867593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1772657085395968083823457 1329492814046976062867593)
                      ·
                        rfl

theorem cell23_2589178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 2, 7, 2].length) (baseStart_2589178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2589178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2589178 prefixEnd_2589178 := by exact prefixLift 2589178
  have htrace : WordTrace (prefixWord ++ tailWord_2589178) baseStart_2589178 baseEnd_2589178 := by
    simpa [prefixWord, tailWord_2589178, baseEnd_2589178] using wordTrace_append hprefix tailTrace_2589178
  have hstable : (prefixWord ++ tailWord_2589178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2589178).length < 2 ^ (prefixWord ++ tailWord_2589178).sum := by decide
  have hdescent : baseEnd_2589178 < baseStart_2589178 := by decide
  rcases family_descends (prefixWord ++ tailWord_2589178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2589185 : List Nat := [1, 2, 4, 1, 3, 1, 3, 1, 1, 3, 3]
def baseStart_2589185 : Nat := 118140960795 + 2589185 * 2 ^ 59
def prefixEnd_2589185 : Nat := 4983230072969 + 3 ^ 40 * 2589185 * 2
def baseEnd_2589185 : Nat := 1329496408411557535480061

theorem tailTrace_2589185 : CollatzResearch.WordTrace tailWord_2589185 prefixEnd_2589185 1329496408411557535480061 := by
  unfold tailWord_2589185
  simp only [CollatzResearch.WordTrace]
  refine ⟨94435335124832417437961009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62956890083221611625307339 94435335124832417437961009)
  ·
    refine ⟨70826501343624313078470757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94435335124832417437961009 70826501343624313078470757)
    ·
      refine ⟨13279969001929558702213267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70826501343624313078470757 13279969001929558702213267)
      ·
        refine ⟨19919953502894338053319901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13279969001929558702213267 19919953502894338053319901)
        ·
          refine ⟨7469982563585376769994963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19919953502894338053319901 7469982563585376769994963)
          ·
            refine ⟨11204973845378065154992445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7469982563585376769994963 11204973845378065154992445)
            ·
              refine ⟨4201865192016774433122167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11204973845378065154992445 4201865192016774433122167)
              ·
                refine ⟨6302797788025161649683251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4201865192016774433122167 6302797788025161649683251)
                ·
                  refine ⟨9454196682037742474524877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6302797788025161649683251 9454196682037742474524877)
                  ·
                    refine ⟨3545323755764153427946829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9454196682037742474524877 3545323755764153427946829)
                    ·
                      refine ⟨1329496408411557535480061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3545323755764153427946829 1329496408411557535480061)
                      ·
                        rfl

theorem cell23_2589185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 1, 1, 3, 3].length) (baseStart_2589185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2589185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2589185 prefixEnd_2589185 := by exact prefixLift 2589185
  have htrace : WordTrace (prefixWord ++ tailWord_2589185) baseStart_2589185 baseEnd_2589185 := by
    simpa [prefixWord, tailWord_2589185, baseEnd_2589185] using wordTrace_append hprefix tailTrace_2589185
  have hstable : (prefixWord ++ tailWord_2589185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2589185).length < 2 ^ (prefixWord ++ tailWord_2589185).sum := by decide
  have hdescent : baseEnd_2589185 < baseStart_2589185 := by decide
  rcases family_descends (prefixWord ++ tailWord_2589185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2589198 : List Nat := [4, 1, 1, 2, 3, 1, 1, 1, 2, 2, 5]
def baseStart_2589198 : Nat := 118140960795 + 2589198 * 2 ^ 59
def prefixEnd_2589198 : Nat := 4983230072969 + 3 ^ 40 * 2589198 * 2
def baseEnd_2589198 : Nat := 1329503083660065984617501

theorem tailTrace_2589198 : CollatzResearch.WordTrace tailWord_2589198 prefixEnd_2589198 1329503083660065984617501 := by
  unfold tailWord_2589198
  simp only [CollatzResearch.WordTrace]
  refine ⟨11804476159223165082273031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62957206182523547105456165 11804476159223165082273031)
  ·
    refine ⟨17706714238834747623409547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11804476159223165082273031 17706714238834747623409547)
    ·
      refine ⟨26560071358252121435114321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17706714238834747623409547 26560071358252121435114321)
      ·
        refine ⟨19920053518689091076335741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26560071358252121435114321 19920053518689091076335741)
        ·
          refine ⟨7470020069508409153625903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19920053518689091076335741 7470020069508409153625903)
          ·
            refine ⟨11205030104262613730438855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7470020069508409153625903 11205030104262613730438855)
            ·
              refine ⟨16807545156393920595658283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11205030104262613730438855 16807545156393920595658283)
              ·
                refine ⟨25211317734590880893487425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16807545156393920595658283 25211317734590880893487425)
                ·
                  refine ⟨18908488300943160670115569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25211317734590880893487425 18908488300943160670115569)
                  ·
                    refine ⟨14181366225707370502586677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18908488300943160670115569 14181366225707370502586677)
                    ·
                      refine ⟨1329503083660065984617501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14181366225707370502586677 1329503083660065984617501)
                      ·
                        rfl

theorem cell23_2589198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_2589198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2589198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2589198 prefixEnd_2589198 := by exact prefixLift 2589198
  have htrace : WordTrace (prefixWord ++ tailWord_2589198) baseStart_2589198 baseEnd_2589198 := by
    simpa [prefixWord, tailWord_2589198, baseEnd_2589198] using wordTrace_append hprefix tailTrace_2589198
  have hstable : (prefixWord ++ tailWord_2589198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2589198).length < 2 ^ (prefixWord ++ tailWord_2589198).sum := by decide
  have hdescent : baseEnd_2589198 < baseStart_2589198 := by decide
  rcases family_descends (prefixWord ++ tailWord_2589198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2589201 : List Nat := [1, 2, 2, 1, 1, 2, 2, 2, 4, 6]
def baseStart_2589201 : Nat := 118140960795 + 2589201 * 2 ^ 59
def prefixEnd_2589201 : Nat := 4983230072969 + 3 ^ 40 * 2589201 * 2
def baseEnd_2589201 : Nat := 443168208034009824293329

theorem tailTrace_2589201 : CollatzResearch.WordTrace tailWord_2589201 prefixEnd_2589201 443168208034009824293329 := by
  unfold tailWord_2589201
  simp only [CollatzResearch.WordTrace]
  refine ⟨94435918692774452170543457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62957279128516301447028971 94435918692774452170543457)
  ·
    refine ⟨70826939019580839127907593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94435918692774452170543457 70826939019580839127907593)
    ·
      refine ⟨53120204264685629345930695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70826939019580839127907593 53120204264685629345930695)
      ·
        refine ⟨79680306397028444018896043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53120204264685629345930695 79680306397028444018896043)
        ·
          refine ⟨119520459595542666028344065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79680306397028444018896043 119520459595542666028344065)
          ·
            refine ⟨89640344696656999521258049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119520459595542666028344065 89640344696656999521258049)
            ·
              refine ⟨67230258522492749640943537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89640344696656999521258049 67230258522492749640943537)
              ·
                refine ⟨50422693891869562230707653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67230258522492749640943537 50422693891869562230707653)
                ·
                  refine ⟨9454255104725542918257685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50422693891869562230707653 9454255104725542918257685)
                  ·
                    refine ⟨443168208034009824293329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9454255104725542918257685 443168208034009824293329)
                    ·
                      rfl

theorem cell23_2589201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 6].length) (baseStart_2589201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2589201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2589201 prefixEnd_2589201 := by exact prefixLift 2589201
  have htrace : WordTrace (prefixWord ++ tailWord_2589201) baseStart_2589201 baseEnd_2589201 := by
    simpa [prefixWord, tailWord_2589201, baseEnd_2589201] using wordTrace_append hprefix tailTrace_2589201
  have hstable : (prefixWord ++ tailWord_2589201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2589201).length < 2 ^ (prefixWord ++ tailWord_2589201).sum := by decide
  have hdescent : baseEnd_2589201 < baseStart_2589201 := by decide
  rcases family_descends (prefixWord ++ tailWord_2589201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2589212 : List Nat := [2, 2, 3, 1, 2, 2, 2, 3, 1, 3, 2]
def baseStart_2589212 : Nat := 118140960795 + 2589212 * 2 ^ 59
def prefixEnd_2589212 : Nat := 4983230072969 + 3 ^ 40 * 2589212 * 2
def baseEnd_2589212 : Nat := 1329510272389228929842437

theorem tailTrace_2589212 : CollatzResearch.WordTrace tailWord_2589212 prefixEnd_2589212 1329510272389228929842437 := by
  unfold tailWord_2589212
  simp only [CollatzResearch.WordTrace]
  refine ⟨47218159947867300524596945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62957546597156400699462593 47218159947867300524596945)
  ·
    refine ⟨35413619960900475393447709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47218159947867300524596945 35413619960900475393447709)
    ·
      refine ⟨13280107485337678272542891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35413619960900475393447709 13280107485337678272542891)
      ·
        refine ⟨19920161228006517408814337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13280107485337678272542891 19920161228006517408814337)
        ·
          refine ⟨14940120921004888056610753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19920161228006517408814337 14940120921004888056610753)
          ·
            refine ⟨11205090690753666042458065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14940120921004888056610753 11205090690753666042458065)
            ·
              refine ⟨8403818018065249531843549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11205090690753666042458065 8403818018065249531843549)
              ·
                refine ⟨3151431756774468574441331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8403818018065249531843549 3151431756774468574441331)
                ·
                  refine ⟨4727147635161702861661997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3151431756774468574441331 4727147635161702861661997)
                  ·
                    refine ⟨1772680363185638573123249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4727147635161702861661997 1772680363185638573123249)
                    ·
                      refine ⟨1329510272389228929842437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1772680363185638573123249 1329510272389228929842437)
                      ·
                        rfl

theorem cell23_2589212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 3, 1, 3, 2].length) (baseStart_2589212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2589212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2589212 prefixEnd_2589212 := by exact prefixLift 2589212
  have htrace : WordTrace (prefixWord ++ tailWord_2589212) baseStart_2589212 baseEnd_2589212 := by
    simpa [prefixWord, tailWord_2589212, baseEnd_2589212] using wordTrace_append hprefix tailTrace_2589212
  have hstable : (prefixWord ++ tailWord_2589212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2589212).length < 2 ^ (prefixWord ++ tailWord_2589212).sum := by decide
  have hdescent : baseEnd_2589212 < baseStart_2589212 := by decide
  rcases family_descends (prefixWord ++ tailWord_2589212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2589236 : List Nat := [2, 5, 1, 3, 1, 1, 1, 3, 2, 1, 3]
def baseStart_2589236 : Nat := 118140960795 + 2589236 * 2 ^ 59
def prefixEnd_2589236 : Nat := 4983230072969 + 3 ^ 40 * 2589236 * 2
def baseEnd_2589236 : Nat := 1329522595924936835942327

theorem tailTrace_2589236 : CollatzResearch.WordTrace tailWord_2589236 prefixEnd_2589236 1329522595924936835942327 := by
  unfold tailWord_2589236
  simp only [CollatzResearch.WordTrace]
  refine ⟨47218597623823826574033781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62958130165098435432045041 47218597623823826574033781)
  ·
    refine ⟨4426743527233483741315667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 47218597623823826574033781 4426743527233483741315667)
    ·
      refine ⟨6640115290850225611973501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4426743527233483741315667 6640115290850225611973501)
      ·
        refine ⟨2490043234068834604490063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6640115290850225611973501 2490043234068834604490063)
        ·
          refine ⟨3735064851103251906735095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2490043234068834604490063 3735064851103251906735095)
          ·
            refine ⟨5602597276654877860102643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3735064851103251906735095 5602597276654877860102643)
            ·
              refine ⟨8403895914982316790153965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5602597276654877860102643 8403895914982316790153965)
              ·
                refine ⟨3151460968118368796307737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8403895914982316790153965 3151460968118368796307737)
                ·
                  refine ⟨2363595726088776597230803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3151460968118368796307737 2363595726088776597230803)
                  ·
                    refine ⟨3545393589133164895846205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2363595726088776597230803 3545393589133164895846205)
                    ·
                      refine ⟨1329522595924936835942327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3545393589133164895846205 1329522595924936835942327)
                      ·
                        rfl

theorem cell23_2589236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_2589236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2589236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2589236 prefixEnd_2589236 := by exact prefixLift 2589236
  have htrace : WordTrace (prefixWord ++ tailWord_2589236) baseStart_2589236 baseEnd_2589236 := by
    simpa [prefixWord, tailWord_2589236, baseEnd_2589236] using wordTrace_append hprefix tailTrace_2589236
  have hstable : (prefixWord ++ tailWord_2589236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2589236).length < 2 ^ (prefixWord ++ tailWord_2589236).sum := by decide
  have hdescent : baseEnd_2589236 < baseStart_2589236 := by decide
  rcases family_descends (prefixWord ++ tailWord_2589236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2589251 : List Nat := [1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 8]
def baseStart_2589251 : Nat := 118140960795 + 2589251 * 2 ^ 59
def prefixEnd_2589251 : Nat := 4983230072969 + 3 ^ 40 * 2589251 * 2
def baseEnd_2589251 : Nat := 1329530298134754277254757

theorem tailTrace_2589251 : CollatzResearch.WordTrace tailWord_2589251 prefixEnd_2589251 1329530298134754277254757 := by
  unfold tailWord_2589251
  simp only [CollatzResearch.WordTrace]
  refine ⟨94437742342593310709863607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62958494895062207139909071 94437742342593310709863607)
  ·
    refine ⟨141656613513889966064795411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94437742342593310709863607 141656613513889966064795411)
    ·
      refine ⟨212484920270834949097193117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141656613513889966064795411 212484920270834949097193117)
      ·
        refine ⟨79681845101563105911447419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 212484920270834949097193117 79681845101563105911447419)
        ·
          refine ⟨119522767652344658867171129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79681845101563105911447419 119522767652344658867171129)
          ·
            refine ⟨89642075739258494150378347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119522767652344658867171129 89642075739258494150378347)
            ·
              refine ⟨134463113608887741225567521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89642075739258494150378347 134463113608887741225567521)
              ·
                refine ⟨100847335206665805919175641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 134463113608887741225567521 100847335206665805919175641)
                ·
                  refine ⟨75635501404999354439381731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 100847335206665805919175641 75635501404999354439381731)
                  ·
                    refine ⟨113453252107499031659072597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 75635501404999354439381731 113453252107499031659072597)
                    ·
                      refine ⟨1329530298134754277254757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 113453252107499031659072597 1329530298134754277254757)
                      ·
                        rfl

theorem cell23_2589251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 8].length) (baseStart_2589251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2589251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2589251 prefixEnd_2589251 := by exact prefixLift 2589251
  have htrace : WordTrace (prefixWord ++ tailWord_2589251) baseStart_2589251 baseEnd_2589251 := by
    simpa [prefixWord, tailWord_2589251, baseEnd_2589251] using wordTrace_append hprefix tailTrace_2589251
  have hstable : (prefixWord ++ tailWord_2589251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2589251).length < 2 ^ (prefixWord ++ tailWord_2589251).sum := by decide
  have hdescent : baseEnd_2589251 < baseStart_2589251 := by decide
  rcases family_descends (prefixWord ++ tailWord_2589251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2589276 : List Nat := [2, 2, 4, 1, 3, 1, 2, 2, 2, 2, 2]
def baseStart_2589276 : Nat := 118140960795 + 2589276 * 2 ^ 59
def prefixEnd_2589276 : Nat := 4983230072969 + 3 ^ 40 * 2589276 * 2
def baseEnd_2589276 : Nat := 1329543135151116679442143

theorem tailTrace_2589276 : CollatzResearch.WordTrace tailWord_2589276 prefixEnd_2589276 1329543135151116679442143 := by
  unfold tailWord_2589276
  simp only [CollatzResearch.WordTrace]
  refine ⟨47219327083751369989761841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62959102778335159986349121 47219327083751369989761841)
  ·
    refine ⟨35414495312813527492321381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47219327083751369989761841 35414495312813527492321381)
    ·
      refine ⟨6640217871152536404810259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35414495312813527492321381 6640217871152536404810259)
      ·
        refine ⟨9960326806728804607215389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6640217871152536404810259 9960326806728804607215389)
        ·
          refine ⟨3735122552523301727705771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9960326806728804607215389 3735122552523301727705771)
          ·
            refine ⟨5602683828784952591558657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3735122552523301727705771 5602683828784952591558657)
            ·
              refine ⟨4202012871588714443668993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5602683828784952591558657 4202012871588714443668993)
              ·
                refine ⟨3151509653691535832751745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4202012871588714443668993 3151509653691535832751745)
                ·
                  refine ⟨2363632240268651874563809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3151509653691535832751745 2363632240268651874563809)
                  ·
                    refine ⟨1772724180201488905922857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2363632240268651874563809 1772724180201488905922857)
                    ·
                      refine ⟨1329543135151116679442143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1772724180201488905922857 1329543135151116679442143)
                      ·
                        rfl

theorem cell23_2589276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 2, 2, 2, 2].length) (baseStart_2589276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2589276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2589276 prefixEnd_2589276 := by exact prefixLift 2589276
  have htrace : WordTrace (prefixWord ++ tailWord_2589276) baseStart_2589276 baseEnd_2589276 := by
    simpa [prefixWord, tailWord_2589276, baseEnd_2589276] using wordTrace_append hprefix tailTrace_2589276
  have hstable : (prefixWord ++ tailWord_2589276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2589276).length < 2 ^ (prefixWord ++ tailWord_2589276).sum := by decide
  have hdescent : baseEnd_2589276 < baseStart_2589276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2589276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2589315 : List Nat := [1, 1, 1, 3, 3, 1, 5, 1, 2, 1, 4]
def baseStart_2589315 : Nat := 118140960795 + 2589315 * 2 ^ 59
def prefixEnd_2589315 : Nat := 4983230072969 + 3 ^ 40 * 2589315 * 2
def baseEnd_2589315 : Nat := 1329563160896642026854463

theorem tailTrace_2589315 : CollatzResearch.WordTrace tailWord_2589315 prefixEnd_2589315 1329563160896642026854463 := by
  unfold tailWord_2589315
  simp only [CollatzResearch.WordTrace]
  refine ⟨94440076614361449640193399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62960051076240966426795599 94440076614361449640193399)
  ·
    refine ⟨141660114921542174460290099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94440076614361449640193399 141660114921542174460290099)
    ·
      refine ⟨212490172382313261690435149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141660114921542174460290099 212490172382313261690435149)
      ·
        refine ⟨79683814643367473133913181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 212490172382313261690435149 79683814643367473133913181)
        ·
          refine ⟨29881430491262802425217443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79683814643367473133913181 29881430491262802425217443)
          ·
            refine ⟨44822145736894203637826165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29881430491262802425217443 44822145736894203637826165)
            ·
              refine ⟨4202076162833831591046203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44822145736894203637826165 4202076162833831591046203)
              ·
                refine ⟨6303114244250747386569305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4202076162833831591046203 6303114244250747386569305)
                ·
                  refine ⟨4727335683188060539926979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6303114244250747386569305 4727335683188060539926979)
                  ·
                    refine ⟨7091003524782090809890469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4727335683188060539926979 7091003524782090809890469)
                    ·
                      refine ⟨1329563160896642026854463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7091003524782090809890469 1329563160896642026854463)
                      ·
                        rfl

theorem cell23_2589315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 1, 2, 1, 4].length) (baseStart_2589315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2589315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2589315 prefixEnd_2589315 := by exact prefixLift 2589315
  have htrace : WordTrace (prefixWord ++ tailWord_2589315) baseStart_2589315 baseEnd_2589315 := by
    simpa [prefixWord, tailWord_2589315, baseEnd_2589315] using wordTrace_append hprefix tailTrace_2589315
  have hstable : (prefixWord ++ tailWord_2589315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2589315).length < 2 ^ (prefixWord ++ tailWord_2589315).sum := by decide
  have hdescent : baseEnd_2589315 < baseStart_2589315 := by decide
  rcases family_descends (prefixWord ++ tailWord_2589315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2589335 : List Nat := [1, 1, 3, 3, 2, 1, 2, 1, 4, 2, 3]
def baseStart_2589335 : Nat := 118140960795 + 2589335 * 2 ^ 59
def prefixEnd_2589335 : Nat := 4983230072969 + 3 ^ 40 * 2589335 * 2
def baseEnd_2589335 : Nat := 1329573430509731948604371

theorem tailTrace_2589335 : CollatzResearch.WordTrace tailWord_2589335 prefixEnd_2589335 1329573430509731948604371 := by
  unfold tailWord_2589335
  simp only [CollatzResearch.WordTrace]
  refine ⟨94440806074288993055921459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62960537382859328703947639 94440806074288993055921459)
  ·
    refine ⟨141661209111433489583882189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94440806074288993055921459 141661209111433489583882189)
    ·
      refine ⟨53122953416787558593955821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141661209111433489583882189 53122953416787558593955821)
      ·
        refine ⟨19921107531295334472733433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53122953416787558593955821 19921107531295334472733433)
        ·
          refine ⟨14940830648471500854550075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19921107531295334472733433 14940830648471500854550075)
          ·
            refine ⟨22411245972707251281825113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14940830648471500854550075 22411245972707251281825113)
            ·
              refine ⟨16808434479530438461368835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22411245972707251281825113 16808434479530438461368835)
              ·
                refine ⟨25212651719295657692053253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16808434479530438461368835 25212651719295657692053253)
                ·
                  refine ⟨4727372197367935817259985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25212651719295657692053253 4727372197367935817259985)
                  ·
                    refine ⟨3545529148025951862944989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4727372197367935817259985 3545529148025951862944989)
                    ·
                      refine ⟨1329573430509731948604371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3545529148025951862944989 1329573430509731948604371)
                      ·
                        rfl

theorem cell23_2589335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 4, 2, 3].length) (baseStart_2589335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2589335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2589335 prefixEnd_2589335 := by exact prefixLift 2589335
  have htrace : WordTrace (prefixWord ++ tailWord_2589335) baseStart_2589335 baseEnd_2589335 := by
    simpa [prefixWord, tailWord_2589335, baseEnd_2589335] using wordTrace_append hprefix tailTrace_2589335
  have hstable : (prefixWord ++ tailWord_2589335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2589335).length < 2 ^ (prefixWord ++ tailWord_2589335).sum := by decide
  have hdescent : baseEnd_2589335 < baseStart_2589335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2589335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2589399 : List Nat := [1, 1, 3, 2, 1, 6, 1, 1, 3, 1, 3]
def baseStart_2589399 : Nat := 118140960795 + 2589399 * 2 ^ 59
def prefixEnd_2589399 : Nat := 4983230072969 + 3 ^ 40 * 2589399 * 2
def baseEnd_2589399 : Nat := 1329606293271619698204077

theorem tailTrace_2589399 : CollatzResearch.WordTrace tailWord_2589399 prefixEnd_2589399 1329606293271619698204077 := by
  unfold tailWord_2589399
  simp only [CollatzResearch.WordTrace]
  refine ⟨94443140346057131986251251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62962093564038087990834167 94443140346057131986251251)
  ·
    refine ⟨141664710519085697979376877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94443140346057131986251251 141664710519085697979376877)
    ·
      refine ⟨53124266444657136742266329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141664710519085697979376877 53124266444657136742266329)
      ·
        refine ⟨39843199833492852556699747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53124266444657136742266329 39843199833492852556699747)
        ·
          refine ⟨59764799750239278835049621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39843199833492852556699747 59764799750239278835049621)
          ·
            refine ⟨2801474988292466195392951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 59764799750239278835049621 2801474988292466195392951)
            ·
              refine ⟨4202212482438699293089427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2801474988292466195392951 4202212482438699293089427)
              ·
                refine ⟨6303318723658048939634141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4202212482438699293089427 6303318723658048939634141)
                ·
                  refine ⟨2363744521371768352362803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6303318723658048939634141 2363744521371768352362803)
                  ·
                    refine ⟨3545616782057652528544205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2363744521371768352362803 3545616782057652528544205)
                    ·
                      refine ⟨1329606293271619698204077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3545616782057652528544205 1329606293271619698204077)
                      ·
                        rfl

theorem cell23_2589399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 1, 3, 1, 3].length) (baseStart_2589399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2589399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2589399 prefixEnd_2589399 := by exact prefixLift 2589399
  have htrace : WordTrace (prefixWord ++ tailWord_2589399) baseStart_2589399 baseEnd_2589399 := by
    simpa [prefixWord, tailWord_2589399, baseEnd_2589399] using wordTrace_append hprefix tailTrace_2589399
  have hstable : (prefixWord ++ tailWord_2589399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2589399).length < 2 ^ (prefixWord ++ tailWord_2589399).sum := by decide
  have hdescent : baseEnd_2589399 < baseStart_2589399 := by decide
  rcases family_descends (prefixWord ++ tailWord_2589399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2589422 : List Nat := [4, 1, 2, 1, 1, 4, 1, 1, 3, 1, 4]
def baseStart_2589422 : Nat := 118140960795 + 2589422 * 2 ^ 59
def prefixEnd_2589422 : Nat := 4983230072969 + 3 ^ 40 * 2589422 * 2
def baseEnd_2589422 : Nat := 1329618103326673108216471

theorem tailTrace_2589422 : CollatzResearch.WordTrace tailWord_2589422 prefixEnd_2589422 1329618103326673108216471 := by
  unfold tailWord_2589422
  simp only [CollatzResearch.WordTrace]
  refine ⟨11805497403121725864292315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62962652816649204609559013 11805497403121725864292315)
  ·
    refine ⟨17708246104682588796438473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11805497403121725864292315 17708246104682588796438473)
    ·
      refine ⟨13281184578511941597328855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17708246104682588796438473 13281184578511941597328855)
      ·
        refine ⟨19921776867767912395993283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13281184578511941597328855 19921776867767912395993283)
        ·
          refine ⟨29882665301651868593989925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19921776867767912395993283 29882665301651868593989925)
          ·
            refine ⟨5602999744059725361373111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29882665301651868593989925 5602999744059725361373111)
            ·
              refine ⟨8404499616089588042059667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5602999744059725361373111 8404499616089588042059667)
              ·
                refine ⟨12606749424134382063089501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8404499616089588042059667 12606749424134382063089501)
                ·
                  refine ⟨4727531034050393273658563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12606749424134382063089501 4727531034050393273658563)
                  ·
                    refine ⟨7091296551075589910487845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4727531034050393273658563 7091296551075589910487845)
                    ·
                      refine ⟨1329618103326673108216471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7091296551075589910487845 1329618103326673108216471)
                      ·
                        rfl

theorem cell23_2589422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 1, 3, 1, 4].length) (baseStart_2589422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2589422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2589422 prefixEnd_2589422 := by exact prefixLift 2589422
  have htrace : WordTrace (prefixWord ++ tailWord_2589422) baseStart_2589422 baseEnd_2589422 := by
    simpa [prefixWord, tailWord_2589422, baseEnd_2589422] using wordTrace_append hprefix tailTrace_2589422
  have hstable : (prefixWord ++ tailWord_2589422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2589422).length < 2 ^ (prefixWord ++ tailWord_2589422).sum := by decide
  have hdescent : baseEnd_2589422 < baseStart_2589422 := by decide
  rcases family_descends (prefixWord ++ tailWord_2589422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2589455 : List Nat := [1, 1, 2, 1, 1, 1, 5, 2, 3, 3, 3]
def baseStart_2589455 : Nat := 118140960795 + 2589455 * 2 ^ 59
def prefixEnd_2589455 : Nat := 4983230072969 + 3 ^ 40 * 2589455 * 2
def baseEnd_2589455 : Nat := 1329635048188271479103819

theorem tailTrace_2589455 : CollatzResearch.WordTrace tailWord_2589455 prefixEnd_2589455 1329635048188271479103819 := by
  unfold tailWord_2589455
  simp only [CollatzResearch.WordTrace]
  refine ⟨94445182833854253550289819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62963455222569502366859879 94445182833854253550289819)
  ·
    refine ⟨141667774250781380325434729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94445182833854253550289819 141667774250781380325434729)
    ·
      refine ⟨106250830688086035244076047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141667774250781380325434729 106250830688086035244076047)
      ·
        refine ⟨159376246032129052866114071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106250830688086035244076047 159376246032129052866114071)
        ·
          refine ⟨239064369048193579299171107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159376246032129052866114071 239064369048193579299171107)
          ·
            refine ⟨358596553572290368948756661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 239064369048193579299171107 358596553572290368948756661)
            ·
              refine ⟨33618426897402222088945937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 358596553572290368948756661 33618426897402222088945937)
              ·
                refine ⟨25213820173051666566709453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33618426897402222088945937 25213820173051666566709453)
                ·
                  refine ⟨9455182564894374962516045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25213820173051666566709453 9455182564894374962516045)
                  ·
                    refine ⟨3545693461835390610943517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9455182564894374962516045 3545693461835390610943517)
                    ·
                      refine ⟨1329635048188271479103819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3545693461835390610943517 1329635048188271479103819)
                      ·
                        rfl

theorem cell23_2589455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 3, 3, 3].length) (baseStart_2589455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2589455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2589455 prefixEnd_2589455 := by exact prefixLift 2589455
  have htrace : WordTrace (prefixWord ++ tailWord_2589455) baseStart_2589455 baseEnd_2589455 := by
    simpa [prefixWord, tailWord_2589455, baseEnd_2589455] using wordTrace_append hprefix tailTrace_2589455
  have hstable : (prefixWord ++ tailWord_2589455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2589455).length < 2 ^ (prefixWord ++ tailWord_2589455).sum := by decide
  have hdescent : baseEnd_2589455 < baseStart_2589455 := by decide
  rcases family_descends (prefixWord ++ tailWord_2589455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2589472 : List Nat := [2, 1, 1, 5, 1, 2, 1, 3, 1, 3, 3]
def baseStart_2589472 : Nat := 118140960795 + 2589472 * 2 ^ 59
def prefixEnd_2589472 : Nat := 4983230072969 + 3 ^ 40 * 2589472 * 2
def baseEnd_2589472 : Nat := 1329643777359397912591241

theorem tailTrace_2589472 : CollatzResearch.WordTrace tailWord_2589472 prefixEnd_2589472 1329643777359397912591241 := by
  unfold tailWord_2589472
  simp only [CollatzResearch.WordTrace]
  refine ⟨47222901437396332726829335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62963868583195110302439113 47222901437396332726829335)
  ·
    refine ⟨70834352156094499090244003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47222901437396332726829335 70834352156094499090244003)
    ·
      refine ⟨106251528234141748635366005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70834352156094499090244003 106251528234141748635366005)
      ·
        refine ⟨9961080771950788934565563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 106251528234141748635366005 9961080771950788934565563)
        ·
          refine ⟨14941621157926183401848345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9961080771950788934565563 14941621157926183401848345)
          ·
            refine ⟨11206215868444637551386259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14941621157926183401848345 11206215868444637551386259)
            ·
              refine ⟨16809323802666956327079389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11206215868444637551386259 16809323802666956327079389)
              ·
                refine ⟨6303496426000108622654771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16809323802666956327079389 6303496426000108622654771)
                ·
                  refine ⟨9455244639000162933982157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6303496426000108622654771 9455244639000162933982157)
                  ·
                    refine ⟨3545716739625061100243309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9455244639000162933982157 3545716739625061100243309)
                    ·
                      refine ⟨1329643777359397912591241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3545716739625061100243309 1329643777359397912591241)
                      ·
                        rfl

theorem cell23_2589472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_2589472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2589472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2589472 prefixEnd_2589472 := by exact prefixLift 2589472
  have htrace : WordTrace (prefixWord ++ tailWord_2589472) baseStart_2589472 baseEnd_2589472 := by
    simpa [prefixWord, tailWord_2589472, baseEnd_2589472] using wordTrace_append hprefix tailTrace_2589472
  have hstable : (prefixWord ++ tailWord_2589472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2589472).length < 2 ^ (prefixWord ++ tailWord_2589472).sum := by decide
  have hdescent : baseEnd_2589472 < baseStart_2589472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2589472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2589529 : List Nat := [1, 2, 1, 2, 2, 4, 3, 1, 1, 4, 2]
def baseStart_2589529 : Nat := 118140960795 + 2589529 * 2 ^ 59
def prefixEnd_2589529 : Nat := 4983230072969 + 3 ^ 40 * 2589529 * 2
def baseEnd_2589529 : Nat := 1329673045756704189578479

theorem tailTrace_2589529 : CollatzResearch.WordTrace tailWord_2589529 prefixEnd_2589529 1329673045756704189578479 := by
  unfold tailWord_2589529
  simp only [CollatzResearch.WordTrace]
  refine ⟨94447881835586164188483641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62965254557057442792322427 94447881835586164188483641)
  ·
    refine ⟨70835911376689623141362731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94447881835586164188483641 70835911376689623141362731)
    ·
      refine ⟨106253867065034434712044097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70835911376689623141362731 106253867065034434712044097)
      ·
        refine ⟨79690400298775826034033073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106253867065034434712044097 79690400298775826034033073)
        ·
          refine ⟨59767800224081869525524805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79690400298775826034033073 59767800224081869525524805)
          ·
            refine ⟨11206462542015350536035901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59767800224081869525524805 11206462542015350536035901)
            ·
              refine ⟨4202423453255756451013463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11206462542015350536035901 4202423453255756451013463)
              ·
                refine ⟨6303635179883634676520195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4202423453255756451013463 6303635179883634676520195)
                ·
                  refine ⟨9455452769825452014780293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6303635179883634676520195 9455452769825452014780293)
                  ·
                    refine ⟨1772897394342272252771305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9455452769825452014780293 1772897394342272252771305)
                    ·
                      refine ⟨1329673045756704189578479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1772897394342272252771305 1329673045756704189578479)
                      ·
                        rfl

theorem cell23_2589529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 1, 1, 4, 2].length) (baseStart_2589529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2589529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2589529 prefixEnd_2589529 := by exact prefixLift 2589529
  have htrace : WordTrace (prefixWord ++ tailWord_2589529) baseStart_2589529 baseEnd_2589529 := by
    simpa [prefixWord, tailWord_2589529, baseEnd_2589529] using wordTrace_append hprefix tailTrace_2589529
  have hstable : (prefixWord ++ tailWord_2589529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2589529).length < 2 ^ (prefixWord ++ tailWord_2589529).sum := by decide
  have hdescent : baseEnd_2589529 < baseStart_2589529 := by decide
  rcases family_descends (prefixWord ++ tailWord_2589529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2589535 : List Nat := [1, 1, 2, 3, 1, 3, 1, 4, 7]
def baseStart_2589535 : Nat := 118140960795 + 2589535 * 2 ^ 59
def prefixEnd_2589535 : Nat := 4983230072969 + 3 ^ 40 * 2589535 * 2
def baseEnd_2589535 : Nat := 147741791848959018455939

theorem tailTrace_2589535 : CollatzResearch.WordTrace tailWord_2589535 prefixEnd_2589535 147741791848959018455939 := by
  unfold tailWord_2589535
  simp only [CollatzResearch.WordTrace]
  refine ⟨94448100673564427213202059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62965400449042951475468039 94448100673564427213202059)
  ·
    refine ⟨141672151010346640819803089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94448100673564427213202059 141672151010346640819803089)
    ·
      refine ⟨106254113257759980614852317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141672151010346640819803089 106254113257759980614852317)
      ·
        refine ⟨39845292471659992730569619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106254113257759980614852317 39845292471659992730569619)
        ·
          refine ⟨59767938707489989095854429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39845292471659992730569619 59767938707489989095854429)
          ·
            refine ⟨22412977015308745910945411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59767938707489989095854429 22412977015308745910945411)
            ·
              refine ⟨33619465522963118866418117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22412977015308745910945411 33619465522963118866418117)
              ·
                refine ⟨6303649785555584787453397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33619465522963118866418117 6303649785555584787453397)
                ·
                  refine ⟨147741791848959018455939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6303649785555584787453397 147741791848959018455939)
                  ·
                    rfl

theorem cell23_2589535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 4, 7].length) (baseStart_2589535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2589535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2589535 prefixEnd_2589535 := by exact prefixLift 2589535
  have htrace : WordTrace (prefixWord ++ tailWord_2589535) baseStart_2589535 baseEnd_2589535 := by
    simpa [prefixWord, tailWord_2589535, baseEnd_2589535] using wordTrace_append hprefix tailTrace_2589535
  have hstable : (prefixWord ++ tailWord_2589535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2589535).length < 2 ^ (prefixWord ++ tailWord_2589535).sum := by decide
  have hdescent : baseEnd_2589535 < baseStart_2589535 := by decide
  rcases family_descends (prefixWord ++ tailWord_2589535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2589599 : List Nat := [1, 1, 2, 5, 2, 2, 2, 1, 2, 5]
def baseStart_2589599 : Nat := 118140960795 + 2589599 * 2 ^ 59
def prefixEnd_2589599 : Nat := 4983230072969 + 3 ^ 40 * 2589599 * 2
def baseEnd_2589599 : Nat := 443236329800839638567719

theorem tailTrace_2589599 : CollatzResearch.WordTrace tailWord_2589599 prefixEnd_2589599 443236329800839638567719 := by
  unfold tailWord_2589599
  simp only [CollatzResearch.WordTrace]
  refine ⟨94450434945332566143531851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62966956630221710762354567 94450434945332566143531851)
  ·
    refine ⟨141675652417998849215297777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94450434945332566143531851 141675652417998849215297777)
    ·
      refine ⟨106256739313499136911473333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141675652417998849215297777 106256739313499136911473333)
      ·
        refine ⟨9961569310640544085450625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 106256739313499136911473333 9961569310640544085450625)
        ·
          refine ⟨7471176982980408064087969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9961569310640544085450625 7471176982980408064087969)
          ·
            refine ⟨5603382737235306048065977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7471176982980408064087969 5603382737235306048065977)
            ·
              refine ⟨4202537052926479536049483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5603382737235306048065977 4202537052926479536049483)
              ·
                refine ⟨6303805579389719304074225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4202537052926479536049483 6303805579389719304074225)
                ·
                  refine ⟨4727854184542289478055669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6303805579389719304074225 4727854184542289478055669)
                  ·
                    refine ⟨443236329800839638567719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4727854184542289478055669 443236329800839638567719)
                    ·
                      rfl

theorem cell23_2589599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 1, 2, 5].length) (baseStart_2589599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2589599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2589599 prefixEnd_2589599 := by exact prefixLift 2589599
  have htrace : WordTrace (prefixWord ++ tailWord_2589599) baseStart_2589599 baseEnd_2589599 := by
    simpa [prefixWord, tailWord_2589599, baseEnd_2589599] using wordTrace_append hprefix tailTrace_2589599
  have hstable : (prefixWord ++ tailWord_2589599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2589599).length < 2 ^ (prefixWord ++ tailWord_2589599).sum := by decide
  have hdescent : baseEnd_2589599 < baseStart_2589599 := by decide
  rcases family_descends (prefixWord ++ tailWord_2589599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2589605 : List Nat := [1, 3, 1, 2, 1, 1, 1, 1, 1, 2, 9]
def baseStart_2589605 : Nat := 118140960795 + 2589605 * 2 ^ 59
def prefixEnd_2589605 : Nat := 4983230072969 + 3 ^ 40 * 2589605 * 2
def baseEnd_2589605 : Nat := 1329712070286445892228129

theorem tailTrace_2589605 : CollatzResearch.WordTrace tailWord_2589605 prefixEnd_2589605 1329712070286445892228129 := by
  unfold tailWord_2589605
  simp only [CollatzResearch.WordTrace]
  refine ⟨94450653783310829168250269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62967102522207219445500179 94450653783310829168250269)
  ·
    refine ⟨35418995168741560938093851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94450653783310829168250269 35418995168741560938093851)
    ·
      refine ⟨53128492753112341407140777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35418995168741560938093851 53128492753112341407140777)
      ·
        refine ⟨39846369564834256055355583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53128492753112341407140777 39846369564834256055355583)
        ·
          refine ⟨59769554347251384083033375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39846369564834256055355583 59769554347251384083033375)
          ·
            refine ⟨89654331520877076124550063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59769554347251384083033375 89654331520877076124550063)
            ·
              refine ⟨134481497281315614186825095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89654331520877076124550063 134481497281315614186825095)
              ·
                refine ⟨201722245921973421280237643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 134481497281315614186825095 201722245921973421280237643)
                ·
                  refine ⟨302583368882960131920356465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 201722245921973421280237643 302583368882960131920356465)
                  ·
                    refine ⟨226937526662220098940267349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 302583368882960131920356465 226937526662220098940267349)
                    ·
                      refine ⟨1329712070286445892228129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 226937526662220098940267349 1329712070286445892228129)
                      ·
                        rfl

theorem cell23_2589605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 2, 9].length) (baseStart_2589605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2589605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2589605 prefixEnd_2589605 := by exact prefixLift 2589605
  have htrace : WordTrace (prefixWord ++ tailWord_2589605) baseStart_2589605 baseEnd_2589605 := by
    simpa [prefixWord, tailWord_2589605, baseEnd_2589605] using wordTrace_append hprefix tailTrace_2589605
  have hstable : (prefixWord ++ tailWord_2589605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2589605).length < 2 ^ (prefixWord ++ tailWord_2589605).sum := by decide
  have hdescent : baseEnd_2589605 < baseStart_2589605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2589605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2589612 : List Nat := [2, 2, 1, 1, 1, 1, 2, 4, 5, 4]
def baseStart_2589612 : Nat := 118140960795 + 2589612 * 2 ^ 59
def prefixEnd_2589612 : Nat := 4983230072969 + 3 ^ 40 * 2589612 * 2
def baseEnd_2589612 : Nat := 443238554883675788280199

theorem tailTrace_2589612 : CollatzResearch.WordTrace tailWord_2589612 prefixEnd_2589612 443238554883675788280199 := by
  unfold tailWord_2589612
  simp only [CollatzResearch.WordTrace]
  refine ⟨47225454547142734681877545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62967272729523646242503393 47225454547142734681877545)
  ·
    refine ⟨35419090910357051011408159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47225454547142734681877545 35419090910357051011408159)
    ·
      refine ⟨53128636365535576517112239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35419090910357051011408159 53128636365535576517112239)
      ·
        refine ⟨79692954548303364775668359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53128636365535576517112239 79692954548303364775668359)
        ·
          refine ⟨119539431822455047163502539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79692954548303364775668359 119539431822455047163502539)
          ·
            refine ⟨179309147733682570745253809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119539431822455047163502539 179309147733682570745253809)
            ·
              refine ⟨134481860800261928058940357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 179309147733682570745253809 134481860800261928058940357)
              ·
                refine ⟨25215348900049111511051317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 134481860800261928058940357 25215348900049111511051317)
                ·
                  refine ⟨2363938959379604204161061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25215348900049111511051317 2363938959379604204161061)
                  ·
                    refine ⟨443238554883675788280199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2363938959379604204161061 443238554883675788280199)
                    ·
                      rfl

theorem cell23_2589612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 4].length) (baseStart_2589612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2589612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2589612 prefixEnd_2589612 := by exact prefixLift 2589612
  have htrace : WordTrace (prefixWord ++ tailWord_2589612) baseStart_2589612 baseEnd_2589612 := by
    simpa [prefixWord, tailWord_2589612, baseEnd_2589612] using wordTrace_append hprefix tailTrace_2589612
  have hstable : (prefixWord ++ tailWord_2589612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2589612).length < 2 ^ (prefixWord ++ tailWord_2589612).sum := by decide
  have hdescent : baseEnd_2589612 < baseStart_2589612 := by decide
  rcases family_descends (prefixWord ++ tailWord_2589612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2589620 : List Nat := [2, 5, 2, 1, 1, 3, 2, 2, 5]
def baseStart_2589620 : Nat := 118140960795 + 2589620 * 2 ^ 59
def prefixEnd_2589620 : Nat := 4983230072969 + 3 ^ 40 * 2589620 * 2
def baseEnd_2589620 : Nat := 147746641388473703726729

theorem tailTrace_2589620 : CollatzResearch.WordTrace tailWord_2589620 prefixEnd_2589620 147746641388473703726729 := by
  unfold tailWord_2589620
  simp only [CollatzResearch.WordTrace]
  refine ⟨47225600439128243365023157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62967467252170991153364209 47225600439128243365023157)
  ·
    refine ⟨4427400041168272815470921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 47225600439128243365023157 4427400041168272815470921)
    ·
      refine ⟨3320550030876204611603191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4427400041168272815470921 3320550030876204611603191)
      ·
        refine ⟨4980825046314306917404787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3320550030876204611603191 4980825046314306917404787)
        ·
          refine ⟨7471237569471460376107181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4980825046314306917404787 7471237569471460376107181)
          ·
            refine ⟨2801714088551797641040193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7471237569471460376107181 2801714088551797641040193)
            ·
              refine ⟨2101285566413848230780145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2801714088551797641040193 2101285566413848230780145)
              ·
                refine ⟨1575964174810386173085109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2101285566413848230780145 1575964174810386173085109)
                ·
                  refine ⟨147746641388473703726729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1575964174810386173085109 147746641388473703726729)
                  ·
                    rfl

theorem cell23_2589620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 2, 2, 5].length) (baseStart_2589620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2589620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2589620 prefixEnd_2589620 := by exact prefixLift 2589620
  have htrace : WordTrace (prefixWord ++ tailWord_2589620) baseStart_2589620 baseEnd_2589620 := by
    simpa [prefixWord, tailWord_2589620, baseEnd_2589620] using wordTrace_append hprefix tailTrace_2589620
  have hstable : (prefixWord ++ tailWord_2589620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2589620).length < 2 ^ (prefixWord ++ tailWord_2589620).sum := by decide
  have hdescent : baseEnd_2589620 < baseStart_2589620 := by decide
  rcases family_descends (prefixWord ++ tailWord_2589620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
