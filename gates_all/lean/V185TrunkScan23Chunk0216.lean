import V185TrunkScan23Chunk0215

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1277965 : List Nat := [1, 7, 1, 2, 1, 2, 1, 3, 1, 1, 3]
def baseStart_1277965 : Nat := 118140960795 + 1277965 * 2 ^ 59
def prefixEnd_1277965 : Nat := 4983230072969 + 3 ^ 40 * 1277965 * 2
def baseEnd_1277965 : Nat := 656210304623197689760253

theorem tailTrace_1277965 : CollatzResearch.WordTrace tailWord_1277965 prefixEnd_1277965 656210304623197689760253 := by
  unfold tailWord_1277965
  simp only [CollatzResearch.WordTrace]
  refine ⟨46611212815158538890619349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31074141876772359260412899 46611212815158538890619349)
  ·
    refine ⟨1092450300355278255248891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 46611212815158538890619349 1092450300355278255248891)
    ·
      refine ⟨1638675450532917382873337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1092450300355278255248891 1638675450532917382873337)
      ·
        refine ⟨1229006587899688037155003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1638675450532917382873337 1229006587899688037155003)
        ·
          refine ⟨1843509881849532055732505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1229006587899688037155003 1843509881849532055732505)
          ·
            refine ⟨1382632411387149041799379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1843509881849532055732505 1382632411387149041799379)
            ·
              refine ⟨2073948617080723562699069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1382632411387149041799379 2073948617080723562699069)
              ·
                refine ⟨777730731405271336012151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2073948617080723562699069 777730731405271336012151)
                ·
                  refine ⟨1166596097107907004018227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 777730731405271336012151 1166596097107907004018227)
                  ·
                    refine ⟨1749894145661860506027341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1166596097107907004018227 1749894145661860506027341)
                    ·
                      refine ⟨656210304623197689760253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1749894145661860506027341 656210304623197689760253)
                      ·
                        rfl

theorem cell23_1277965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_1277965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1277965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1277965 prefixEnd_1277965 := by exact prefixLift 1277965
  have htrace : WordTrace (prefixWord ++ tailWord_1277965) baseStart_1277965 baseEnd_1277965 := by
    simpa [prefixWord, tailWord_1277965, baseEnd_1277965] using wordTrace_append hprefix tailTrace_1277965
  have hstable : (prefixWord ++ tailWord_1277965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277965).length < 2 ^ (prefixWord ++ tailWord_1277965).sum := by decide
  have hdescent : baseEnd_1277965 < baseStart_1277965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277988 : List Nat := [2, 3, 1, 4, 2, 1, 3, 2, 1, 2, 2]
def baseStart_1277988 : Nat := 118140960795 + 1277988 * 2 ^ 59
def prefixEnd_1277988 : Nat := 4983230072969 + 3 ^ 40 * 1277988 * 2
def baseEnd_1277988 : Nat := 656222114678251099772647

theorem tailTrace_1277988 : CollatzResearch.WordTrace tailWord_1277988 prefixEnd_1277988 656222114678251099772647 := by
  unfold tailWord_1277988
  simp only [CollatzResearch.WordTrace]
  refine ⟨23306025847037606909353309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31074701129383475879137745 23306025847037606909353309)
  ·
    refine ⟨8739759692639102591007491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23306025847037606909353309 8739759692639102591007491)
    ·
      refine ⟨13109639538958653886511237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8739759692639102591007491 13109639538958653886511237)
      ·
        refine ⟨2458057413554747603720857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13109639538958653886511237 2458057413554747603720857)
        ·
          refine ⟨1843543060166060702790643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2458057413554747603720857 1843543060166060702790643)
          ·
            refine ⟨2765314590249091054185965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1843543060166060702790643 2765314590249091054185965)
            ·
              refine ⟨1036992971343409145319737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2765314590249091054185965 1036992971343409145319737)
              ·
                refine ⟨777744728507556858989803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1036992971343409145319737 777744728507556858989803)
                ·
                  refine ⟨1166617092761335288484705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 777744728507556858989803 1166617092761335288484705)
                  ·
                    refine ⟨874962819571001466363529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1166617092761335288484705 874962819571001466363529)
                    ·
                      refine ⟨656222114678251099772647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 874962819571001466363529 656222114678251099772647)
                      ·
                        rfl

theorem cell23_1277988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 3, 2, 1, 2, 2].length) (baseStart_1277988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1277988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1277988 prefixEnd_1277988 := by exact prefixLift 1277988
  have htrace : WordTrace (prefixWord ++ tailWord_1277988) baseStart_1277988 baseEnd_1277988 := by
    simpa [prefixWord, tailWord_1277988, baseEnd_1277988] using wordTrace_append hprefix tailTrace_1277988
  have hstable : (prefixWord ++ tailWord_1277988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277988).length < 2 ^ (prefixWord ++ tailWord_1277988).sum := by decide
  have hdescent : baseEnd_1277988 < baseStart_1277988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278010 : List Nat := [3, 1, 1, 1, 3, 1, 1, 5, 1, 4, 2]
def baseStart_1278010 : Nat := 118140960795 + 1278010 * 2 ^ 59
def prefixEnd_1278010 : Nat := 4983230072969 + 3 ^ 40 * 1278010 * 2
def baseEnd_1278010 : Nat := 656233411252650013697545

theorem tailTrace_1278010 : CollatzResearch.WordTrace tailWord_1278010 prefixEnd_1278010 656233411252650013697545 := by
  unfold tailWord_1278010
  simp only [CollatzResearch.WordTrace]
  refine ⟨11653213524998877894001871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31075236066663674384004989 11653213524998877894001871)
  ·
    refine ⟨17479820287498316841002807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11653213524998877894001871 17479820287498316841002807)
    ·
      refine ⟨26219730431247475261504211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17479820287498316841002807 26219730431247475261504211)
      ·
        refine ⟨39329595646871212892256317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26219730431247475261504211 39329595646871212892256317)
        ·
          refine ⟨14748598367576704834596119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39329595646871212892256317 14748598367576704834596119)
          ·
            refine ⟨22122897551365057251894179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14748598367576704834596119 22122897551365057251894179)
            ·
              refine ⟨33184346327047585877841269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22122897551365057251894179 33184346327047585877841269)
              ·
                refine ⟨3111032468160711176047619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33184346327047585877841269 3111032468160711176047619)
                ·
                  refine ⟨4666548702241066764071429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3111032468160711176047619 4666548702241066764071429)
                  ·
                    refine ⟨874977881670200018263393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4666548702241066764071429 874977881670200018263393)
                    ·
                      refine ⟨656233411252650013697545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 874977881670200018263393 656233411252650013697545)
                      ·
                        rfl

theorem cell23_1278010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 5, 1, 4, 2].length) (baseStart_1278010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1278010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1278010 prefixEnd_1278010 := by exact prefixLift 1278010
  have htrace : WordTrace (prefixWord ++ tailWord_1278010) baseStart_1278010 baseEnd_1278010 := by
    simpa [prefixWord, tailWord_1278010, baseEnd_1278010] using wordTrace_append hprefix tailTrace_1278010
  have hstable : (prefixWord ++ tailWord_1278010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278010).length < 2 ^ (prefixWord ++ tailWord_1278010).sum := by decide
  have hdescent : baseEnd_1278010 < baseStart_1278010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278013 : List Nat := [1, 4, 1, 3, 1, 1, 1, 1, 4, 1, 5]
def baseStart_1278013 : Nat := 118140960795 + 1278013 * 2 ^ 59
def prefixEnd_1278013 : Nat := 4983230072969 + 3 ^ 40 * 1278013 * 2
def baseEnd_1278013 : Nat := 656234951694613501960031

theorem tailTrace_1278013 : CollatzResearch.WordTrace tailWord_1278013 prefixEnd_1278013 656234951694613501960031 := by
  unfold tailWord_1278013
  simp only [CollatzResearch.WordTrace]
  refine ⟨46612963518984643088366693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31075309012656428725577795 46612963518984643088366693)
  ·
    refine ⟨8739930659809620579068755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46612963518984643088366693 8739930659809620579068755)
    ·
      refine ⟨13109895989714430868603133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8739930659809620579068755 13109895989714430868603133)
      ·
        refine ⟨4916210996142911575726175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13109895989714430868603133 4916210996142911575726175)
        ·
          refine ⟨7374316494214367363589263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4916210996142911575726175 7374316494214367363589263)
          ·
            refine ⟨11061474741321551045383895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7374316494214367363589263 11061474741321551045383895)
            ·
              refine ⟨16592212111982326568075843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11061474741321551045383895 16592212111982326568075843)
              ·
                refine ⟨24888318167973489852113765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16592212111982326568075843 24888318167973489852113765)
                ·
                  refine ⟨4666559656495029347271331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24888318167973489852113765 4666559656495029347271331)
                  ·
                    refine ⟨6999839484742544020906997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4666559656495029347271331 6999839484742544020906997)
                    ·
                      refine ⟨656234951694613501960031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6999839484742544020906997 656234951694613501960031)
                      ·
                        rfl

theorem cell23_1278013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_1278013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1278013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1278013 prefixEnd_1278013 := by exact prefixLift 1278013
  have htrace : WordTrace (prefixWord ++ tailWord_1278013) baseStart_1278013 baseEnd_1278013 := by
    simpa [prefixWord, tailWord_1278013, baseEnd_1278013] using wordTrace_append hprefix tailTrace_1278013
  have hstable : (prefixWord ++ tailWord_1278013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278013).length < 2 ^ (prefixWord ++ tailWord_1278013).sum := by decide
  have hdescent : baseEnd_1278013 < baseStart_1278013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278014 : List Nat := [4, 2, 1, 3, 2, 1, 1, 1, 3, 3, 2]
def baseStart_1278014 : Nat := 118140960795 + 1278014 * 2 ^ 59
def prefixEnd_1278014 : Nat := 4983230072969 + 3 ^ 40 * 1278014 * 2
def baseEnd_1278014 : Nat := 656235465175267998047527

theorem tailTrace_1278014 : CollatzResearch.WordTrace tailWord_1278014 prefixEnd_1278014 656235465175267998047527 := by
  unfold tailWord_1278014
  simp only [CollatzResearch.WordTrace]
  refine ⟨5826624998997627532394137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31075333327987346839435397 5826624998997627532394137)
  ·
    refine ⟨4369968749248220649295603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5826624998997627532394137 4369968749248220649295603)
    ·
      refine ⟨6554953123872330973943405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4369968749248220649295603 6554953123872330973943405)
      ·
        refine ⟨2458107421452124115228777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6554953123872330973943405 2458107421452124115228777)
        ·
          refine ⟨1843580566089093086421583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2458107421452124115228777 1843580566089093086421583)
          ·
            refine ⟨2765370849133639629632375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1843580566089093086421583 2765370849133639629632375)
            ·
              refine ⟨4148056273700459444448563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2765370849133639629632375 4148056273700459444448563)
              ·
                refine ⟨6222084410550689166672845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4148056273700459444448563 6222084410550689166672845)
                ·
                  refine ⟨2333281653956508437502317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6222084410550689166672845 2333281653956508437502317)
                  ·
                    refine ⟨874980620233690664063369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2333281653956508437502317 874980620233690664063369)
                    ·
                      refine ⟨656235465175267998047527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 874980620233690664063369 656235465175267998047527)
                      ·
                        rfl

theorem cell23_1278014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_1278014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1278014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1278014 prefixEnd_1278014 := by exact prefixLift 1278014
  have htrace : WordTrace (prefixWord ++ tailWord_1278014) baseStart_1278014 baseEnd_1278014 := by
    simpa [prefixWord, tailWord_1278014, baseEnd_1278014] using wordTrace_append hprefix tailTrace_1278014
  have hstable : (prefixWord ++ tailWord_1278014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278014).length < 2 ^ (prefixWord ++ tailWord_1278014).sum := by decide
  have hdescent : baseEnd_1278014 < baseStart_1278014 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278044 : List Nat := [2, 2, 4, 1, 1, 2, 1, 4, 2, 2, 2]
def baseStart_1278044 : Nat := 118140960795 + 1278044 * 2 ^ 59
def prefixEnd_1278044 : Nat := 4983230072969 + 3 ^ 40 * 1278044 * 2
def baseEnd_1278044 : Nat := 656250869594902880672389

theorem tailTrace_1278044 : CollatzResearch.WordTrace tailWord_1278044 prefixEnd_1278044 656250869594902880672389 := by
  unfold tailWord_1278044
  simp only [CollatzResearch.WordTrace]
  refine ⟨23307047090936167691372593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31076062787914890255163457 23307047090936167691372593)
  ·
    refine ⟨17480285318202125768529445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23307047090936167691372593 17480285318202125768529445)
    ·
      refine ⟨3277553497162898581599271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17480285318202125768529445 3277553497162898581599271)
      ·
        refine ⟨4916330245744347872398907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3277553497162898581599271 4916330245744347872398907)
        ·
          refine ⟨7374495368616521808598361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4916330245744347872398907 7374495368616521808598361)
          ·
            refine ⟨5530871526462391356448771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7374495368616521808598361 5530871526462391356448771)
            ·
              refine ⟨8296307289693587034673157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5530871526462391356448771 8296307289693587034673157)
              ·
                refine ⟨1555557616817547569001217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8296307289693587034673157 1555557616817547569001217)
                ·
                  refine ⟨1166668212613160676750913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1555557616817547569001217 1166668212613160676750913)
                  ·
                    refine ⟨875001159459870507563185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1166668212613160676750913 875001159459870507563185)
                    ·
                      refine ⟨656250869594902880672389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 875001159459870507563185 656250869594902880672389)
                      ·
                        rfl

theorem cell23_1278044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 4, 2, 2, 2].length) (baseStart_1278044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1278044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1278044 prefixEnd_1278044 := by exact prefixLift 1278044
  have htrace : WordTrace (prefixWord ++ tailWord_1278044) baseStart_1278044 baseEnd_1278044 := by
    simpa [prefixWord, tailWord_1278044, baseEnd_1278044] using wordTrace_append hprefix tailTrace_1278044
  have hstable : (prefixWord ++ tailWord_1278044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278044).length < 2 ^ (prefixWord ++ tailWord_1278044).sum := by decide
  have hdescent : baseEnd_1278044 < baseStart_1278044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278060 : List Nat := [2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 3]
def baseStart_1278060 : Nat := 118140960795 + 1278060 * 2 ^ 59
def prefixEnd_1278060 : Nat := 4983230072969 + 3 ^ 40 * 1278060 * 2
def baseEnd_1278060 : Nat := 656259085285374818072315

theorem tailTrace_1278060 : CollatzResearch.WordTrace tailWord_1278060 prefixEnd_1278060 656259085285374818072315 := by
  unfold tailWord_1278060
  simp only [CollatzResearch.WordTrace]
  refine ⟨23307338874907185057663817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31076451833209580076885089 23307338874907185057663817)
  ·
    refine ⟨17480504156180388793247863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23307338874907185057663817 17480504156180388793247863)
    ·
      refine ⟨26220756234270583189871795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17480504156180388793247863 26220756234270583189871795)
      ·
        refine ⟨39331134351405874784807693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26220756234270583189871795 39331134351405874784807693)
        ·
          refine ⟨14749175381777203044302885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39331134351405874784807693 14749175381777203044302885)
          ·
            refine ⟨2765470384083225570806791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14749175381777203044302885 2765470384083225570806791)
            ·
              refine ⟨4148205576124838356210187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2765470384083225570806791 4148205576124838356210187)
              ·
                refine ⟨6222308364187257534315281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4148205576124838356210187 6222308364187257534315281)
                ·
                  refine ⟨4666731273140443150736461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6222308364187257534315281 4666731273140443150736461)
                  ·
                    refine ⟨1750024227427666181526173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4666731273140443150736461 1750024227427666181526173)
                    ·
                      refine ⟨656259085285374818072315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1750024227427666181526173 656259085285374818072315)
                      ·
                        rfl

theorem cell23_1278060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 3].length) (baseStart_1278060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1278060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1278060 prefixEnd_1278060 := by exact prefixLift 1278060
  have htrace : WordTrace (prefixWord ++ tailWord_1278060) baseStart_1278060 baseEnd_1278060 := by
    simpa [prefixWord, tailWord_1278060, baseEnd_1278060] using wordTrace_append hprefix tailTrace_1278060
  have hstable : (prefixWord ++ tailWord_1278060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278060).length < 2 ^ (prefixWord ++ tailWord_1278060).sum := by decide
  have hdescent : baseEnd_1278060 < baseStart_1278060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278144 : List Nat := [2, 1, 1, 2, 5, 1, 3, 3, 1, 4]
def baseStart_1278144 : Nat := 118140960795 + 1278144 * 2 ^ 59
def prefixEnd_1278144 : Nat := 4983230072969 + 3 ^ 40 * 1278144 * 2
def baseEnd_1278144 : Nat := 218767405886784163140643

theorem tailTrace_1278144 : CollatzResearch.WordTrace tailWord_1278144 prefixEnd_1278144 218767405886784163140643 := by
  unfold tailWord_1278144
  simp only [CollatzResearch.WordTrace]
  refine ⟨23308870740755026230692743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31078494321006701640923657 23308870740755026230692743)
  ·
    refine ⟨34963306111132539346039115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23308870740755026230692743 34963306111132539346039115)
    ·
      refine ⟨52444959166698809019058673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34963306111132539346039115 52444959166698809019058673)
      ·
        refine ⟨39333719375024106764294005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52444959166698809019058673 39333719375024106764294005)
        ·
          refine ⟨3687536191408510009152563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39333719375024106764294005 3687536191408510009152563)
          ·
            refine ⟨5531304287112765013728845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3687536191408510009152563 5531304287112765013728845)
            ·
              refine ⟨2074239107667286880148317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5531304287112765013728845 2074239107667286880148317)
              ·
                refine ⟨777839665375232580055619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2074239107667286880148317 777839665375232580055619)
                ·
                  refine ⟨1166759498062848870083429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 777839665375232580055619 1166759498062848870083429)
                  ·
                    refine ⟨218767405886784163140643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1166759498062848870083429 218767405886784163140643)
                    ·
                      rfl

theorem cell23_1278144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 3, 1, 4].length) (baseStart_1278144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1278144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1278144 prefixEnd_1278144 := by exact prefixLift 1278144
  have htrace : WordTrace (prefixWord ++ tailWord_1278144) baseStart_1278144 baseEnd_1278144 := by
    simpa [prefixWord, tailWord_1278144, baseEnd_1278144] using wordTrace_append hprefix tailTrace_1278144
  have hstable : (prefixWord ++ tailWord_1278144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278144).length < 2 ^ (prefixWord ++ tailWord_1278144).sum := by decide
  have hdescent : baseEnd_1278144 < baseStart_1278144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278160 : List Nat := [2, 1, 1, 1, 1, 2, 1, 1, 2, 9, 2]
def baseStart_1278160 : Nat := 118140960795 + 1278160 * 2 ^ 59
def prefixEnd_1278160 : Nat := 4983230072969 + 3 ^ 40 * 1278160 * 2
def baseEnd_1278160 : Nat := 656310433350824426821855

theorem tailTrace_1278160 : CollatzResearch.WordTrace tailWord_1278160 prefixEnd_1278160 656310433350824426821855 := by
  unfold tailWord_1278160
  simp only [CollatzResearch.WordTrace]
  refine ⟨23309162524726043596983967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31078883366301391462645289 23309162524726043596983967)
  ·
    refine ⟨34963743787089065395475951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23309162524726043596983967 34963743787089065395475951)
    ·
      refine ⟨52445615680633598093213927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34963743787089065395475951 52445615680633598093213927)
      ·
        refine ⟨78668423520950397139820891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52445615680633598093213927 78668423520950397139820891)
        ·
          refine ⟨118002635281425595709731337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78668423520950397139820891 118002635281425595709731337)
          ·
            refine ⟨88501976461069196782298503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118002635281425595709731337 88501976461069196782298503)
            ·
              refine ⟨132752964691603795173447755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88501976461069196782298503 132752964691603795173447755)
              ·
                refine ⟨199129447037405692760171633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 132752964691603795173447755 199129447037405692760171633)
                ·
                  refine ⟨149347085278054269570128725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 199129447037405692760171633 149347085278054269570128725)
                  ·
                    refine ⟨875080577801099235762473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 149347085278054269570128725 875080577801099235762473)
                    ·
                      refine ⟨656310433350824426821855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 875080577801099235762473 656310433350824426821855)
                      ·
                        rfl

theorem cell23_1278160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 2, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 2, 9, 2].length) (baseStart_1278160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1278160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1278160 prefixEnd_1278160 := by exact prefixLift 1278160
  have htrace : WordTrace (prefixWord ++ tailWord_1278160) baseStart_1278160 baseEnd_1278160 := by
    simpa [prefixWord, tailWord_1278160, baseEnd_1278160] using wordTrace_append hprefix tailTrace_1278160
  have hstable : (prefixWord ++ tailWord_1278160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278160).length < 2 ^ (prefixWord ++ tailWord_1278160).sum := by decide
  have hdescent : baseEnd_1278160 < baseStart_1278160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278177 : List Nat := [1, 2, 3, 1, 3, 1, 1, 2, 4, 3, 2]
def baseStart_1278177 : Nat := 118140960795 + 1278177 * 2 ^ 59
def prefixEnd_1278177 : Nat := 4983230072969 + 3 ^ 40 * 1278177 * 2
def baseEnd_1278177 : Nat := 656319162521950860309277

theorem tailTrace_1278177 : CollatzResearch.WordTrace tailWord_1278177 prefixEnd_1278177 656319162521950860309277 := by
  unfold tailWord_1278177
  simp only [CollatzResearch.WordTrace]
  refine ⟨46618945090390499097336785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31079296726926999398224523 46618945090390499097336785)
  ·
    refine ⟨34964208817792874323002589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46618945090390499097336785 34964208817792874323002589)
    ·
      refine ⟨13111578306672327871125971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34964208817792874323002589 13111578306672327871125971)
      ·
        refine ⟨19667367460008491806688957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13111578306672327871125971 19667367460008491806688957)
        ·
          refine ⟨7375262797503184427508359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19667367460008491806688957 7375262797503184427508359)
          ·
            refine ⟨11062894196254776641262539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7375262797503184427508359 11062894196254776641262539)
            ·
              refine ⟨16594341294382164961893809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11062894196254776641262539 16594341294382164961893809)
              ·
                refine ⟨12445755970786623721420357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16594341294382164961893809 12445755970786623721420357)
                ·
                  refine ⟨2333579244522491947766317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12445755970786623721420357 2333579244522491947766317)
                  ·
                    refine ⟨875092216695934480412369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2333579244522491947766317 875092216695934480412369)
                    ·
                      refine ⟨656319162521950860309277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 875092216695934480412369 656319162521950860309277)
                      ·
                        rfl

theorem cell23_1278177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 4, 3, 2].length) (baseStart_1278177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1278177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1278177 prefixEnd_1278177 := by exact prefixLift 1278177
  have htrace : WordTrace (prefixWord ++ tailWord_1278177) baseStart_1278177 baseEnd_1278177 := by
    simpa [prefixWord, tailWord_1278177, baseEnd_1278177] using wordTrace_append hprefix tailTrace_1278177
  have hstable : (prefixWord ++ tailWord_1278177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278177).length < 2 ^ (prefixWord ++ tailWord_1278177).sum := by decide
  have hdescent : baseEnd_1278177 < baseStart_1278177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278194 : List Nat := [3, 2, 1, 3, 2, 1, 1, 3, 2, 3, 2]
def baseStart_1278194 : Nat := 118140960795 + 1278194 * 2 ^ 59
def prefixEnd_1278194 : Nat := 4983230072969 + 3 ^ 40 * 1278194 * 2
def baseEnd_1278194 : Nat := 656327891693077293796699

theorem tailTrace_1278194 : CollatzResearch.WordTrace tailWord_1278194 prefixEnd_1278194 656327891693077293796699 := by
  unfold tailWord_1278194
  simp only [CollatzResearch.WordTrace]
  refine ⟨11654891282832227750176409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31079710087552607333803757 11654891282832227750176409)
  ·
    refine ⟨8741168462124170812632307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11654891282832227750176409 8741168462124170812632307)
    ·
      refine ⟨13111752693186256218948461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8741168462124170812632307 13111752693186256218948461)
      ·
        refine ⟨4916907259944846082105673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13111752693186256218948461 4916907259944846082105673)
        ·
          refine ⟨3687680444958634561579255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4916907259944846082105673 3687680444958634561579255)
          ·
            refine ⟨5531520667437951842368883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3687680444958634561579255 5531520667437951842368883)
            ·
              refine ⟨8297281001156927763553325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5531520667437951842368883 8297281001156927763553325)
              ·
                refine ⟨3111480375433847911332497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8297281001156927763553325 3111480375433847911332497)
                ·
                  refine ⟨2333610281575385933499373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3111480375433847911332497 2333610281575385933499373)
                  ·
                    refine ⟨875103855590769725062265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2333610281575385933499373 875103855590769725062265)
                    ·
                      refine ⟨656327891693077293796699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 875103855590769725062265 656327891693077293796699)
                      ·
                        rfl

theorem cell23_1278194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 3, 2, 3, 2].length) (baseStart_1278194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1278194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1278194 prefixEnd_1278194 := by exact prefixLift 1278194
  have htrace : WordTrace (prefixWord ++ tailWord_1278194) baseStart_1278194 baseEnd_1278194 := by
    simpa [prefixWord, tailWord_1278194, baseEnd_1278194] using wordTrace_append hprefix tailTrace_1278194
  have hstable : (prefixWord ++ tailWord_1278194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278194).length < 2 ^ (prefixWord ++ tailWord_1278194).sum := by decide
  have hdescent : baseEnd_1278194 < baseStart_1278194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278200 : List Nat := [2, 1, 2, 1, 1, 2, 1, 3, 6, 4]
def baseStart_1278200 : Nat := 118140960795 + 1278200 * 2 ^ 59
def prefixEnd_1278200 : Nat := 4983230072969 + 3 ^ 40 * 1278200 * 2
def baseEnd_1278200 : Nat := 218776990859001423440557

theorem tailTrace_1278200 : CollatzResearch.WordTrace tailWord_1278200 prefixEnd_1278200 218776990859001423440557 := by
  unfold tailWord_1278200
  simp only [CollatzResearch.WordTrace]
  refine ⟨23309891984653587012712027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31079855979538116016949369 23309891984653587012712027)
  ·
    refine ⟨34964837976980380519068041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23309891984653587012712027 34964837976980380519068041)
    ·
      refine ⟨26223628482735285389301031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34964837976980380519068041 26223628482735285389301031)
      ·
        refine ⟨39335442724102928083951547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26223628482735285389301031 39335442724102928083951547)
        ·
          refine ⟨59003164086154392125927321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39335442724102928083951547 59003164086154392125927321)
          ·
            refine ⟨44252373064615794094445491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59003164086154392125927321 44252373064615794094445491)
            ·
              refine ⟨66378559596923691141668237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44252373064615794094445491 66378559596923691141668237)
              ·
                refine ⟨24891959848846384178125589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66378559596923691141668237 24891959848846384178125589)
                ·
                  refine ⟨1166810617914674258349637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 24891959848846384178125589 1166810617914674258349637)
                  ·
                    refine ⟨218776990859001423440557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1166810617914674258349637 218776990859001423440557)
                    ·
                      rfl

theorem cell23_1278200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 6, 4].length) (baseStart_1278200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1278200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1278200 prefixEnd_1278200 := by exact prefixLift 1278200
  have htrace : WordTrace (prefixWord ++ tailWord_1278200) baseStart_1278200 baseEnd_1278200 := by
    simpa [prefixWord, tailWord_1278200, baseEnd_1278200] using wordTrace_append hprefix tailTrace_1278200
  have hstable : (prefixWord ++ tailWord_1278200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278200).length < 2 ^ (prefixWord ++ tailWord_1278200).sum := by decide
  have hdescent : baseEnd_1278200 < baseStart_1278200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278203 : List Nat := [1, 1, 1, 1, 1, 3, 1, 1, 2, 5, 6]
def baseStart_1278203 : Nat := 118140960795 + 1278203 * 2 ^ 59
def prefixEnd_1278203 : Nat := 4983230072969 + 3 ^ 40 * 1278203 * 2
def baseEnd_1278203 : Nat := 656332513018967758584157

theorem tailTrace_1278203 : CollatzResearch.WordTrace tailWord_1278203 prefixEnd_1278203 656332513018967758584157 := by
  unfold tailWord_1278203
  simp only [CollatzResearch.WordTrace]
  refine ⟨46619893388296305537783263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31079928925530870358522175 46619893388296305537783263)
  ·
    refine ⟨69929840082444458306674895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46619893388296305537783263 69929840082444458306674895)
    ·
      refine ⟨104894760123666687460012343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69929840082444458306674895 104894760123666687460012343)
      ·
        refine ⟨157342140185500031190018515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104894760123666687460012343 157342140185500031190018515)
        ·
          refine ⟨236013210278250046785027773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157342140185500031190018515 236013210278250046785027773)
          ·
            refine ⟨88504953854343767544385415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 236013210278250046785027773 88504953854343767544385415)
            ·
              refine ⟨132757430781515651316578123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88504953854343767544385415 132757430781515651316578123)
              ·
                refine ⟨199136146172273476974867185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 132757430781515651316578123 199136146172273476974867185)
                ·
                  refine ⟨149352109629205107731150389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 199136146172273476974867185 149352109629205107731150389)
                  ·
                    refine ⟨14001760277737978849795349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 149352109629205107731150389 14001760277737978849795349)
                    ·
                      refine ⟨656332513018967758584157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14001760277737978849795349 656332513018967758584157)
                      ·
                        rfl

theorem cell23_1278203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 5, 6].length) (baseStart_1278203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1278203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1278203 prefixEnd_1278203 := by exact prefixLift 1278203
  have htrace : WordTrace (prefixWord ++ tailWord_1278203) baseStart_1278203 baseEnd_1278203 := by
    simpa [prefixWord, tailWord_1278203, baseEnd_1278203] using wordTrace_append hprefix tailTrace_1278203
  have hstable : (prefixWord ++ tailWord_1278203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278203).length < 2 ^ (prefixWord ++ tailWord_1278203).sum := by decide
  have hdescent : baseEnd_1278203 < baseStart_1278203 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278204 : List Nat := [2, 2, 2, 1, 4, 2, 3, 1, 1, 5]
def baseStart_1278204 : Nat := 118140960795 + 1278204 * 2 ^ 59
def prefixEnd_1278204 : Nat := 4983230072969 + 3 ^ 40 * 1278204 * 2
def baseEnd_1278204 : Nat := 218777675499874084890551

theorem tailTrace_1278204 : CollatzResearch.WordTrace tailWord_1278204 prefixEnd_1278204 218777675499874084890551 := by
  unfold tailWord_1278204
  simp only [CollatzResearch.WordTrace]
  refine ⟨23309964930646341354284833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31079953240861788472379777 23309964930646341354284833)
  ·
    refine ⟨17482473697984756015713625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23309964930646341354284833 17482473697984756015713625)
    ·
      refine ⟨13111855273488567011785219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17482473697984756015713625 13111855273488567011785219)
      ·
        refine ⟨19667782910232850517677829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13111855273488567011785219 19667782910232850517677829)
        ·
          refine ⟨3687709295668659472064593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19667782910232850517677829 3687709295668659472064593)
          ·
            refine ⟨2765781971751494604048445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3687709295668659472064593 2765781971751494604048445)
            ·
              refine ⟨1037168239406810476518167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2765781971751494604048445 1037168239406810476518167)
              ·
                refine ⟨1555752359110215714777251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1037168239406810476518167 1555752359110215714777251)
                ·
                  refine ⟨2333628538665323572165877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1555752359110215714777251 2333628538665323572165877)
                  ·
                    refine ⟨218777675499874084890551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2333628538665323572165877 218777675499874084890551)
                    ·
                      rfl

theorem cell23_1278204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 3, 1, 1, 5].length) (baseStart_1278204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1278204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1278204 prefixEnd_1278204 := by exact prefixLift 1278204
  have htrace : WordTrace (prefixWord ++ tailWord_1278204) baseStart_1278204 baseEnd_1278204 := by
    simpa [prefixWord, tailWord_1278204, baseEnd_1278204] using wordTrace_append hprefix tailTrace_1278204
  have hstable : (prefixWord ++ tailWord_1278204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278204).length < 2 ^ (prefixWord ++ tailWord_1278204).sum := by decide
  have hdescent : baseEnd_1278204 < baseStart_1278204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278217 : List Nat := [1, 2, 1, 1, 3, 4, 1, 4, 2, 4]
def baseStart_1278217 : Nat := 118140960795 + 1278217 * 2 ^ 59
def prefixEnd_1278217 : Nat := 4983230072969 + 3 ^ 40 * 1278217 * 2
def baseEnd_1278217 : Nat := 218779900582710234603031

theorem tailTrace_1278217 : CollatzResearch.WordTrace tailWord_1278217 prefixEnd_1278217 218779900582710234603031 := by
  unfold tailWord_1278217
  simp only [CollatzResearch.WordTrace]
  refine ⟨46620404010245585928792905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31080269340163723952528603 46620404010245585928792905)
  ·
    refine ⟨34965303007684189446594679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46620404010245585928792905 34965303007684189446594679)
    ·
      refine ⟨52447954511526284169892019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34965303007684189446594679 52447954511526284169892019)
      ·
        refine ⟨78671931767289426254838029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52447954511526284169892019 78671931767289426254838029)
        ·
          refine ⟨29501974412733534845564261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78671931767289426254838029 29501974412733534845564261)
          ·
            refine ⟨5531620202387537783543299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29501974412733534845564261 5531620202387537783543299)
            ·
              refine ⟨8297430303581306675314949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5531620202387537783543299 8297430303581306675314949)
              ·
                refine ⟨1555768181921495001621553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8297430303581306675314949 1555768181921495001621553)
                ·
                  refine ⟨1166826136441121251216165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1555768181921495001621553 1166826136441121251216165)
                  ·
                    refine ⟨218779900582710234603031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1166826136441121251216165 218779900582710234603031)
                    ·
                      rfl

theorem cell23_1278217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 4, 2, 4].length) (baseStart_1278217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1278217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1278217 prefixEnd_1278217 := by exact prefixLift 1278217
  have htrace : WordTrace (prefixWord ++ tailWord_1278217) baseStart_1278217 baseEnd_1278217 := by
    simpa [prefixWord, tailWord_1278217, baseEnd_1278217] using wordTrace_append hprefix tailTrace_1278217
  have hstable : (prefixWord ++ tailWord_1278217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278217).length < 2 ^ (prefixWord ++ tailWord_1278217).sum := by decide
  have hdescent : baseEnd_1278217 < baseStart_1278217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278220 : List Nat := [2, 2, 1, 2, 2, 2, 1, 2, 3, 2, 4]
def baseStart_1278220 : Nat := 118140960795 + 1278220 * 2 ^ 59
def prefixEnd_1278220 : Nat := 4983230072969 + 3 ^ 40 * 1278220 * 2
def baseEnd_1278220 : Nat := 656341242190094192071579

theorem tailTrace_1278220 : CollatzResearch.WordTrace tailWord_1278220 prefixEnd_1278220 656341242190094192071579 := by
  unfold tailWord_1278220
  simp only [CollatzResearch.WordTrace]
  refine ⟨23310256714617358720576057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31080342286156478294101409 23310256714617358720576057)
  ·
    refine ⟨17482692535963019040432043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23310256714617358720576057 17482692535963019040432043)
    ·
      refine ⟨26224038803944528560648065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17482692535963019040432043 26224038803944528560648065)
      ·
        refine ⟨19668029102958396420486049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26224038803944528560648065 19668029102958396420486049)
        ·
          refine ⟨14751021827218797315364537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19668029102958396420486049 14751021827218797315364537)
          ·
            refine ⟨11063266370414097986523403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14751021827218797315364537 11063266370414097986523403)
            ·
              refine ⟨16594899555621146979785105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11063266370414097986523403 16594899555621146979785105)
              ·
                refine ⟨12446174666715860234838829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16594899555621146979785105 12446174666715860234838829)
                ·
                  refine ⟨4667315500018447588064561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12446174666715860234838829 4667315500018447588064561)
                  ·
                    refine ⟨3500486625013835691048421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4667315500018447588064561 3500486625013835691048421)
                    ·
                      refine ⟨656341242190094192071579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3500486625013835691048421 656341242190094192071579)
                      ·
                        rfl

theorem cell23_1278220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 3, 2, 4].length) (baseStart_1278220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1278220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1278220 prefixEnd_1278220 := by exact prefixLift 1278220
  have htrace : WordTrace (prefixWord ++ tailWord_1278220) baseStart_1278220 baseEnd_1278220 := by
    simpa [prefixWord, tailWord_1278220, baseEnd_1278220] using wordTrace_append hprefix tailTrace_1278220
  have hstable : (prefixWord ++ tailWord_1278220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278220).length < 2 ^ (prefixWord ++ tailWord_1278220).sum := by decide
  have hdescent : baseEnd_1278220 < baseStart_1278220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278258 : List Nat := [3, 2, 1, 1, 6, 1, 2, 1, 1, 1, 4]
def baseStart_1278258 : Nat := 118140960795 + 1278258 * 2 ^ 59
def prefixEnd_1278258 : Nat := 4983230072969 + 3 ^ 40 * 1278258 * 2
def baseEnd_1278258 : Nat := 656360754454965043396405

theorem tailTrace_1278258 : CollatzResearch.WordTrace tailWord_1278258 prefixEnd_1278258 656360754454965043396405 := by
  unfold tailWord_1278258
  simp only [CollatzResearch.WordTrace]
  refine ⟨11655474850774262482758857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31081266268731366620690285 11655474850774262482758857)
  ·
    refine ⟨8741606138080696862069143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11655474850774262482758857 8741606138080696862069143)
    ·
      refine ⟨13112409207121045293103715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8741606138080696862069143 13112409207121045293103715)
      ·
        refine ⟨19668613810681567939655573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13112409207121045293103715 19668613810681567939655573)
        ·
          refine ⟨921966272375698497171355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 19668613810681567939655573 921966272375698497171355)
          ·
            refine ⟨1382949408563547745757033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 921966272375698497171355 1382949408563547745757033)
            ·
              refine ⟨1037212056422660809317775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1382949408563547745757033 1037212056422660809317775)
              ·
                refine ⟨1555818084633991213976663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1037212056422660809317775 1555818084633991213976663)
                ·
                  refine ⟨2333727126950986820964995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1555818084633991213976663 2333727126950986820964995)
                  ·
                    refine ⟨3500590690426480231447493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2333727126950986820964995 3500590690426480231447493)
                    ·
                      refine ⟨656360754454965043396405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3500590690426480231447493 656360754454965043396405)
                      ·
                        rfl

theorem cell23_1278258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 2, 1, 1, 1, 4].length) (baseStart_1278258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1278258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1278258 prefixEnd_1278258 := by exact prefixLift 1278258
  have htrace : WordTrace (prefixWord ++ tailWord_1278258) baseStart_1278258 baseEnd_1278258 := by
    simpa [prefixWord, tailWord_1278258, baseEnd_1278258] using wordTrace_append hprefix tailTrace_1278258
  have hstable : (prefixWord ++ tailWord_1278258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278258).length < 2 ^ (prefixWord ++ tailWord_1278258).sum := by decide
  have hdescent : baseEnd_1278258 < baseStart_1278258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278280 : List Nat := [2, 1, 3, 1, 1, 2, 2, 1, 1, 5, 4]
def baseStart_1278280 : Nat := 118140960795 + 1278280 * 2 ^ 59
def prefixEnd_1278280 : Nat := 4983230072969 + 3 ^ 40 * 1278280 * 2
def baseEnd_1278280 : Nat := 656372051029363957321303

theorem tailTrace_1278280 : CollatzResearch.WordTrace tailWord_1278280 prefixEnd_1278280 656372051029363957321303 := by
  unfold tailWord_1278280
  simp only [CollatzResearch.WordTrace]
  refine ⟨23311350904508673844168147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31081801206011565125557529 23311350904508673844168147)
  ·
    refine ⟨34967026356763010766252221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23311350904508673844168147 34967026356763010766252221)
    ·
      refine ⟨13112634883786129037344583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34967026356763010766252221 13112634883786129037344583)
      ·
        refine ⟨19668952325679193556016875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13112634883786129037344583 19668952325679193556016875)
        ·
          refine ⟨29503428488518790334025313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19668952325679193556016875 29503428488518790334025313)
          ·
            refine ⟨22127571366389092750518985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29503428488518790334025313 22127571366389092750518985)
            ·
              refine ⟨16595678524791819562889239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22127571366389092750518985 16595678524791819562889239)
              ·
                refine ⟨24893517787187729344333859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16595678524791819562889239 24893517787187729344333859)
                ·
                  refine ⟨37340276680781594016500789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24893517787187729344333859 37340276680781594016500789)
                  ·
                    refine ⟨3500650938823274439046949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37340276680781594016500789 3500650938823274439046949)
                    ·
                      refine ⟨656372051029363957321303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3500650938823274439046949 656372051029363957321303)
                      ·
                        rfl

theorem cell23_1278280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 1, 5, 4].length) (baseStart_1278280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1278280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1278280 prefixEnd_1278280 := by exact prefixLift 1278280
  have htrace : WordTrace (prefixWord ++ tailWord_1278280) baseStart_1278280 baseEnd_1278280 := by
    simpa [prefixWord, tailWord_1278280, baseEnd_1278280] using wordTrace_append hprefix tailTrace_1278280
  have hstable : (prefixWord ++ tailWord_1278280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278280).length < 2 ^ (prefixWord ++ tailWord_1278280).sum := by decide
  have hdescent : baseEnd_1278280 < baseStart_1278280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278317 : List Nat := [1, 5, 1, 1, 1, 2, 3, 1, 2, 1, 5]
def baseStart_1278317 : Nat := 118140960795 + 1278317 * 2 ^ 59
def prefixEnd_1278317 : Nat := 4983230072969 + 3 ^ 40 * 1278317 * 2
def baseEnd_1278317 : Nat := 656391049813580312558633

theorem tailTrace_1278317 : CollatzResearch.WordTrace tailWord_1278317 prefixEnd_1278317 656391049813580312558633 := by
  unfold tailWord_1278317
  simp only [CollatzResearch.WordTrace]
  refine ⟨46624051309883303007433205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31082700873255535338288803 46624051309883303007433205)
  ·
    refine ⟨4371004810301559656946863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46624051309883303007433205 4371004810301559656946863)
    ·
      refine ⟨6556507215452339485420295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4371004810301559656946863 6556507215452339485420295)
      ·
        refine ⟨9834760823178509228130443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6556507215452339485420295 9834760823178509228130443)
        ·
          refine ⟨14752141234767763842195665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9834760823178509228130443 14752141234767763842195665)
          ·
            refine ⟨11064105926075822881646749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14752141234767763842195665 11064105926075822881646749)
            ·
              refine ⟨4149039722278433580617531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11064105926075822881646749 4149039722278433580617531)
              ·
                refine ⟨6223559583417650370926297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4149039722278433580617531 6223559583417650370926297)
                ·
                  refine ⟨4667669687563237778194723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6223559583417650370926297 4667669687563237778194723)
                  ·
                    refine ⟨7001504531344856667292085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4667669687563237778194723 7001504531344856667292085)
                    ·
                      refine ⟨656391049813580312558633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7001504531344856667292085 656391049813580312558633)
                      ·
                        rfl

theorem cell23_1278317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_1278317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1278317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1278317 prefixEnd_1278317 := by exact prefixLift 1278317
  have htrace : WordTrace (prefixWord ++ tailWord_1278317) baseStart_1278317 baseEnd_1278317 := by
    simpa [prefixWord, tailWord_1278317, baseEnd_1278317] using wordTrace_append hprefix tailTrace_1278317
  have hstable : (prefixWord ++ tailWord_1278317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278317).length < 2 ^ (prefixWord ++ tailWord_1278317).sum := by decide
  have hdescent : baseEnd_1278317 < baseStart_1278317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278348 : List Nat := [2, 2, 1, 2, 1, 4, 4, 1, 2, 2, 2]
def baseStart_1278348 : Nat := 118140960795 + 1278348 * 2 ^ 59
def prefixEnd_1278348 : Nat := 4983230072969 + 3 ^ 40 * 1278348 * 2
def baseEnd_1278348 : Nat := 656406967713869691270991

theorem tailTrace_1278348 : CollatzResearch.WordTrace tailWord_1278348 prefixEnd_1278348 656406967713869691270991 := by
  unfold tailWord_1278348
  simp only [CollatzResearch.WordTrace]
  refine ⟨23312590986385497650905849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31083454648513996867874465 23312590986385497650905849)
  ·
    refine ⟨17484443239789123238179387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23312590986385497650905849 17484443239789123238179387)
    ·
      refine ⟨26226664859683684857269081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17484443239789123238179387 26226664859683684857269081)
      ·
        refine ⟨19669998644762763642951811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26226664859683684857269081 19669998644762763642951811)
        ·
          refine ⟨29504997967144145464427717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19669998644762763642951811 29504997967144145464427717)
          ·
            refine ⟨5532187118839527274580197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29504997967144145464427717 5532187118839527274580197)
            ·
              refine ⟨1037285084782411363983787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5532187118839527274580197 1037285084782411363983787)
              ·
                refine ⟨1555927627173617045975681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1037285084782411363983787 1555927627173617045975681)
                ·
                  refine ⟨1166945720380212784481761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1555927627173617045975681 1166945720380212784481761)
                  ·
                    refine ⟨875209290285159588361321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1166945720380212784481761 875209290285159588361321)
                    ·
                      refine ⟨656406967713869691270991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 875209290285159588361321 656406967713869691270991)
                      ·
                        rfl

theorem cell23_1278348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 4, 1, 2, 2, 2].length) (baseStart_1278348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1278348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1278348 prefixEnd_1278348 := by exact prefixLift 1278348
  have htrace : WordTrace (prefixWord ++ tailWord_1278348) baseStart_1278348 baseEnd_1278348 := by
    simpa [prefixWord, tailWord_1278348, baseEnd_1278348] using wordTrace_append hprefix tailTrace_1278348
  have hstable : (prefixWord ++ tailWord_1278348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278348).length < 2 ^ (prefixWord ++ tailWord_1278348).sum := by decide
  have hdescent : baseEnd_1278348 < baseStart_1278348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278418 : List Nat := [3, 2, 2, 4, 1, 2, 1, 1, 2, 5]
def baseStart_1278418 : Nat := 118140960795 + 1278418 * 2 ^ 59
def prefixEnd_1278418 : Nat := 4983230072969 + 3 ^ 40 * 1278418 * 2
def baseEnd_1278418 : Nat := 218814303786561472465223

theorem tailTrace_1278418 : CollatzResearch.WordTrace tailWord_1278418 prefixEnd_1278418 218814303786561472465223 := by
  unfold tailWord_1278418
  simp only [CollatzResearch.WordTrace]
  refine ⟨11656933770629349314214977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31085156721678264837906605 11656933770629349314214977)
  ·
    refine ⟨8742700327972011985661233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11656933770629349314214977 8742700327972011985661233)
    ·
      refine ⟨6557025245979008989245925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8742700327972011985661233 6557025245979008989245925)
      ·
        refine ⟨1229442233621064185483611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6557025245979008989245925 1229442233621064185483611)
        ·
          refine ⟨1844163350431596278225417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1229442233621064185483611 1844163350431596278225417)
          ·
            refine ⟨1383122512823697208669063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1844163350431596278225417 1383122512823697208669063)
            ·
              refine ⟨2074683769235545813003595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1383122512823697208669063 2074683769235545813003595)
              ·
                refine ⟨3112025653853318719505393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2074683769235545813003595 3112025653853318719505393)
                ·
                  refine ⟨2334019240389989039629045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3112025653853318719505393 2334019240389989039629045)
                  ·
                    refine ⟨218814303786561472465223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2334019240389989039629045 218814303786561472465223)
                    ·
                      rfl

theorem cell23_1278418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 1, 2, 5].length) (baseStart_1278418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1278418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1278418 prefixEnd_1278418 := by exact prefixLift 1278418
  have htrace : WordTrace (prefixWord ++ tailWord_1278418) baseStart_1278418 baseEnd_1278418 := by
    simpa [prefixWord, tailWord_1278418, baseEnd_1278418] using wordTrace_append hprefix tailTrace_1278418
  have hstable : (prefixWord ++ tailWord_1278418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278418).length < 2 ^ (prefixWord ++ tailWord_1278418).sum := by decide
  have hdescent : baseEnd_1278418 < baseStart_1278418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278421 : List Nat := [1, 3, 2, 3, 1, 4, 1, 1, 2, 1, 4]
def baseStart_1278421 : Nat := 118140960795 + 1278421 * 2 ^ 59
def prefixEnd_1278421 : Nat := 4983230072969 + 3 ^ 40 * 1278421 * 2
def baseEnd_1278421 : Nat := 656444451801647905658155

theorem tailTrace_1278421 : CollatzResearch.WordTrace tailWord_1278421 prefixEnd_1278421 656444451801647905658155 := by
  unfold tailWord_1278421
  simp only [CollatzResearch.WordTrace]
  refine ⟨46627844501506528769219117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31085229667671019179479411 46627844501506528769219117)
  ·
    refine ⟨17485441688064948288457169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46627844501506528769219117 17485441688064948288457169)
    ·
      refine ⟨13114081266048711216342877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17485441688064948288457169 13114081266048711216342877)
      ·
        refine ⟨4917780474768266706128579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13114081266048711216342877 4917780474768266706128579)
        ·
          refine ⟨7376670712152400059192869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4917780474768266706128579 7376670712152400059192869)
          ·
            refine ⟨1383125758528575011098663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7376670712152400059192869 1383125758528575011098663)
            ·
              refine ⟨2074688637792862516647995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1383125758528575011098663 2074688637792862516647995)
              ·
                refine ⟨3112032956689293774971993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2074688637792862516647995 3112032956689293774971993)
                ·
                  refine ⟨2334024717516970331228995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3112032956689293774971993 2334024717516970331228995)
                  ·
                    refine ⟨3501037076275455496843493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2334024717516970331228995 3501037076275455496843493)
                    ·
                      refine ⟨656444451801647905658155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3501037076275455496843493 656444451801647905658155)
                      ·
                        rfl

theorem cell23_1278421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 1, 2, 1, 4].length) (baseStart_1278421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1278421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1278421 prefixEnd_1278421 := by exact prefixLift 1278421
  have htrace : WordTrace (prefixWord ++ tailWord_1278421) baseStart_1278421 baseEnd_1278421 := by
    simpa [prefixWord, tailWord_1278421, baseEnd_1278421] using wordTrace_append hprefix tailTrace_1278421
  have hstable : (prefixWord ++ tailWord_1278421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278421).length < 2 ^ (prefixWord ++ tailWord_1278421).sum := by decide
  have hdescent : baseEnd_1278421 < baseStart_1278421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278431 : List Nat := [1, 1, 2, 3, 3, 2, 1, 5, 1, 4]
def baseStart_1278431 : Nat := 118140960795 + 1278431 * 2 ^ 59
def prefixEnd_1278431 : Nat := 4983230072969 + 3 ^ 40 * 1278431 * 2
def baseEnd_1278431 : Nat := 218816528869397622177703

theorem tailTrace_1278431 : CollatzResearch.WordTrace tailWord_1278431 prefixEnd_1278431 218816528869397622177703 := by
  unfold tailWord_1278431
  simp only [CollatzResearch.WordTrace]
  refine ⟨46628209231470300477083147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31085472820980200318055431 46628209231470300477083147)
  ·
    refine ⟨69942313847205450715624721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46628209231470300477083147 69942313847205450715624721)
    ·
      refine ⟨52456735385404088036718541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69942313847205450715624721 52456735385404088036718541)
      ·
        refine ⟨19671275769526533013769453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52456735385404088036718541 19671275769526533013769453)
        ·
          refine ⟨7376728413572449880163545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19671275769526533013769453 7376728413572449880163545)
          ·
            refine ⟨5532546310179337410122659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7376728413572449880163545 5532546310179337410122659)
            ·
              refine ⟨8298819465269006115183989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5532546310179337410122659 8298819465269006115183989)
              ·
                refine ⟨778014324868969323298499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8298819465269006115183989 778014324868969323298499)
                ·
                  refine ⟨1167021487303453984947749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 778014324868969323298499 1167021487303453984947749)
                  ·
                    refine ⟨218816528869397622177703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1167021487303453984947749 218816528869397622177703)
                    ·
                      rfl

theorem cell23_1278431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 5, 1, 4].length) (baseStart_1278431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1278431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1278431 prefixEnd_1278431 := by exact prefixLift 1278431
  have htrace : WordTrace (prefixWord ++ tailWord_1278431) baseStart_1278431 baseEnd_1278431 := by
    simpa [prefixWord, tailWord_1278431, baseEnd_1278431] using wordTrace_append hprefix tailTrace_1278431
  have hstable : (prefixWord ++ tailWord_1278431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278431).length < 2 ^ (prefixWord ++ tailWord_1278431).sum := by decide
  have hdescent : baseEnd_1278431 < baseStart_1278431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278457 : List Nat := [1, 2, 1, 3, 1, 2, 2, 1, 5, 5]
def baseStart_1278457 : Nat := 118140960795 + 1278457 * 2 ^ 59
def prefixEnd_1278457 : Nat := 4983230072969 + 3 ^ 40 * 1278457 * 2
def baseEnd_1278457 : Nat := 218820979035069921602663

theorem tailTrace_1278457 : CollatzResearch.WordTrace tailWord_1278457 prefixEnd_1278457 218820979035069921602663 := by
  unfold tailWord_1278457
  simp only [CollatzResearch.WordTrace]
  refine ⟨46629157529376106917529625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31086105019584071278353083 46629157529376106917529625)
  ·
    refine ⟨34971868147032080188147219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46629157529376106917529625 34971868147032080188147219)
    ·
      refine ⟨52457802220548120282220829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34971868147032080188147219 52457802220548120282220829)
      ·
        refine ⟨19671675832705545105832811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52457802220548120282220829 19671675832705545105832811)
        ·
          refine ⟨29507513749058317658749217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19671675832705545105832811 29507513749058317658749217)
          ·
            refine ⟨22130635311793738244061913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29507513749058317658749217 22130635311793738244061913)
            ·
              refine ⟨16597976483845303683046435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22130635311793738244061913 16597976483845303683046435)
              ·
                refine ⟨24896964725767955524569653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16597976483845303683046435 24896964725767955524569653)
                ·
                  refine ⟨2334090443040745830428405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24896964725767955524569653 2334090443040745830428405)
                  ·
                    refine ⟨218820979035069921602663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2334090443040745830428405 218820979035069921602663)
                    ·
                      rfl

theorem cell23_1278457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 5, 5].length) (baseStart_1278457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1278457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1278457 prefixEnd_1278457 := by exact prefixLift 1278457
  have htrace : WordTrace (prefixWord ++ tailWord_1278457) baseStart_1278457 baseEnd_1278457 := by
    simpa [prefixWord, tailWord_1278457, baseEnd_1278457] using wordTrace_append hprefix tailTrace_1278457
  have hstable : (prefixWord ++ tailWord_1278457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278457).length < 2 ^ (prefixWord ++ tailWord_1278457).sum := by decide
  have hdescent : baseEnd_1278457 < baseStart_1278457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278514 : List Nat := [3, 2, 1, 1, 2, 1, 4, 2, 1, 1, 5]
def baseStart_1278514 : Nat := 118140960795 + 1278514 * 2 ^ 59
def prefixEnd_1278514 : Nat := 4983230072969 + 3 ^ 40 * 1278514 * 2
def baseEnd_1278514 : Nat := 656492205502516041795227

theorem tailTrace_1278514 : CollatzResearch.WordTrace tailWord_1278514 prefixEnd_1278514 656492205502516041795227 := by
  unfold tailWord_1278514
  simp only [CollatzResearch.WordTrace]
  refine ⟨11657809122542401413088649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31087490993446403768236397 11657809122542401413088649)
  ·
    refine ⟨8743356841906801059816487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11657809122542401413088649 8743356841906801059816487)
    ·
      refine ⟨13115035262860201589724731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8743356841906801059816487 13115035262860201589724731)
      ·
        refine ⟨19672552894290302384587097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13115035262860201589724731 19672552894290302384587097)
        ·
          refine ⟨14754414670717726788440323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19672552894290302384587097 14754414670717726788440323)
          ·
            refine ⟨22131622006076590182660485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14754414670717726788440323 22131622006076590182660485)
            ·
              refine ⟨4149679126139360659248841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22131622006076590182660485 4149679126139360659248841)
              ·
                refine ⟨3112259344604520494436631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4149679126139360659248841 3112259344604520494436631)
                ·
                  refine ⟨4668389016906780741654947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3112259344604520494436631 4668389016906780741654947)
                  ·
                    refine ⟨7002583525360171112482421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4668389016906780741654947 7002583525360171112482421)
                    ·
                      refine ⟨656492205502516041795227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7002583525360171112482421 656492205502516041795227)
                      ·
                        rfl

theorem cell23_1278514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 2, 1, 1, 5].length) (baseStart_1278514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1278514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1278514 prefixEnd_1278514 := by exact prefixLift 1278514
  have htrace : WordTrace (prefixWord ++ tailWord_1278514) baseStart_1278514 baseEnd_1278514 := by
    simpa [prefixWord, tailWord_1278514, baseEnd_1278514] using wordTrace_append hprefix tailTrace_1278514
  have hstable : (prefixWord ++ tailWord_1278514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278514).length < 2 ^ (prefixWord ++ tailWord_1278514).sum := by decide
  have hdescent : baseEnd_1278514 < baseStart_1278514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278521 : List Nat := [1, 2, 1, 5, 1, 1, 3, 3, 2, 4]
def baseStart_1278521 : Nat := 118140960795 + 1278521 * 2 ^ 59
def prefixEnd_1278521 : Nat := 4983230072969 + 3 ^ 40 * 1278521 * 2
def baseEnd_1278521 : Nat := 218831933289032504802565

theorem tailTrace_1278521 : CollatzResearch.WordTrace tailWord_1278521 prefixEnd_1278521 218831933289032504802565 := by
  unfold tailWord_1278521
  simp only [CollatzResearch.WordTrace]
  refine ⟨46631491801144245847859417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31087661200762830565239611 46631491801144245847859417)
  ·
    refine ⟨34973618850858184385894563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46631491801144245847859417 34973618850858184385894563)
    ·
      refine ⟨52460428276287276578841845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34973618850858184385894563 52460428276287276578841845)
      ·
        refine ⟨4918165150901932179266423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 52460428276287276578841845 4918165150901932179266423)
        ·
          refine ⟨7377247726352898268899635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4918165150901932179266423 7377247726352898268899635)
          ·
            refine ⟨11065871589529347403349453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7377247726352898268899635 11065871589529347403349453)
            ·
              refine ⟨4149701846073505276256045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11065871589529347403349453 4149701846073505276256045)
              ·
                refine ⟨1556138192277564478596017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4149701846073505276256045 1556138192277564478596017)
                ·
                  refine ⟨1167103644208173358947013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1556138192277564478596017 1167103644208173358947013)
                  ·
                    refine ⟨218831933289032504802565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1167103644208173358947013 218831933289032504802565)
                    ·
                      rfl

theorem cell23_1278521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 3, 2, 4].length) (baseStart_1278521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1278521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1278521 prefixEnd_1278521 := by exact prefixLift 1278521
  have htrace : WordTrace (prefixWord ++ tailWord_1278521) baseStart_1278521 baseEnd_1278521 := by
    simpa [prefixWord, tailWord_1278521, baseEnd_1278521] using wordTrace_append hprefix tailTrace_1278521
  have hstable : (prefixWord ++ tailWord_1278521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278521).length < 2 ^ (prefixWord ++ tailWord_1278521).sum := by decide
  have hdescent : baseEnd_1278521 < baseStart_1278521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278524 : List Nat := [2, 2, 2, 2, 3, 1, 2, 1, 1, 1, 6]
def baseStart_1278524 : Nat := 118140960795 + 1278524 * 2 ^ 59
def prefixEnd_1278524 : Nat := 4983230072969 + 3 ^ 40 * 1278524 * 2
def baseEnd_1278524 : Nat := 656497340309061002670181

theorem tailTrace_1278524 : CollatzResearch.WordTrace tailWord_1278524 prefixEnd_1278524 656497340309061002670181 := by
  unfold tailWord_1278524
  simp only [CollatzResearch.WordTrace]
  refine ⟨23315800610066688680109313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31087734146755584906812417 23315800610066688680109313)
  ·
    refine ⟨17486850457550016510081985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23315800610066688680109313 17486850457550016510081985)
    ·
      refine ⟨13115137843162512382561489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17486850457550016510081985 13115137843162512382561489)
      ·
        refine ⟨9836353382371884286921117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13115137843162512382561489 9836353382371884286921117)
        ·
          refine ⟨3688632518389456607595419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9836353382371884286921117 3688632518389456607595419)
          ·
            refine ⟨5532948777584184911393129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3688632518389456607595419 5532948777584184911393129)
            ·
              refine ⟨4149711583188138683544847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5532948777584184911393129 4149711583188138683544847)
              ·
                refine ⟨6224567374782208025317271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4149711583188138683544847 6224567374782208025317271)
                ·
                  refine ⟨9336851062173312037975907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6224567374782208025317271 9336851062173312037975907)
                  ·
                    refine ⟨14005276593259968056963861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9336851062173312037975907 14005276593259968056963861)
                    ·
                      refine ⟨656497340309061002670181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14005276593259968056963861 656497340309061002670181)
                      ·
                        rfl

theorem cell23_1278524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_1278524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1278524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1278524 prefixEnd_1278524 := by exact prefixLift 1278524
  have htrace : WordTrace (prefixWord ++ tailWord_1278524) baseStart_1278524 baseEnd_1278524 := by
    simpa [prefixWord, tailWord_1278524, baseEnd_1278524] using wordTrace_append hprefix tailTrace_1278524
  have hstable : (prefixWord ++ tailWord_1278524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278524).length < 2 ^ (prefixWord ++ tailWord_1278524).sum := by decide
  have hdescent : baseEnd_1278524 < baseStart_1278524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278541 : List Nat := [1, 6, 1, 1, 2, 1, 1, 1, 3, 2, 4]
def baseStart_1278541 : Nat := 118140960795 + 1278541 * 2 ^ 59
def prefixEnd_1278541 : Nat := 4983230072969 + 3 ^ 40 * 1278541 * 2
def baseEnd_1278541 : Nat := 656506069480187436157603

theorem tailTrace_1278541 : CollatzResearch.WordTrace tailWord_1278541 prefixEnd_1278541 656506069480187436157603 := by
  unfold tailWord_1278541
  simp only [CollatzResearch.WordTrace]
  refine ⟨46632221261071789263587477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31088147507381192842391651 46632221261071789263587477)
  ·
    refine ⟨2185885371612740121730663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 46632221261071789263587477 2185885371612740121730663)
    ·
      refine ⟨3278828057419110182595995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2185885371612740121730663 3278828057419110182595995)
      ·
        refine ⟨4918242086128665273893993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3278828057419110182595995 4918242086128665273893993)
        ·
          refine ⟨3688681564596498955420495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4918242086128665273893993 3688681564596498955420495)
          ·
            refine ⟨5533022346894748433130743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3688681564596498955420495 5533022346894748433130743)
            ·
              refine ⟨8299533520342122649696115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5533022346894748433130743 8299533520342122649696115)
              ·
                refine ⟨12449300280513183974544173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8299533520342122649696115 12449300280513183974544173)
                ·
                  refine ⟨4668487605192443990454065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12449300280513183974544173 4668487605192443990454065)
                  ·
                    refine ⟨3501365703894332992840549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4668487605192443990454065 3501365703894332992840549)
                    ·
                      refine ⟨656506069480187436157603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3501365703894332992840549 656506069480187436157603)
                      ·
                        rfl

theorem cell23_1278541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_1278541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1278541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1278541 prefixEnd_1278541 := by exact prefixLift 1278541
  have htrace : WordTrace (prefixWord ++ tailWord_1278541) baseStart_1278541 baseEnd_1278541 := by
    simpa [prefixWord, tailWord_1278541, baseEnd_1278541] using wordTrace_append hprefix tailTrace_1278541
  have hstable : (prefixWord ++ tailWord_1278541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278541).length < 2 ^ (prefixWord ++ tailWord_1278541).sum := by decide
  have hdescent : baseEnd_1278541 < baseStart_1278541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278568 : List Nat := [2, 1, 4, 3, 3, 1, 1, 8]
def baseStart_1278568 : Nat := 118140960795 + 1278568 * 2 ^ 59
def prefixEnd_1278568 : Nat := 4983230072969 + 3 ^ 40 * 1278568 * 2
def baseEnd_1278568 : Nat := 24315553091031808537777

theorem tailTrace_1278568 : CollatzResearch.WordTrace tailWord_1278568 prefixEnd_1278568 24315553091031808537777 := by
  unfold tailWord_1278568
  simp only [CollatzResearch.WordTrace]
  refine ⟨23316603015986986437410179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31088804021315981916546905 23316603015986986437410179)
  ·
    refine ⟨34974904523980479656115269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23316603015986986437410179 34974904523980479656115269)
    ·
      refine ⟨6557794598246339935521613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34974904523980479656115269 6557794598246339935521613)
      ·
        refine ⟨2459172974342377475820605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6557794598246339935521613 2459172974342377475820605)
        ·
          refine ⟨922189865378391553432727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2459172974342377475820605 922189865378391553432727)
          ·
            refine ⟨1383284798067587330149091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 922189865378391553432727 1383284798067587330149091)
            ·
              refine ⟨2074927197101380995223637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1383284798067587330149091 2074927197101380995223637)
              ·
                refine ⟨24315553091031808537777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2074927197101380995223637 24315553091031808537777)
                ·
                  rfl

theorem cell23_1278568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 8].length) (baseStart_1278568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1278568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1278568 prefixEnd_1278568 := by exact prefixLift 1278568
  have htrace : WordTrace (prefixWord ++ tailWord_1278568) baseStart_1278568 baseEnd_1278568 := by
    simpa [prefixWord, tailWord_1278568, baseEnd_1278568] using wordTrace_append hprefix tailTrace_1278568
  have hstable : (prefixWord ++ tailWord_1278568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278568).length < 2 ^ (prefixWord ++ tailWord_1278568).sum := by decide
  have hdescent : baseEnd_1278568 < baseStart_1278568 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278578 : List Nat := [3, 2, 1, 2, 4, 1, 2, 1, 1, 3, 3]
def baseStart_1278578 : Nat := 118140960795 + 1278578 * 2 ^ 59
def prefixEnd_1278578 : Nat := 4983230072969 + 3 ^ 40 * 1278578 * 2
def baseEnd_1278578 : Nat := 656525068264403791394933

theorem tailTrace_1278578 : CollatzResearch.WordTrace tailWord_1278578 prefixEnd_1278578 656525068264403791394933 := by
  unfold tailWord_1278578
  simp only [CollatzResearch.WordTrace]
  refine ⟨11658392690484436145671097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31089047174625163055122925 11658392690484436145671097)
  ·
    refine ⟨8743794517863327109253323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11658392690484436145671097 8743794517863327109253323)
    ·
      refine ⟨13115691776794990663879985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8743794517863327109253323 13115691776794990663879985)
      ·
        refine ⟨9836768832596242997909989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13115691776794990663879985 9836768832596242997909989)
        ·
          refine ⟨1844394156111795562108123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9836768832596242997909989 1844394156111795562108123)
          ·
            refine ⟨2766591234167693343162185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1844394156111795562108123 2766591234167693343162185)
            ·
              refine ⟨2074943425625770007371639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2766591234167693343162185 2074943425625770007371639)
              ·
                refine ⟨3112415138438655011057459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2074943425625770007371639 3112415138438655011057459)
                ·
                  refine ⟨4668622707657982516586189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3112415138438655011057459 4668622707657982516586189)
                  ·
                    refine ⟨1750733515371743443719821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4668622707657982516586189 1750733515371743443719821)
                    ·
                      refine ⟨656525068264403791394933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1750733515371743443719821 656525068264403791394933)
                      ·
                        rfl

theorem cell23_1278578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 1, 1, 3, 3].length) (baseStart_1278578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1278578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1278578 prefixEnd_1278578 := by exact prefixLift 1278578
  have htrace : WordTrace (prefixWord ++ tailWord_1278578) baseStart_1278578 baseEnd_1278578 := by
    simpa [prefixWord, tailWord_1278578, baseEnd_1278578] using wordTrace_append hprefix tailTrace_1278578
  have hstable : (prefixWord ++ tailWord_1278578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278578).length < 2 ^ (prefixWord ++ tailWord_1278578).sum := by decide
  have hdescent : baseEnd_1278578 < baseStart_1278578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278604 : List Nat := [2, 2, 1, 2, 1, 1, 2, 2, 1, 6, 3]
def baseStart_1278604 : Nat := 118140960795 + 1278604 * 2 ^ 59
def prefixEnd_1278604 : Nat := 4983230072969 + 3 ^ 40 * 1278604 * 2
def baseEnd_1278604 : Nat := 656538418761420689669813

theorem tailTrace_1278604 : CollatzResearch.WordTrace tailWord_1278604 prefixEnd_1278604 656538418761420689669813 := by
  unfold tailWord_1278604
  simp only [CollatzResearch.WordTrace]
  refine ⟨23317259529921775511565433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31089679373229034015420577 23317259529921775511565433)
  ·
    refine ⟨17487944647441331633674075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23317259529921775511565433 17487944647441331633674075)
    ·
      refine ⟨26231916971161997450511113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17487944647441331633674075 26231916971161997450511113)
      ·
        refine ⟨19673937728371498087883335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26231916971161997450511113 19673937728371498087883335)
        ·
          refine ⟨29510906592557247131825003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19673937728371498087883335 29510906592557247131825003)
          ·
            refine ⟨44266359888835870697737505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29510906592557247131825003 44266359888835870697737505)
            ·
              refine ⟨33199769916626903023303129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44266359888835870697737505 33199769916626903023303129)
              ·
                refine ⟨24899827437470177267477347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33199769916626903023303129 24899827437470177267477347)
                ·
                  refine ⟨37349741156205265901216021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24899827437470177267477347 37349741156205265901216021)
                  ·
                    refine ⟨1750769116697121839119501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 37349741156205265901216021 1750769116697121839119501)
                    ·
                      refine ⟨656538418761420689669813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1750769116697121839119501 656538418761420689669813)
                      ·
                        rfl

theorem cell23_1278604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 1, 6, 3].length) (baseStart_1278604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1278604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1278604 prefixEnd_1278604 := by exact prefixLift 1278604
  have htrace : WordTrace (prefixWord ++ tailWord_1278604) baseStart_1278604 baseEnd_1278604 := by
    simpa [prefixWord, tailWord_1278604, baseEnd_1278604] using wordTrace_append hprefix tailTrace_1278604
  have hstable : (prefixWord ++ tailWord_1278604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278604).length < 2 ^ (prefixWord ++ tailWord_1278604).sum := by decide
  have hdescent : baseEnd_1278604 < baseStart_1278604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278612 : List Nat := [2, 4, 2, 2, 1, 3, 1, 2, 2, 1, 3]
def baseStart_1278612 : Nat := 118140960795 + 1278612 * 2 ^ 59
def prefixEnd_1278612 : Nat := 4983230072969 + 3 ^ 40 * 1278612 * 2
def baseEnd_1278612 : Nat := 656542526606656658369777

theorem tailTrace_1278612 : CollatzResearch.WordTrace tailWord_1278612 prefixEnd_1278612 656542526606656658369777 := by
  unfold tailWord_1278612
  simp only [CollatzResearch.WordTrace]
  refine ⟨23317405421907284194711045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31089873895876378926281393 23317405421907284194711045)
  ·
    refine ⟨4372013516607615786508321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23317405421907284194711045 4372013516607615786508321)
    ·
      refine ⟨3279010137455711839881241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4372013516607615786508321 3279010137455711839881241)
      ·
        refine ⟨2459257603091783879910931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3279010137455711839881241 2459257603091783879910931)
        ·
          refine ⟨3688886404637675819866397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2459257603091783879910931 3688886404637675819866397)
          ·
            refine ⟨1383332401739128432449899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3688886404637675819866397 1383332401739128432449899)
            ·
              refine ⟨2074998602608692648674849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1383332401739128432449899 2074998602608692648674849)
              ·
                refine ⟨1556248951956519486506137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2074998602608692648674849 1556248951956519486506137)
                ·
                  refine ⟨1167186713967389614879603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1556248951956519486506137 1167186713967389614879603)
                  ·
                    refine ⟨1750780070951084422319405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1167186713967389614879603 1750780070951084422319405)
                    ·
                      refine ⟨656542526606656658369777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1750780070951084422319405 656542526606656658369777)
                      ·
                        rfl

theorem cell23_1278612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_1278612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1278612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1278612 prefixEnd_1278612 := by exact prefixLift 1278612
  have htrace : WordTrace (prefixWord ++ tailWord_1278612) baseStart_1278612 baseEnd_1278612 := by
    simpa [prefixWord, tailWord_1278612, baseEnd_1278612] using wordTrace_append hprefix tailTrace_1278612
  have hstable : (prefixWord ++ tailWord_1278612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278612).length < 2 ^ (prefixWord ++ tailWord_1278612).sum := by decide
  have hdescent : baseEnd_1278612 < baseStart_1278612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278714 : List Nat := [3, 1, 1, 1, 1, 3, 2, 1, 10]
def baseStart_1278714 : Nat := 118140960795 + 1278714 * 2 ^ 59
def prefixEnd_1278714 : Nat := 4983230072969 + 3 ^ 40 * 1278714 * 2
def baseEnd_1278714 : Nat := 72954989070379473254923

theorem tailTrace_1278714 : CollatzResearch.WordTrace tailWord_1278714 prefixEnd_1278714 72954989070379473254923 := by
  unfold tailWord_1278714
  simp only [CollatzResearch.WordTrace]
  refine ⟨11659632772361259952408799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31092354059630026539756797 11659632772361259952408799)
  ·
    refine ⟨17489449158541889928613199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11659632772361259952408799 17489449158541889928613199)
    ·
      refine ⟨26234173737812834892919799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17489449158541889928613199 26234173737812834892919799)
      ·
        refine ⟨39351260606719252339379699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26234173737812834892919799 39351260606719252339379699)
        ·
          refine ⟨59026890910078878509069549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39351260606719252339379699 59026890910078878509069549)
          ·
            refine ⟨22135084091279579440901081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59026890910078878509069549 22135084091279579440901081)
            ·
              refine ⟨16601313068459684580675811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22135084091279579440901081 16601313068459684580675811)
              ·
                refine ⟨24901969602689526871013717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16601313068459684580675811 24901969602689526871013717)
                ·
                  refine ⟨72954989070379473254923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 24901969602689526871013717 72954989070379473254923)
                  ·
                    rfl

theorem cell23_1278714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 10].length) (baseStart_1278714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1278714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1278714 prefixEnd_1278714 := by exact prefixLift 1278714
  have htrace : WordTrace (prefixWord ++ tailWord_1278714) baseStart_1278714 baseEnd_1278714 := by
    simpa [prefixWord, tailWord_1278714, baseEnd_1278714] using wordTrace_append hprefix tailTrace_1278714
  have hstable : (prefixWord ++ tailWord_1278714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278714).length < 2 ^ (prefixWord ++ tailWord_1278714).sum := by decide
  have hdescent : baseEnd_1278714 < baseStart_1278714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278728 : List Nat := [2, 1, 3, 2, 2, 2, 2, 2, 2, 2, 3]
def baseStart_1278728 : Nat := 118140960795 + 1278728 * 2 ^ 59
def prefixEnd_1278728 : Nat := 4983230072969 + 3 ^ 40 * 1278728 * 2
def baseEnd_1278728 : Nat := 656602090362578204519243

theorem tailTrace_1278728 : CollatzResearch.WordTrace tailWord_1278728 prefixEnd_1278728 656602090362578204519243 := by
  unfold tailWord_1278728
  simp only [CollatzResearch.WordTrace]
  refine ⟨23319520855697160100322419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31092694474262880133763225 23319520855697160100322419)
  ·
    refine ⟨34979281283545740150483629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23319520855697160100322419 34979281283545740150483629)
    ·
      refine ⟨13117230481329652556431361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34979281283545740150483629 13117230481329652556431361)
      ·
        refine ⟨9837922860997239417323521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13117230481329652556431361 9837922860997239417323521)
        ·
          refine ⟨7378442145747929562992641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9837922860997239417323521 7378442145747929562992641)
          ·
            refine ⟨5533831609310947172244481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7378442145747929562992641 5533831609310947172244481)
            ·
              refine ⟨4150373706983210379183361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5533831609310947172244481 4150373706983210379183361)
              ·
                refine ⟨3112780280237407784387521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4150373706983210379183361 3112780280237407784387521)
                ·
                  refine ⟨2334585210178055838290641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3112780280237407784387521 2334585210178055838290641)
                  ·
                    refine ⟨1750938907633541878717981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2334585210178055838290641 1750938907633541878717981)
                    ·
                      refine ⟨656602090362578204519243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1750938907633541878717981 656602090362578204519243)
                      ·
                        rfl

theorem cell23_1278728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 2, 2, 2, 3].length) (baseStart_1278728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1278728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1278728 prefixEnd_1278728 := by exact prefixLift 1278728
  have htrace : WordTrace (prefixWord ++ tailWord_1278728) baseStart_1278728 baseEnd_1278728 := by
    simpa [prefixWord, tailWord_1278728, baseEnd_1278728] using wordTrace_append hprefix tailTrace_1278728
  have hstable : (prefixWord ++ tailWord_1278728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278728).length < 2 ^ (prefixWord ++ tailWord_1278728).sum := by decide
  have hdescent : baseEnd_1278728 < baseStart_1278728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278782 : List Nat := [4, 2, 1, 2, 4, 1, 1, 2, 6]
def baseStart_1278782 : Nat := 118140960795 + 1278782 * 2 ^ 59
def prefixEnd_1278782 : Nat := 4983230072969 + 3 ^ 40 * 1278782 * 2
def baseEnd_1278782 : Nat := 72958868701991221471555

theorem tailTrace_1278782 : CollatzResearch.WordTrace tailWord_1278782 prefixEnd_1278782 72958868701991221471555 := by
  unfold tailWord_1278782
  simp only [CollatzResearch.WordTrace]
  refine ⟨5830126406649835927888825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31094007502132458282073733 5830126406649835927888825)
  ·
    refine ⟨4372594804987376945916619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5830126406649835927888825 4372594804987376945916619)
    ·
      refine ⟨6558892207481065418874929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4372594804987376945916619 6558892207481065418874929)
      ·
        refine ⟨4919169155610799064156197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6558892207481065418874929 4919169155610799064156197)
        ·
          refine ⟨922344216677024824529287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4919169155610799064156197 922344216677024824529287)
          ·
            refine ⟨1383516325015537236793931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 922344216677024824529287 1383516325015537236793931)
            ·
              refine ⟨2075274487523305855190897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1383516325015537236793931 2075274487523305855190897)
              ·
                refine ⟨1556455865642479391393173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2075274487523305855190897 1556455865642479391393173)
                ·
                  refine ⟨72958868701991221471555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1556455865642479391393173 72958868701991221471555)
                  ·
                    rfl

theorem cell23_1278782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 2, 6].length) (baseStart_1278782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1278782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1278782 prefixEnd_1278782 := by exact prefixLift 1278782
  have htrace : WordTrace (prefixWord ++ tailWord_1278782) baseStart_1278782 baseEnd_1278782 := by
    simpa [prefixWord, tailWord_1278782, baseEnd_1278782] using wordTrace_append hprefix tailTrace_1278782
  have hstable : (prefixWord ++ tailWord_1278782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278782).length < 2 ^ (prefixWord ++ tailWord_1278782).sum := by decide
  have hdescent : baseEnd_1278782 < baseStart_1278782 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278808 : List Nat := [2, 1, 2, 2, 1, 1, 1, 7, 2, 4]
def baseStart_1278808 : Nat := 118140960795 + 1278808 * 2 ^ 59
def prefixEnd_1278808 : Nat := 4983230072969 + 3 ^ 40 * 1278808 * 2
def baseEnd_1278808 : Nat := 218881056271645963839625

theorem tailTrace_1278808 : CollatzResearch.WordTrace tailWord_1278808 prefixEnd_1278808 218881056271645963839625 := by
  unfold tailWord_1278808
  simp only [CollatzResearch.WordTrace]
  refine ⟨23320979775552246931778539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31094639700736329242371385 23320979775552246931778539)
  ·
    refine ⟨34981469663328370397667809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23320979775552246931778539 34981469663328370397667809)
    ·
      refine ⟨26236102247496277798250857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34981469663328370397667809 26236102247496277798250857)
      ·
        refine ⟨19677076685622208348688143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26236102247496277798250857 19677076685622208348688143)
        ·
          refine ⟨29515615028433312523032215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19677076685622208348688143 29515615028433312523032215)
          ·
            refine ⟨44273422542649968784548323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29515615028433312523032215 44273422542649968784548323)
            ·
              refine ⟨66410133813974953176822485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44273422542649968784548323 66410133813974953176822485)
              ·
                refine ⟨1556487511265037965081777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 66410133813974953176822485 1556487511265037965081777)
                ·
                  refine ⟨1167365633448778473811333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1556487511265037965081777 1167365633448778473811333)
                  ·
                    refine ⟨218881056271645963839625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1167365633448778473811333 218881056271645963839625)
                    ·
                      rfl

theorem cell23_1278808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 7, 2, 4].length) (baseStart_1278808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1278808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1278808 prefixEnd_1278808 := by exact prefixLift 1278808
  have htrace : WordTrace (prefixWord ++ tailWord_1278808) baseStart_1278808 baseEnd_1278808 := by
    simpa [prefixWord, tailWord_1278808, baseEnd_1278808] using wordTrace_append hprefix tailTrace_1278808
  have hstable : (prefixWord ++ tailWord_1278808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278808).length < 2 ^ (prefixWord ++ tailWord_1278808).sum := by decide
  have hdescent : baseEnd_1278808 < baseStart_1278808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278815 : List Nat := [1, 1, 2, 3, 1, 3, 1, 4, 3, 2, 2]
def baseStart_1278815 : Nat := 118140960795 + 1278815 * 2 ^ 59
def prefixEnd_1278815 : Nat := 4983230072969 + 3 ^ 40 * 1278815 * 2
def baseEnd_1278815 : Nat := 656646763179519364131343

theorem tailTrace_1278815 : CollatzResearch.WordTrace tailWord_1278815 prefixEnd_1278815 656646763179519364131343 := by
  unfold tailWord_1278815
  simp only [CollatzResearch.WordTrace]
  refine ⟨46642214862079134059061899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31094809908052756039374599 46642214862079134059061899)
  ·
    refine ⟨69963322293118701088592849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46642214862079134059061899 69963322293118701088592849)
    ·
      refine ⟨52472491719839025816444637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69963322293118701088592849 52472491719839025816444637)
      ·
        refine ⟨19677184394939634681166739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52472491719839025816444637 19677184394939634681166739)
        ·
          refine ⟨29515776592409452021750109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19677184394939634681166739 29515776592409452021750109)
          ·
            refine ⟨11068416222153544508156291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29515776592409452021750109 11068416222153544508156291)
            ·
              refine ⟨16602624333230316762234437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11068416222153544508156291 16602624333230316762234437)
              ·
                refine ⟨3112992062480684392918957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16602624333230316762234437 3112992062480684392918957)
                ·
                  refine ⟨1167372023430256647344609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3112992062480684392918957 1167372023430256647344609)
                  ·
                    refine ⟨875529017572692485508457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1167372023430256647344609 875529017572692485508457)
                    ·
                      refine ⟨656646763179519364131343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 875529017572692485508457 656646763179519364131343)
                      ·
                        rfl

theorem cell23_1278815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 4, 3, 2, 2].length) (baseStart_1278815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1278815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1278815 prefixEnd_1278815 := by exact prefixLift 1278815
  have htrace : WordTrace (prefixWord ++ tailWord_1278815) baseStart_1278815 baseEnd_1278815 := by
    simpa [prefixWord, tailWord_1278815, baseEnd_1278815] using wordTrace_append hprefix tailTrace_1278815
  have hstable : (prefixWord ++ tailWord_1278815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278815).length < 2 ^ (prefixWord ++ tailWord_1278815).sum := by decide
  have hdescent : baseEnd_1278815 < baseStart_1278815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278838 : List Nat := [5, 1, 1, 3, 1, 1, 11]
def baseStart_1278838 : Nat := 118140960795 + 1278838 * 2 ^ 59
def prefixEnd_1278838 : Nat := 4983230072969 + 3 ^ 40 * 1278838 * 2
def baseEnd_1278838 : Nat := 8106895965858923137577

theorem tailTrace_1278838 : CollatzResearch.WordTrace tailWord_1278838 prefixEnd_1278838 8106895965858923137577 := by
  unfold tailWord_1278838
  simp only [CollatzResearch.WordTrace]
  refine ⟨2915190858812238061696823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31095369160663872658099445 2915190858812238061696823)
  ·
    refine ⟨4372786288218357092545235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2915190858812238061696823 4372786288218357092545235)
    ·
      refine ⟨6559179432327535638817853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4372786288218357092545235 6559179432327535638817853)
      ·
        refine ⟨2459692287122825864556695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6559179432327535638817853 2459692287122825864556695)
        ·
          refine ⟨3689538430684238796835043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2459692287122825864556695 3689538430684238796835043)
          ·
            refine ⟨5534307646026358195252565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3689538430684238796835043 5534307646026358195252565)
            ·
              refine ⟨8106895965858923137577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 5534307646026358195252565 8106895965858923137577)
              ·
                rfl

theorem cell23_1278838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 11].length) (baseStart_1278838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1278838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1278838 prefixEnd_1278838 := by exact prefixLift 1278838
  have htrace : WordTrace (prefixWord ++ tailWord_1278838) baseStart_1278838 baseEnd_1278838 := by
    simpa [prefixWord, tailWord_1278838, baseEnd_1278838] using wordTrace_append hprefix tailTrace_1278838
  have hstable : (prefixWord ++ tailWord_1278838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278838).length < 2 ^ (prefixWord ++ tailWord_1278838).sum := by decide
  have hdescent : baseEnd_1278838 < baseStart_1278838 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278851 : List Nat := [1, 1, 1, 3, 4, 1, 2, 1, 2, 7]
def baseStart_1278851 : Nat := 118140960795 + 1278851 * 2 ^ 59
def prefixEnd_1278851 : Nat := 4983230072969 + 3 ^ 40 * 1278851 * 2
def baseEnd_1278851 : Nat := 218888416161027074427059

theorem tailTrace_1278851 : CollatzResearch.WordTrace tailWord_1278851 prefixEnd_1278851 218888416161027074427059 := by
  unfold tailWord_1278851
  simp only [CollatzResearch.WordTrace]
  refine ⟨46643527889948712207372407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31095685259965808138248271 46643527889948712207372407)
  ·
    refine ⟨69965291834923068311058611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46643527889948712207372407 69965291834923068311058611)
    ·
      refine ⟨104947937752384602466587917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69965291834923068311058611 104947937752384602466587917)
      ·
        refine ⟨39355476657144225924970469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104947937752384602466587917 39355476657144225924970469)
        ·
          refine ⟨7379151873214542360931963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39355476657144225924970469 7379151873214542360931963)
          ·
            refine ⟨11068727809821813541397945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7379151873214542360931963 11068727809821813541397945)
            ·
              refine ⟨8301545857366360156048459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11068727809821813541397945 8301545857366360156048459)
              ·
                refine ⟨12452318786049540234072689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8301545857366360156048459 12452318786049540234072689)
                ·
                  refine ⟨9339239089537155175554517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12452318786049540234072689 9339239089537155175554517)
                  ·
                    refine ⟨218888416161027074427059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9339239089537155175554517 218888416161027074427059)
                    ·
                      rfl

theorem cell23_1278851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 2, 7].length) (baseStart_1278851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1278851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1278851 prefixEnd_1278851 := by exact prefixLift 1278851
  have htrace : WordTrace (prefixWord ++ tailWord_1278851) baseStart_1278851 baseEnd_1278851 := by
    simpa [prefixWord, tailWord_1278851, baseEnd_1278851] using wordTrace_append hprefix tailTrace_1278851
  have hstable : (prefixWord ++ tailWord_1278851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278851).length < 2 ^ (prefixWord ++ tailWord_1278851).sum := by decide
  have hdescent : baseEnd_1278851 < baseStart_1278851 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278900 : List Nat := [2, 5, 2, 1, 1, 3, 2, 2, 1, 2, 2]
def baseStart_1278900 : Nat := 118140960795 + 1278900 * 2 ^ 59
def prefixEnd_1278900 : Nat := 4983230072969 + 3 ^ 40 * 1278900 * 2
def baseEnd_1278900 : Nat := 656690409035151531568453

theorem tailTrace_1278900 : CollatzResearch.WordTrace tailWord_1278900 prefixEnd_1278900 656690409035151531568453 := by
  unfold tailWord_1278900
  simp only [CollatzResearch.WordTrace]
  refine ⟨23322657533385596787953077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31096876711180795717270769 23322657533385596787953077)
  ·
    refine ⟨2186499143754899698870601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23322657533385596787953077 2186499143754899698870601)
    ·
      refine ⟨1639874357816174774152951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2186499143754899698870601 1639874357816174774152951)
      ·
        refine ⟨2459811536724262161229427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1639874357816174774152951 2459811536724262161229427)
        ·
          refine ⟨3689717305086393241844141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2459811536724262161229427 3689717305086393241844141)
          ·
            refine ⟨1383643989407397465691553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3689717305086393241844141 1383643989407397465691553)
            ·
              refine ⟨1037732992055548099268665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1383643989407397465691553 1037732992055548099268665)
              ·
                refine ⟨778299744041661074451499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1037732992055548099268665 778299744041661074451499)
                ·
                  refine ⟨1167449616062491611677249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 778299744041661074451499 1167449616062491611677249)
                  ·
                    refine ⟨875587212046868708757937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1167449616062491611677249 875587212046868708757937)
                    ·
                      refine ⟨656690409035151531568453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 875587212046868708757937 656690409035151531568453)
                      ·
                        rfl

theorem cell23_1278900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 2, 2, 1, 2, 2].length) (baseStart_1278900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1278900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1278900 prefixEnd_1278900 := by exact prefixLift 1278900
  have htrace : WordTrace (prefixWord ++ tailWord_1278900) baseStart_1278900 baseEnd_1278900 := by
    simpa [prefixWord, tailWord_1278900, baseEnd_1278900] using wordTrace_append hprefix tailTrace_1278900
  have hstable : (prefixWord ++ tailWord_1278900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278900).length < 2 ^ (prefixWord ++ tailWord_1278900).sum := by decide
  have hdescent : baseEnd_1278900 < baseStart_1278900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278962 : List Nat := [3, 2, 1, 5, 1, 1, 2, 1, 7]
def baseStart_1278962 : Nat := 118140960795 + 1278962 * 2 ^ 59
def prefixEnd_1278962 : Nat := 4983230072969 + 3 ^ 40 * 1278962 * 2
def baseEnd_1278962 : Nat := 72969138315081143221463

theorem tailTrace_1278962 : CollatzResearch.WordTrace tailWord_1278962 prefixEnd_1278962 72969138315081143221463 := by
  unfold tailWord_1278962
  simp only [CollatzResearch.WordTrace]
  refine ⟨11661894098136644541165785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31098384261697718776442093 11661894098136644541165785)
  ·
    refine ⟨8746420573602483405874339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11661894098136644541165785 8746420573602483405874339)
    ·
      refine ⟨13119630860403725108811509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8746420573602483405874339 13119630860403725108811509)
      ·
        refine ⟨1229965393162849228951079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13119630860403725108811509 1229965393162849228951079)
        ·
          refine ⟨1844948089744273843426619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1229965393162849228951079 1844948089744273843426619)
          ·
            refine ⟨2767422134616410765139929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1844948089744273843426619 2767422134616410765139929)
            ·
              refine ⟨2075566600962308073854947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2767422134616410765139929 2075566600962308073854947)
              ·
                refine ⟨3113349901443462110782421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2075566600962308073854947 3113349901443462110782421)
                ·
                  refine ⟨72969138315081143221463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3113349901443462110782421 72969138315081143221463)
                  ·
                    rfl

theorem cell23_1278962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 1, 7].length) (baseStart_1278962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1278962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1278962 prefixEnd_1278962 := by exact prefixLift 1278962
  have htrace : WordTrace (prefixWord ++ tailWord_1278962) baseStart_1278962 baseEnd_1278962 := by
    simpa [prefixWord, tailWord_1278962, baseEnd_1278962] using wordTrace_append hprefix tailTrace_1278962
  have hstable : (prefixWord ++ tailWord_1278962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278962).length < 2 ^ (prefixWord ++ tailWord_1278962).sum := by decide
  have hdescent : baseEnd_1278962 < baseStart_1278962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279012 : List Nat := [2, 3, 1, 4, 1, 2, 1, 2, 2, 1, 4]
def baseStart_1279012 : Nat := 118140960795 + 1279012 * 2 ^ 59
def prefixEnd_1279012 : Nat := 4983230072969 + 3 ^ 40 * 1279012 * 2
def baseEnd_1279012 : Nat := 656747918868455093367937

theorem tailTrace_1279012 : CollatzResearch.WordTrace tailWord_1279012 prefixEnd_1279012 656747918868455093367937 := by
  unfold tailWord_1279012
  simp only [CollatzResearch.WordTrace]
  refine ⟨23324700021182718351991645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31099600028243624469322193 23324700021182718351991645)
  ·
    refine ⟨8746762507943519381996867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23324700021182718351991645 8746762507943519381996867)
    ·
      refine ⟨13120143761915279072995301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8746762507943519381996867 13120143761915279072995301)
      ·
        refine ⟨2460026955359114826186619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13120143761915279072995301 2460026955359114826186619)
        ·
          refine ⟨3690040433038672239279929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2460026955359114826186619 3690040433038672239279929)
          ·
            refine ⟨2767530324779004179459947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3690040433038672239279929 2767530324779004179459947)
            ·
              refine ⟨4151295487168506269189921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2767530324779004179459947 4151295487168506269189921)
              ·
                refine ⟨3113471615376379701892441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4151295487168506269189921 3113471615376379701892441)
                ·
                  refine ⟨2335103711532284776419331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3113471615376379701892441 2335103711532284776419331)
                  ·
                    refine ⟨3502655567298427164628997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2335103711532284776419331 3502655567298427164628997)
                    ·
                      refine ⟨656747918868455093367937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3502655567298427164628997 656747918868455093367937)
                      ·
                        rfl

theorem cell23_1279012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_1279012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1279012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1279012 prefixEnd_1279012 := by exact prefixLift 1279012
  have htrace : WordTrace (prefixWord ++ tailWord_1279012) baseStart_1279012 baseEnd_1279012 := by
    simpa [prefixWord, tailWord_1279012, baseEnd_1279012] using wordTrace_append hprefix tailTrace_1279012
  have hstable : (prefixWord ++ tailWord_1279012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279012).length < 2 ^ (prefixWord ++ tailWord_1279012).sum := by decide
  have hdescent : baseEnd_1279012 < baseStart_1279012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279069 : List Nat := [1, 4, 4, 1, 2, 1, 2, 2, 6]
def baseStart_1279069 : Nat := 118140960795 + 1279069 * 2 ^ 59
def prefixEnd_1279069 : Nat := 4983230072969 + 3 ^ 40 * 1279069 * 2
def baseEnd_1279069 : Nat := 72975243029529041150575

theorem tailTrace_1279069 : CollatzResearch.WordTrace tailWord_1279069 prefixEnd_1279069 72975243029529041150575 := by
  unfold tailWord_1279069
  simp only [CollatzResearch.WordTrace]
  refine ⟨46651479003158935438808261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31100986002105956959205507 46651479003158935438808261)
  ·
    refine ⟨8747152313092300394776549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46651479003158935438808261 8747152313092300394776549)
    ·
      refine ⟨1640091058704806324020603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8747152313092300394776549 1640091058704806324020603)
      ·
        refine ⟨2460136588057209486030905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1640091058704806324020603 2460136588057209486030905)
        ·
          refine ⟨1845102441042907114523179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2460136588057209486030905 1845102441042907114523179)
          ·
            refine ⟨2767653661564360671784769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1845102441042907114523179 2767653661564360671784769)
            ·
              refine ⟨2075740246173270503838577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2767653661564360671784769 2075740246173270503838577)
              ·
                refine ⟨1556805184629952877878933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2075740246173270503838577 1556805184629952877878933)
                ·
                  refine ⟨72975243029529041150575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1556805184629952877878933 72975243029529041150575)
                  ·
                    rfl

theorem cell23_1279069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 2, 6].length) (baseStart_1279069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1279069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1279069 prefixEnd_1279069 := by exact prefixLift 1279069
  have htrace : WordTrace (prefixWord ++ tailWord_1279069) baseStart_1279069 baseEnd_1279069 := by
    simpa [prefixWord, tailWord_1279069, baseEnd_1279069] using wordTrace_append hprefix tailTrace_1279069
  have hstable : (prefixWord ++ tailWord_1279069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279069).length < 2 ^ (prefixWord ++ tailWord_1279069).sum := by decide
  have hdescent : baseEnd_1279069 < baseStart_1279069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279072 : List Nat := [2, 1, 1, 3, 2, 2, 1, 4, 2, 3, 2]
def baseStart_1279072 : Nat := 118140960795 + 1279072 * 2 ^ 59
def prefixEnd_1279072 : Nat := 4983230072969 + 3 ^ 40 * 1279072 * 2
def baseEnd_1279072 : Nat := 656778727707724858617661

theorem tailTrace_1279072 : CollatzResearch.WordTrace tailWord_1279072 prefixEnd_1279072 656778727707724858617661 := by
  unfold tailWord_1279072
  simp only [CollatzResearch.WordTrace]
  refine ⟨23325794211074033475583735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31101058948098711300778313 23325794211074033475583735)
  ·
    refine ⟨34988691316611050213375603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23325794211074033475583735 34988691316611050213375603)
    ·
      refine ⟨52483036974916575320063405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34988691316611050213375603 52483036974916575320063405)
      ·
        refine ⟨19681138865593715745023777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52483036974916575320063405 19681138865593715745023777)
        ·
          refine ⟨14760854149195286808767833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19681138865593715745023777 14760854149195286808767833)
          ·
            refine ⟨11070640611896465106575875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14760854149195286808767833 11070640611896465106575875)
            ·
              refine ⟨16605960917844697659863813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11070640611896465106575875 16605960917844697659863813)
              ·
                refine ⟨3113617672095880811224465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16605960917844697659863813 3113617672095880811224465)
                ·
                  refine ⟨2335213254071910608418349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3113617672095880811224465 2335213254071910608418349)
                  ·
                    refine ⟨875704970276966478156881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2335213254071910608418349 875704970276966478156881)
                    ·
                      refine ⟨656778727707724858617661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 875704970276966478156881 656778727707724858617661)
                      ·
                        rfl

theorem cell23_1279072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 4, 2, 3, 2].length) (baseStart_1279072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1279072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1279072 prefixEnd_1279072 := by exact prefixLift 1279072
  have htrace : WordTrace (prefixWord ++ tailWord_1279072) baseStart_1279072 baseEnd_1279072 := by
    simpa [prefixWord, tailWord_1279072, baseEnd_1279072] using wordTrace_append hprefix tailTrace_1279072
  have hstable : (prefixWord ++ tailWord_1279072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279072).length < 2 ^ (prefixWord ++ tailWord_1279072).sum := by decide
  have hdescent : baseEnd_1279072 < baseStart_1279072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279095 : List Nat := [1, 1, 3, 1, 1, 4, 4, 1, 1, 6]
def baseStart_1279095 : Nat := 118140960795 + 1279095 * 2 ^ 59
def prefixEnd_1279095 : Nat := 4983230072969 + 3 ^ 40 * 1279095 * 2
def baseEnd_1279095 : Nat := 218930179254259422876685

theorem tailTrace_1279095 : CollatzResearch.WordTrace tailWord_1279095 prefixEnd_1279095 218930179254259422876685 := by
  unfold tailWord_1279095
  simp only [CollatzResearch.WordTrace]
  refine ⟨46652427301064741879254739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31101618200709827919503159 46652427301064741879254739)
  ·
    refine ⟨69978640951597112818882109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46652427301064741879254739 69978640951597112818882109)
    ·
      refine ⟨26241990356848917307080791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69978640951597112818882109 26241990356848917307080791)
      ·
        refine ⟨39362985535273375960621187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26241990356848917307080791 39362985535273375960621187)
        ·
          refine ⟨59044478302910063940931781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39362985535273375960621187 59044478302910063940931781)
          ·
            refine ⟨11070839681795636988924709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59044478302910063940931781 11070839681795636988924709)
            ·
              refine ⟨2075782440336681935423383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11070839681795636988924709 2075782440336681935423383)
              ·
                refine ⟨3113673660505022903135075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2075782440336681935423383 3113673660505022903135075)
                ·
                  refine ⟨4670510490757534354702613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3113673660505022903135075 4670510490757534354702613)
                  ·
                    refine ⟨218930179254259422876685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4670510490757534354702613 218930179254259422876685)
                    ·
                      rfl

theorem cell23_1279095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 1, 1, 6].length) (baseStart_1279095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1279095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1279095 prefixEnd_1279095 := by exact prefixLift 1279095
  have htrace : WordTrace (prefixWord ++ tailWord_1279095) baseStart_1279095 baseEnd_1279095 := by
    simpa [prefixWord, tailWord_1279095, baseEnd_1279095] using wordTrace_append hprefix tailTrace_1279095
  have hstable : (prefixWord ++ tailWord_1279095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279095).length < 2 ^ (prefixWord ++ tailWord_1279095).sum := by decide
  have hdescent : baseEnd_1279095 < baseStart_1279095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279136 : List Nat := [2, 1, 1, 4, 2, 1, 1, 6, 1, 2, 2]
def baseStart_1279136 : Nat := 118140960795 + 1279136 * 2 ^ 59
def prefixEnd_1279136 : Nat := 4983230072969 + 3 ^ 40 * 1279136 * 2
def baseEnd_1279136 : Nat := 656811590469612608217367

theorem tailTrace_1279136 : CollatzResearch.WordTrace tailWord_1279136 prefixEnd_1279136 656811590469612608217367 := by
  unfold tailWord_1279136
  simp only [CollatzResearch.WordTrace]
  refine ⟨23326961346958102940748631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31102615129277470587664841 23326961346958102940748631)
  ·
    refine ⟨34990442020437154411122947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23326961346958102940748631 34990442020437154411122947)
    ·
      refine ⟨52485663030655731616684421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34990442020437154411122947 52485663030655731616684421)
      ·
        refine ⟨9841061818247949678128329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52485663030655731616684421 9841061818247949678128329)
        ·
          refine ⟨7380796363685962258596247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9841061818247949678128329 7380796363685962258596247)
          ·
            refine ⟨11071194545528943387894371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7380796363685962258596247 11071194545528943387894371)
            ·
              refine ⟨16606791818293415081841557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11071194545528943387894371 16606791818293415081841557)
              ·
                refine ⟨778443366482503831961323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 16606791818293415081841557 778443366482503831961323)
                ·
                  refine ⟨1167665049723755747941985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 778443366482503831961323 1167665049723755747941985)
                  ·
                    refine ⟨875748787292816810956489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1167665049723755747941985 875748787292816810956489)
                    ·
                      refine ⟨656811590469612608217367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 875748787292816810956489 656811590469612608217367)
                      ·
                        rfl

theorem cell23_1279136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 6, 1, 2, 2].length) (baseStart_1279136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1279136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1279136 prefixEnd_1279136 := by exact prefixLift 1279136
  have htrace : WordTrace (prefixWord ++ tailWord_1279136) baseStart_1279136 baseEnd_1279136 := by
    simpa [prefixWord, tailWord_1279136, baseEnd_1279136] using wordTrace_append hprefix tailTrace_1279136
  have hstable : (prefixWord ++ tailWord_1279136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279136).length < 2 ^ (prefixWord ++ tailWord_1279136).sum := by decide
  have hdescent : baseEnd_1279136 < baseStart_1279136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279165 : List Nat := [1, 4, 1, 2, 1, 1, 3, 1, 2, 2, 5]
def baseStart_1279165 : Nat := 118140960795 + 1279165 * 2 ^ 59
def prefixEnd_1279165 : Nat := 4983230072969 + 3 ^ 40 * 1279165 * 2
def baseEnd_1279165 : Nat := 656826481408592994754733

theorem tailTrace_1279165 : CollatzResearch.WordTrace tailWord_1279165 prefixEnd_1279165 656826481408592994754733 := by
  unfold tailWord_1279165
  simp only [CollatzResearch.WordTrace]
  refine ⟨46654980410811143834302949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31103320273874095889535299 46654980410811143834302949)
  ·
    refine ⟨8747808827027089468931803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46654980410811143834302949 8747808827027089468931803)
    ·
      refine ⟨13121713240540634203397705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8747808827027089468931803 13121713240540634203397705)
      ·
        refine ⟨9841284930405475652548279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13121713240540634203397705 9841284930405475652548279)
        ·
          refine ⟨14761927395608213478822419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9841284930405475652548279 14761927395608213478822419)
          ·
            refine ⟨22142891093412320218233629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14761927395608213478822419 22142891093412320218233629)
            ·
              refine ⟨8303584160029620081837611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22142891093412320218233629 8303584160029620081837611)
              ·
                refine ⟨12455376240044430122756417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8303584160029620081837611 12455376240044430122756417)
                ·
                  refine ⟨9341532180033322592067313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12455376240044430122756417 9341532180033322592067313)
                  ·
                    refine ⟨7006149135024991944050485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9341532180033322592067313 7006149135024991944050485)
                    ·
                      refine ⟨656826481408592994754733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7006149135024991944050485 656826481408592994754733)
                      ·
                        rfl

theorem cell23_1279165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_1279165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1279165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1279165 prefixEnd_1279165 := by exact prefixLift 1279165
  have htrace : WordTrace (prefixWord ++ tailWord_1279165) baseStart_1279165 baseEnd_1279165 := by
    simpa [prefixWord, tailWord_1279165, baseEnd_1279165] using wordTrace_append hprefix tailTrace_1279165
  have hstable : (prefixWord ++ tailWord_1279165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279165).length < 2 ^ (prefixWord ++ tailWord_1279165).sum := by decide
  have hdescent : baseEnd_1279165 < baseStart_1279165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279213 : List Nat := [1, 5, 1, 2, 2, 3, 1, 2, 1, 3, 2]
def baseStart_1279213 : Nat := 118140960795 + 1279213 * 2 ^ 59
def prefixEnd_1279213 : Nat := 4983230072969 + 3 ^ 40 * 1279213 * 2
def baseEnd_1279213 : Nat := 656851128480008806954513

theorem tailTrace_1279213 : CollatzResearch.WordTrace tailWord_1279213 prefixEnd_1279213 656851128480008806954513 := by
  unfold tailWord_1279213
  simp only [CollatzResearch.WordTrace]
  refine ⟨46656731114637248032050293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31104487409758165354700195 46656731114637248032050293)
  ·
    refine ⟨4374068541997242003004715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46656731114637248032050293 4374068541997242003004715)
    ·
      refine ⟨6561102812995863004507073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4374068541997242003004715 6561102812995863004507073)
      ·
        refine ⟨4920827109746897253380305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6561102812995863004507073 4920827109746897253380305)
        ·
          refine ⟨3690620332310172940035229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4920827109746897253380305 3690620332310172940035229)
          ·
            refine ⟨1383982624616314852513211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3690620332310172940035229 1383982624616314852513211)
            ·
              refine ⟨2075973936924472278769817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1383982624616314852513211 2075973936924472278769817)
              ·
                refine ⟨1556980452693354209077363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2075973936924472278769817 1556980452693354209077363)
                ·
                  refine ⟨2335470679040031313616045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1556980452693354209077363 2335470679040031313616045)
                  ·
                    refine ⟨875801504640011742606017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2335470679040031313616045 875801504640011742606017)
                    ·
                      refine ⟨656851128480008806954513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 875801504640011742606017 656851128480008806954513)
                      ·
                        rfl

theorem cell23_1279213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 2, 1, 3, 2].length) (baseStart_1279213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1279213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1279213 prefixEnd_1279213 := by exact prefixLift 1279213
  have htrace : WordTrace (prefixWord ++ tailWord_1279213) baseStart_1279213 baseEnd_1279213 := by
    simpa [prefixWord, tailWord_1279213, baseEnd_1279213] using wordTrace_append hprefix tailTrace_1279213
  have hstable : (prefixWord ++ tailWord_1279213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279213).length < 2 ^ (prefixWord ++ tailWord_1279213).sum := by decide
  have hdescent : baseEnd_1279213 < baseStart_1279213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279222 : List Nat := [5, 1, 1, 1, 1, 1, 1, 2, 4, 2, 4]
def baseStart_1279222 : Nat := 118140960795 + 1279222 * 2 ^ 59
def prefixEnd_1279222 : Nat := 4983230072969 + 3 ^ 40 * 1279222 * 2
def baseEnd_1279222 : Nat := 656855749805899271741971

theorem tailTrace_1279222 : CollatzResearch.WordTrace tailWord_1279222 prefixEnd_1279222 656855749805899271741971 := by
  unfold tailWord_1279222
  simp only [CollatzResearch.WordTrace]
  refine ⟨2916066210725290160570495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31104706247736428379418613 2916066210725290160570495)
  ·
    refine ⟨4374099316087935240855743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2916066210725290160570495 4374099316087935240855743)
    ·
      refine ⟨6561148974131902861283615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4374099316087935240855743 6561148974131902861283615)
      ·
        refine ⟨9841723461197854291925423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6561148974131902861283615 9841723461197854291925423)
        ·
          refine ⟨14762585191796781437888135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9841723461197854291925423 14762585191796781437888135)
          ·
            refine ⟨22143877787695172156832203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14762585191796781437888135 22143877787695172156832203)
            ·
              refine ⟨33215816681542758235248305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22143877787695172156832203 33215816681542758235248305)
              ·
                refine ⟨24911862511157068676436229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33215816681542758235248305 24911862511157068676436229)
                ·
                  refine ⟨4670974220841950376831793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24911862511157068676436229 4670974220841950376831793)
                  ·
                    refine ⟨3503230665631462782623845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4670974220841950376831793 3503230665631462782623845)
                    ·
                      refine ⟨656855749805899271741971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3503230665631462782623845 656855749805899271741971)
                      ·
                        rfl

theorem cell23_1279222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_1279222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1279222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1279222 prefixEnd_1279222 := by exact prefixLift 1279222
  have htrace : WordTrace (prefixWord ++ tailWord_1279222) baseStart_1279222 baseEnd_1279222 := by
    simpa [prefixWord, tailWord_1279222, baseEnd_1279222] using wordTrace_append hprefix tailTrace_1279222
  have hstable : (prefixWord ++ tailWord_1279222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279222).length < 2 ^ (prefixWord ++ tailWord_1279222).sum := by decide
  have hdescent : baseEnd_1279222 < baseStart_1279222 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279232 : List Nat := [2, 1, 1, 2, 1, 1, 3, 7, 5]
def baseStart_1279232 : Nat := 118140960795 + 1279232 * 2 ^ 59
def prefixEnd_1279232 : Nat := 4983230072969 + 3 ^ 40 * 1279232 * 2
def baseEnd_1279232 : Nat := 72984542734716025846325

theorem tailTrace_1279232 : CollatzResearch.WordTrace tailWord_1279232 prefixEnd_1279232 72984542734716025846325 := by
  unfold tailWord_1279232
  simp only [CollatzResearch.WordTrace]
  refine ⟨23328712050784207138495975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31104949401045609517994633 23328712050784207138495975)
  ·
    refine ⟨34993068076176310707743963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23328712050784207138495975 34993068076176310707743963)
    ·
      refine ⟨52489602114264466061615945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34993068076176310707743963 52489602114264466061615945)
      ·
        refine ⟨39367201585698349546211959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52489602114264466061615945 39367201585698349546211959)
        ·
          refine ⟨59050802378547524319317939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39367201585698349546211959 59050802378547524319317939)
          ·
            refine ⟨88576203567821286478976909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59050802378547524319317939 88576203567821286478976909)
            ·
              refine ⟨33216076337932982429616341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88576203567821286478976909 33216076337932982429616341)
              ·
                refine ⟨778501789170304275694133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 33216076337932982429616341 778501789170304275694133)
                ·
                  refine ⟨72984542734716025846325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 778501789170304275694133 72984542734716025846325)
                  ·
                    rfl

theorem cell23_1279232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 7, 5].length) (baseStart_1279232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1279232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1279232 prefixEnd_1279232 := by exact prefixLift 1279232
  have htrace : WordTrace (prefixWord ++ tailWord_1279232) baseStart_1279232 baseEnd_1279232 := by
    simpa [prefixWord, tailWord_1279232, baseEnd_1279232] using wordTrace_append hprefix tailTrace_1279232
  have hstable : (prefixWord ++ tailWord_1279232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279232).length < 2 ^ (prefixWord ++ tailWord_1279232).sum := by decide
  have hdescent : baseEnd_1279232 < baseStart_1279232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279242 : List Nat := [3, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3]
def baseStart_1279242 : Nat := 118140960795 + 1279242 * 2 ^ 59
def prefixEnd_1279242 : Nat := 4983230072969 + 3 ^ 40 * 1279242 * 2
def baseEnd_1279242 : Nat := 656866019418989193491879

theorem tailTrace_1279242 : CollatzResearch.WordTrace tailWord_1279242 prefixEnd_1279242 656866019418989193491879 := by
  unfold tailWord_1279242
  simp only [CollatzResearch.WordTrace]
  refine ⟨11664447207883046496213995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31105192554354790656570653 11664447207883046496213995)
  ·
    refine ⟨17496670811824569744320993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11664447207883046496213995 17496670811824569744320993)
    ·
      refine ⟨13122503108868427308240745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17496670811824569744320993 13122503108868427308240745)
      ·
        refine ⟨9841877331651320481180559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13122503108868427308240745 9841877331651320481180559)
        ·
          refine ⟨14762815997476980721770839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9841877331651320481180559 14762815997476980721770839)
          ·
            refine ⟨22144223996215471082656259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14762815997476980721770839 22144223996215471082656259)
            ·
              refine ⟨33216335994323206623984389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22144223996215471082656259 33216335994323206623984389)
              ·
                refine ⟨6228062998935601241997073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33216335994323206623984389 6228062998935601241997073)
                ·
                  refine ⟨4671047249201700931497805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6228062998935601241997073 4671047249201700931497805)
                  ·
                    refine ⟨1751642718450637849311677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4671047249201700931497805 1751642718450637849311677)
                    ·
                      refine ⟨656866019418989193491879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1751642718450637849311677 656866019418989193491879)
                      ·
                        rfl

theorem cell23_1279242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3].length) (baseStart_1279242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1279242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1279242 prefixEnd_1279242 := by exact prefixLift 1279242
  have htrace : WordTrace (prefixWord ++ tailWord_1279242) baseStart_1279242 baseEnd_1279242 := by
    simpa [prefixWord, tailWord_1279242, baseEnd_1279242] using wordTrace_append hprefix tailTrace_1279242
  have hstable : (prefixWord ++ tailWord_1279242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279242).length < 2 ^ (prefixWord ++ tailWord_1279242).sum := by decide
  have hdescent : baseEnd_1279242 < baseStart_1279242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279322 : List Nat := [3, 1, 1, 2, 1, 2, 2, 5, 6]
def baseStart_1279322 : Nat := 118140960795 + 1279322 * 2 ^ 59
def prefixEnd_1279322 : Nat := 4983230072969 + 3 ^ 40 * 1279322 * 2
def baseEnd_1279322 : Nat := 72989677541260986721279

theorem tailTrace_1279322 : CollatzResearch.WordTrace tailWord_1279322 prefixEnd_1279322 72989677541260986721279 := by
  unfold tailWord_1279322
  simp only [CollatzResearch.WordTrace]
  refine ⟨11665176667810589911942055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31107137780828239765178813 11665176667810589911942055)
  ·
    refine ⟨17497765001715884867913083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11665176667810589911942055 17497765001715884867913083)
    ·
      refine ⟨26246647502573827301869625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17497765001715884867913083 26246647502573827301869625)
      ·
        refine ⟨19684985626930370476402219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26246647502573827301869625 19684985626930370476402219)
        ·
          refine ⟨29527478440395555714603329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19684985626930370476402219 29527478440395555714603329)
          ·
            refine ⟨22145608830296666785952497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29527478440395555714603329 22145608830296666785952497)
            ·
              refine ⟨16609206622722500089464373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22145608830296666785952497 16609206622722500089464373)
              ·
                refine ⟨1557113120880234383387285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16609206622722500089464373 1557113120880234383387285)
                ·
                  refine ⟨72989677541260986721279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1557113120880234383387285 72989677541260986721279)
                  ·
                    rfl

theorem cell23_1279322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 5, 6].length) (baseStart_1279322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1279322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1279322 prefixEnd_1279322 := by exact prefixLift 1279322
  have htrace : WordTrace (prefixWord ++ tailWord_1279322) baseStart_1279322 baseEnd_1279322 := by
    simpa [prefixWord, tailWord_1279322, baseEnd_1279322] using wordTrace_append hprefix tailTrace_1279322
  have hstable : (prefixWord ++ tailWord_1279322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279322).length < 2 ^ (prefixWord ++ tailWord_1279322).sum := by decide
  have hdescent : baseEnd_1279322 < baseStart_1279322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279399 : List Nat := [1, 1, 6, 1, 1, 1, 3, 2, 1, 6]
def baseStart_1279399 : Nat := 118140960795 + 1279399 * 2 ^ 59
def prefixEnd_1279399 : Nat := 4983230072969 + 3 ^ 40 * 1279399 * 2
def baseEnd_1279399 : Nat := 218982211960581693076219

theorem tailTrace_1279399 : CollatzResearch.WordTrace tailWord_1279399 prefixEnd_1279399 218982211960581693076219 := by
  unfold tailWord_1279399
  simp only [CollatzResearch.WordTrace]
  refine ⟨46663515091963401798321251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31109010061308934532214167 46663515091963401798321251)
  ·
    refine ⟨69995272637945102697481877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46663515091963401798321251 69995272637945102697481877)
    ·
      refine ⟨3281028404903676688944463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 69995272637945102697481877 3281028404903676688944463)
      ·
        refine ⟨4921542607355515033416695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3281028404903676688944463 4921542607355515033416695)
        ·
          refine ⟨7382313911033272550125043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4921542607355515033416695 7382313911033272550125043)
          ·
            refine ⟨11073470866549908825187565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7382313911033272550125043 11073470866549908825187565)
            ·
              refine ⟨4152551574956215809445337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11073470866549908825187565 4152551574956215809445337)
              ·
                refine ⟨3114413681217161857084003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4152551574956215809445337 3114413681217161857084003)
                ·
                  refine ⟨4671620521825742785626005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3114413681217161857084003 4671620521825742785626005)
                  ·
                    refine ⟨218982211960581693076219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4671620521825742785626005 218982211960581693076219)
                    ·
                      rfl

theorem cell23_1279399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_1279399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1279399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1279399 prefixEnd_1279399 := by exact prefixLift 1279399
  have htrace : WordTrace (prefixWord ++ tailWord_1279399) baseStart_1279399 baseEnd_1279399 := by
    simpa [prefixWord, tailWord_1279399, baseEnd_1279399] using wordTrace_append hprefix tailTrace_1279399
  have hstable : (prefixWord ++ tailWord_1279399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279399).length < 2 ^ (prefixWord ++ tailWord_1279399).sum := by decide
  have hdescent : baseEnd_1279399 < baseStart_1279399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279417 : List Nat := [1, 2, 1, 4, 4, 2, 2, 2, 1, 1, 3]
def baseStart_1279417 : Nat := 118140960795 + 1279417 * 2 ^ 59
def prefixEnd_1279417 : Nat := 4983230072969 + 3 ^ 40 * 1279417 * 2
def baseEnd_1279417 : Nat := 656955878533526008803575

theorem tailTrace_1279417 : CollatzResearch.WordTrace tailWord_1279417 prefixEnd_1279417 656955878533526008803575 := by
  unfold tailWord_1279417
  simp only [CollatzResearch.WordTrace]
  refine ⟨46664171605898190872476505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31109447737265460581651003 46664171605898190872476505)
  ·
    refine ⟨34998128704423643154357379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46664171605898190872476505 34998128704423643154357379)
    ·
      refine ⟨52497193056635464731536069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34998128704423643154357379 52497193056635464731536069)
      ·
        refine ⟨9843223698119149637163013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52497193056635464731536069 9843223698119149637163013)
        ·
          refine ⟨1845604443397340556968065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9843223698119149637163013 1845604443397340556968065)
          ·
            refine ⟨1384203332548005417726049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1845604443397340556968065 1384203332548005417726049)
            ·
              refine ⟨1038152499411004063294537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1384203332548005417726049 1038152499411004063294537)
              ·
                refine ⟨778614374558253047470903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1038152499411004063294537 778614374558253047470903)
                ·
                  refine ⟨1167921561837379571206355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 778614374558253047470903 1167921561837379571206355)
                  ·
                    refine ⟨1751882342756069356809533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1167921561837379571206355 1751882342756069356809533)
                    ·
                      refine ⟨656955878533526008803575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1751882342756069356809533 656955878533526008803575)
                      ·
                        rfl

theorem cell23_1279417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 2, 2, 1, 1, 3].length) (baseStart_1279417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1279417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1279417 prefixEnd_1279417 := by exact prefixLift 1279417
  have htrace : WordTrace (prefixWord ++ tailWord_1279417) baseStart_1279417 baseEnd_1279417 := by
    simpa [prefixWord, tailWord_1279417, baseEnd_1279417] using wordTrace_append hprefix tailTrace_1279417
  have hstable : (prefixWord ++ tailWord_1279417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279417).length < 2 ^ (prefixWord ++ tailWord_1279417).sum := by decide
  have hdescent : baseEnd_1279417 < baseStart_1279417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279436 : List Nat := [2, 2, 1, 4, 2, 2, 2, 1, 1, 2, 4]
def baseStart_1279436 : Nat := 118140960795 + 1279436 * 2 ^ 59
def prefixEnd_1279436 : Nat := 4983230072969 + 3 ^ 40 * 1279436 * 2
def baseEnd_1279436 : Nat := 656965634665961434465987

theorem tailTrace_1279436 : CollatzResearch.WordTrace tailWord_1279436 prefixEnd_1279436 656965634665961434465987 := by
  unfold tailWord_1279436
  simp only [CollatzResearch.WordTrace]
  refine ⟨23332432296414678558709081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31109909728552904744945441 23332432296414678558709081)
  ·
    refine ⟨17499324222311008919031811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23332432296414678558709081 17499324222311008919031811)
    ·
      refine ⟨26248986333466513378547717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17499324222311008919031811 26248986333466513378547717)
      ·
        refine ⟨4921684937524971258477697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26248986333466513378547717 4921684937524971258477697)
        ·
          refine ⟨3691263703143728443858273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4921684937524971258477697 3691263703143728443858273)
          ·
            refine ⟨2768447777357796332893705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3691263703143728443858273 2768447777357796332893705)
            ·
              refine ⟨2076335833018347249670279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2768447777357796332893705 2076335833018347249670279)
              ·
                refine ⟨3114503749527520874505419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2076335833018347249670279 3114503749527520874505419)
                ·
                  refine ⟨4671755624291281311758129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3114503749527520874505419 4671755624291281311758129)
                  ·
                    refine ⟨3503816718218460983818597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4671755624291281311758129 3503816718218460983818597)
                    ·
                      refine ⟨656965634665961434465987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3503816718218460983818597 656965634665961434465987)
                      ·
                        rfl

theorem cell23_1279436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_1279436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1279436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1279436 prefixEnd_1279436 := by exact prefixLift 1279436
  have htrace : WordTrace (prefixWord ++ tailWord_1279436) baseStart_1279436 baseEnd_1279436 := by
    simpa [prefixWord, tailWord_1279436, baseEnd_1279436] using wordTrace_append hprefix tailTrace_1279436
  have hstable : (prefixWord ++ tailWord_1279436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279436).length < 2 ^ (prefixWord ++ tailWord_1279436).sum := by decide
  have hdescent : baseEnd_1279436 < baseStart_1279436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279439 : List Nat := [1, 1, 2, 1, 1, 4, 3, 3, 1, 3, 3]
def baseStart_1279439 : Nat := 118140960795 + 1279439 * 2 ^ 59
def prefixEnd_1279439 : Nat := 4983230072969 + 3 ^ 40 * 1279439 * 2
def baseEnd_1279439 : Nat := 656967175107924922728473

theorem tailTrace_1279439 : CollatzResearch.WordTrace tailWord_1279439 prefixEnd_1279439 656967175107924922728473 := by
  unfold tailWord_1279439
  simp only [CollatzResearch.WordTrace]
  refine ⟨46664974011818488629777371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31109982674545659086518247 46664974011818488629777371)
  ·
    refine ⟨69997461017727732944666057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46664974011818488629777371 69997461017727732944666057)
    ·
      refine ⟨52498095763295799708499543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69997461017727732944666057 52498095763295799708499543)
      ·
        refine ⟨78747143644943699562749315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52498095763295799708499543 78747143644943699562749315)
        ·
          refine ⟨118120715467415549344123973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78747143644943699562749315 118120715467415549344123973)
          ·
            refine ⟨22147634150140415502023245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 118120715467415549344123973 22147634150140415502023245)
            ·
              refine ⟨8305362806302655813258717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22147634150140415502023245 8305362806302655813258717)
              ·
                refine ⟨3114511052363495929972019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8305362806302655813258717 3114511052363495929972019)
                ·
                  refine ⟨4671766578545243894958029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3114511052363495929972019 4671766578545243894958029)
                  ·
                    refine ⟨1751912466954466460609261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4671766578545243894958029 1751912466954466460609261)
                    ·
                      refine ⟨656967175107924922728473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1751912466954466460609261 656967175107924922728473)
                      ·
                        rfl

theorem cell23_1279439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 3, 1, 3, 3].length) (baseStart_1279439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1279439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1279439 prefixEnd_1279439 := by exact prefixLift 1279439
  have htrace : WordTrace (prefixWord ++ tailWord_1279439) baseStart_1279439 baseEnd_1279439 := by
    simpa [prefixWord, tailWord_1279439, baseEnd_1279439] using wordTrace_append hprefix tailTrace_1279439
  have hstable : (prefixWord ++ tailWord_1279439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279439).length < 2 ^ (prefixWord ++ tailWord_1279439).sum := by decide
  have hdescent : baseEnd_1279439 < baseStart_1279439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279473 : List Nat := [1, 2, 2, 2, 3, 2, 3, 2, 2, 1, 3]
def baseStart_1279473 : Nat := 118140960795 + 1279473 * 2 ^ 59
def prefixEnd_1279473 : Nat := 4983230072969 + 3 ^ 40 * 1279473 * 2
def baseEnd_1279473 : Nat := 656984633450177789703317

theorem tailTrace_1279473 : CollatzResearch.WordTrace tailWord_1279473 prefixEnd_1279473 656984633450177789703317 := by
  unfold tailWord_1279473
  simp only [CollatzResearch.WordTrace]
  refine ⟨46666214093695312436515073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31110809395796874957676715 46666214093695312436515073)
  ·
    refine ⟨34999660570271484327386305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46666214093695312436515073 34999660570271484327386305)
    ·
      refine ⟨26249745427703613245539729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34999660570271484327386305 26249745427703613245539729)
      ·
        refine ⟨19687309070777709934154797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26249745427703613245539729 19687309070777709934154797)
        ·
          refine ⟨7382740901541641225308049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19687309070777709934154797 7382740901541641225308049)
          ·
            refine ⟨5537055676156230918981037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7382740901541641225308049 5537055676156230918981037)
            ·
              refine ⟨2076395878558586594617889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5537055676156230918981037 2076395878558586594617889)
              ·
                refine ⟨1557296908918939945963417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2076395878558586594617889 1557296908918939945963417)
                ·
                  refine ⟨1167972681689204959472563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1557296908918939945963417 1167972681689204959472563)
                  ·
                    refine ⟨1751959022533807439208845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1167972681689204959472563 1751959022533807439208845)
                    ·
                      refine ⟨656984633450177789703317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1751959022533807439208845 656984633450177789703317)
                      ·
                        rfl

theorem cell23_1279473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 2, 2, 1, 3].length) (baseStart_1279473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1279473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1279473 prefixEnd_1279473 := by exact prefixLift 1279473
  have htrace : WordTrace (prefixWord ++ tailWord_1279473) baseStart_1279473 baseEnd_1279473 := by
    simpa [prefixWord, tailWord_1279473, baseEnd_1279473] using wordTrace_append hprefix tailTrace_1279473
  have hstable : (prefixWord ++ tailWord_1279473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279473).length < 2 ^ (prefixWord ++ tailWord_1279473).sum := by decide
  have hdescent : baseEnd_1279473 < baseStart_1279473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279490 : List Nat := [3, 4, 1, 2, 1, 3, 1, 1, 1, 3, 3]
def baseStart_1279490 : Nat := 118140960795 + 1279490 * 2 ^ 59
def prefixEnd_1279490 : Nat := 4983230072969 + 3 ^ 40 * 1279490 * 2
def baseEnd_1279490 : Nat := 656993362621304223190739

theorem tailTrace_1279490 : CollatzResearch.WordTrace tailWord_1279490 prefixEnd_1279490 656993362621304223190739 := by
  unfold tailWord_1279490
  simp only [CollatzResearch.WordTrace]
  refine ⟨11666708533658431084970981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31111222756422482893255949 11666708533658431084970981)
  ·
    refine ⟨2187507850060955828432059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11666708533658431084970981 2187507850060955828432059)
    ·
      refine ⟨3281261775091433742648089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2187507850060955828432059 3281261775091433742648089)
      ·
        refine ⟨2460946331318575306986067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3281261775091433742648089 2460946331318575306986067)
        ·
          refine ⟨3691419496977862960479101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2460946331318575306986067 3691419496977862960479101)
          ·
            refine ⟨1384282311366698610179663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3691419496977862960479101 1384282311366698610179663)
            ·
              refine ⟨2076423467050047915269495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1384282311366698610179663 2076423467050047915269495)
              ·
                refine ⟨3114635200575071872904243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2076423467050047915269495 3114635200575071872904243)
                ·
                  refine ⟨4671952800862607809356365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3114635200575071872904243 4671952800862607809356365)
                  ·
                    refine ⟨1751982300323477928508637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4671952800862607809356365 1751982300323477928508637)
                    ·
                      refine ⟨656993362621304223190739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1751982300323477928508637 656993362621304223190739)
                      ·
                        rfl

theorem cell23_1279490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_1279490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1279490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1279490 prefixEnd_1279490 := by exact prefixLift 1279490
  have htrace : WordTrace (prefixWord ++ tailWord_1279490) baseStart_1279490 baseEnd_1279490 := by
    simpa [prefixWord, tailWord_1279490, baseEnd_1279490] using wordTrace_append hprefix tailTrace_1279490
  have hstable : (prefixWord ++ tailWord_1279490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279490).length < 2 ^ (prefixWord ++ tailWord_1279490).sum := by decide
  have hdescent : baseEnd_1279490 < baseStart_1279490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279494 : List Nat := [6, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3]
def baseStart_1279494 : Nat := 118140960795 + 1279494 * 2 ^ 59
def prefixEnd_1279494 : Nat := 4983230072969 + 3 ^ 40 * 1279494 * 2
def baseEnd_1279494 : Nat := 656995416543922207540721

theorem tailTrace_1279494 : CollatzResearch.WordTrace tailWord_1279494 prefixEnd_1279494 656995416543922207540721 := by
  unfold tailWord_1279494
  simp only [CollatzResearch.WordTrace]
  refine ⟨1458343125831851031969673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 31111320017746155348686357 1458343125831851031969673)
  ·
    refine ⟨1093757344373888273977255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1458343125831851031969673 1093757344373888273977255)
    ·
      refine ⟨1640636016560832410965883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1093757344373888273977255 1640636016560832410965883)
      ·
        refine ⟨2460954024841248616448825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1640636016560832410965883 2460954024841248616448825)
        ·
          refine ⟨1845715518630936462336619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2460954024841248616448825 1845715518630936462336619)
          ·
            refine ⟨2768573277946404693504929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1845715518630936462336619 2768573277946404693504929)
            ·
              refine ⟨2076429958459803520128697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2768573277946404693504929 2076429958459803520128697)
              ·
                refine ⟨1557322468844852640096523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2076429958459803520128697 1557322468844852640096523)
                ·
                  refine ⟨2335983703267278960144785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1557322468844852640096523 2335983703267278960144785)
                  ·
                    refine ⟨1751987777450459220108589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2335983703267278960144785 1751987777450459220108589)
                    ·
                      refine ⟨656995416543922207540721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1751987777450459220108589 656995416543922207540721)
                      ·
                        rfl

theorem cell23_1279494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_1279494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1279494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1279494 prefixEnd_1279494 := by exact prefixLift 1279494
  have htrace : WordTrace (prefixWord ++ tailWord_1279494) baseStart_1279494 baseEnd_1279494 := by
    simpa [prefixWord, tailWord_1279494, baseEnd_1279494] using wordTrace_append hprefix tailTrace_1279494
  have hstable : (prefixWord ++ tailWord_1279494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279494).length < 2 ^ (prefixWord ++ tailWord_1279494).sum := by decide
  have hdescent : baseEnd_1279494 < baseStart_1279494 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279500 : List Nat := [2, 2, 1, 2, 5, 1, 2, 2, 1, 3, 2]
def baseStart_1279500 : Nat := 118140960795 + 1279500 * 2 ^ 59
def prefixEnd_1279500 : Nat := 4983230072969 + 3 ^ 40 * 1279500 * 2
def baseEnd_1279500 : Nat := 656998497427849184065693

theorem tailTrace_1279500 : CollatzResearch.WordTrace tailWord_1279500 prefixEnd_1279500 656998497427849184065693 := by
  unfold tailWord_1279500
  simp only [CollatzResearch.WordTrace]
  refine ⟨23333599432298748023873977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31111465909731664031831969 23333599432298748023873977)
  ·
    refine ⟨17500199574224061017905483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23333599432298748023873977 17500199574224061017905483)
    ·
      refine ⟨26250299361336091526858225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17500199574224061017905483 26250299361336091526858225)
      ·
        refine ⟨19687724521002068645143669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26250299361336091526858225 19687724521002068645143669)
        ·
          refine ⟨1845724173843943935482219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19687724521002068645143669 1845724173843943935482219)
          ·
            refine ⟨2768586260765915903223329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1845724173843943935482219 2768586260765915903223329)
            ·
              refine ⟨2076439695574436927417497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2768586260765915903223329 2076439695574436927417497)
              ·
                refine ⟨1557329771680827695563123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2076439695574436927417497 1557329771680827695563123)
                ·
                  refine ⟨2335994657521241543344685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1557329771680827695563123 2335994657521241543344685)
                  ·
                    refine ⟨875997996570465578754257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2335994657521241543344685 875997996570465578754257)
                    ·
                      refine ⟨656998497427849184065693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 875997996570465578754257 656998497427849184065693)
                      ·
                        rfl

theorem cell23_1279500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 2, 1, 3, 2].length) (baseStart_1279500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1279500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1279500 prefixEnd_1279500 := by exact prefixLift 1279500
  have htrace : WordTrace (prefixWord ++ tailWord_1279500) baseStart_1279500 baseEnd_1279500 := by
    simpa [prefixWord, tailWord_1279500, baseEnd_1279500] using wordTrace_append hprefix tailTrace_1279500
  have hstable : (prefixWord ++ tailWord_1279500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279500).length < 2 ^ (prefixWord ++ tailWord_1279500).sum := by decide
  have hdescent : baseEnd_1279500 < baseStart_1279500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279530 : List Nat := [3, 1, 4, 1, 1, 1, 2, 4, 2, 2, 2]
def baseStart_1279530 : Nat := 118140960795 + 1279530 * 2 ^ 59
def prefixEnd_1279530 : Nat := 4983230072969 + 3 ^ 40 * 1279530 * 2
def baseEnd_1279530 : Nat := 657013901847484066690555

theorem tailTrace_1279530 : CollatzResearch.WordTrace tailWord_1279530 prefixEnd_1279530 657013901847484066690555 := by
  unfold tailWord_1279530
  simp only [CollatzResearch.WordTrace]
  refine ⟨11667073263622202792835011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31112195369659207447560029 11667073263622202792835011)
  ·
    refine ⟨17500609895433304189252517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11667073263622202792835011 17500609895433304189252517)
    ·
      refine ⟨3281364355393744535484847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17500609895433304189252517 3281364355393744535484847)
      ·
        refine ⟨4922046533090616803227271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3281364355393744535484847 4922046533090616803227271)
        ·
          refine ⟨7383069799635925204840907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4922046533090616803227271 7383069799635925204840907)
          ·
            refine ⟨11074604699453887807261361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7383069799635925204840907 11074604699453887807261361)
            ·
              refine ⟨8305953524590415855446021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11074604699453887807261361 8305953524590415855446021)
              ·
                refine ⟨1557366285860702972896129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8305953524590415855446021 1557366285860702972896129)
                ·
                  refine ⟨1168024714395527229672097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1557366285860702972896129 1168024714395527229672097)
                  ·
                    refine ⟨876018535796645422254073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1168024714395527229672097 876018535796645422254073)
                    ·
                      refine ⟨657013901847484066690555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 876018535796645422254073 657013901847484066690555)
                      ·
                        rfl

theorem cell23_1279530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 4, 2, 2, 2].length) (baseStart_1279530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1279530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1279530 prefixEnd_1279530 := by exact prefixLift 1279530
  have htrace : WordTrace (prefixWord ++ tailWord_1279530) baseStart_1279530 baseEnd_1279530 := by
    simpa [prefixWord, tailWord_1279530, baseEnd_1279530] using wordTrace_append hprefix tailTrace_1279530
  have hstable : (prefixWord ++ tailWord_1279530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279530).length < 2 ^ (prefixWord ++ tailWord_1279530).sum := by decide
  have hdescent : baseEnd_1279530 < baseStart_1279530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279596 : List Nat := [2, 2, 1, 1, 3, 1, 1, 5, 3, 4]
def baseStart_1279596 : Nat := 118140960795 + 1279596 * 2 ^ 59
def prefixEnd_1279596 : Nat := 4983230072969 + 3 ^ 40 * 1279596 * 2
def baseEnd_1279596 : Nat := 219015930523560269488417

theorem tailTrace_1279596 : CollatzResearch.WordTrace tailWord_1279596 prefixEnd_1279596 219015930523560269488417 := by
  unfold tailWord_1279596
  simp only [CollatzResearch.WordTrace]
  refine ⟨23335350136124852221621321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31113800181499802962161761 23335350136124852221621321)
  ·
    refine ⟨17501512602093639166215991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23335350136124852221621321 17501512602093639166215991)
    ·
      refine ⟨26252268903140458749323987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17501512602093639166215991 26252268903140458749323987)
      ·
        refine ⟨39378403354710688123985981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26252268903140458749323987 39378403354710688123985981)
        ·
          refine ⟨14766901258016508046494743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39378403354710688123985981 14766901258016508046494743)
          ·
            refine ⟨22150351887024762069742115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14766901258016508046494743 22150351887024762069742115)
            ·
              refine ⟨33225527830537143104613173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22150351887024762069742115 33225527830537143104613173)
              ·
                refine ⟨3114893234112857166057485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33225527830537143104613173 3114893234112857166057485)
                ·
                  refine ⟨1168084962792321437271557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3114893234112857166057485 1168084962792321437271557)
                  ·
                    refine ⟨219015930523560269488417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1168084962792321437271557 219015930523560269488417)
                    ·
                      rfl

theorem cell23_1279596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 4].length) (baseStart_1279596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1279596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1279596 prefixEnd_1279596 := by exact prefixLift 1279596
  have htrace : WordTrace (prefixWord ++ tailWord_1279596) baseStart_1279596 baseEnd_1279596 := by
    simpa [prefixWord, tailWord_1279596, baseEnd_1279596] using wordTrace_append hprefix tailTrace_1279596
  have hstable : (prefixWord ++ tailWord_1279596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279596).length < 2 ^ (prefixWord ++ tailWord_1279596).sum := by decide
  have hdescent : baseEnd_1279596 < baseStart_1279596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279599 : List Nat := [1, 1, 2, 1, 3, 2, 1, 2, 2, 4, 4]
def baseStart_1279599 : Nat := 118140960795 + 1279599 * 2 ^ 59
def prefixEnd_1279599 : Nat := 4983230072969 + 3 ^ 40 * 1279599 * 2
def baseEnd_1279599 : Nat := 657049332012644296727737

theorem tailTrace_1279599 : CollatzResearch.WordTrace tailWord_1279599 prefixEnd_1279599 657049332012644296727737 := by
  unfold tailWord_1279599
  simp only [CollatzResearch.WordTrace]
  refine ⟨46670809691238835955601851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31113873127492557303734567 46670809691238835955601851)
  ·
    refine ⟨70006214536858253933402777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46670809691238835955601851 70006214536858253933402777)
    ·
      refine ⟨52504660902643690450052083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70006214536858253933402777 52504660902643690450052083)
      ·
        refine ⟨78756991353965535675078125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52504660902643690450052083 78756991353965535675078125)
        ·
          refine ⟨29533871757737075878154297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78756991353965535675078125 29533871757737075878154297)
          ·
            refine ⟨22150403818302806908615723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29533871757737075878154297 22150403818302806908615723)
            ·
              refine ⟨33225605727454210362923585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22150403818302806908615723 33225605727454210362923585)
              ·
                refine ⟨24919204295590657772192689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33225605727454210362923585 24919204295590657772192689)
                ·
                  refine ⟨18689403221692993329144517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24919204295590657772192689 18689403221692993329144517)
                  ·
                    refine ⟨3504263104067436249214597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18689403221692993329144517 3504263104067436249214597)
                    ·
                      refine ⟨657049332012644296727737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3504263104067436249214597 657049332012644296727737)
                      ·
                        rfl

theorem cell23_1279599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 4, 4].length) (baseStart_1279599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1279599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1279599 prefixEnd_1279599 := by exact prefixLift 1279599
  have htrace : WordTrace (prefixWord ++ tailWord_1279599) baseStart_1279599 baseEnd_1279599 := by
    simpa [prefixWord, tailWord_1279599, baseEnd_1279599] using wordTrace_append hprefix tailTrace_1279599
  have hstable : (prefixWord ++ tailWord_1279599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279599).length < 2 ^ (prefixWord ++ tailWord_1279599).sum := by decide
  have hdescent : baseEnd_1279599 < baseStart_1279599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279613 : List Nat := [1, 4, 1, 1, 4, 2, 1, 2, 3, 4]
def baseStart_1279613 : Nat := 118140960795 + 1279613 * 2 ^ 59
def prefixEnd_1279613 : Nat := 4983230072969 + 3 ^ 40 * 1279613 * 2
def baseEnd_1279613 : Nat := 219018840247269080650891

theorem tailTrace_1279613 : CollatzResearch.WordTrace tailWord_1279613 prefixEnd_1279613 219018840247269080650891 := by
  unfold tailWord_1279613
  simp only [CollatzResearch.WordTrace]
  refine ⟨46671320313188116346611493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31114213542125410897740995 46671320313188116346611493)
  ·
    refine ⟨8750872558722771814989655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46671320313188116346611493 8750872558722771814989655)
    ·
      refine ⟨13126308838084157722484483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8750872558722771814989655 13126308838084157722484483)
      ·
        refine ⟨19689463257126236583726725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13126308838084157722484483 19689463257126236583726725)
        ·
          refine ⟨3691774360711169359448761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19689463257126236583726725 3691774360711169359448761)
          ·
            refine ⟨2768830770533377019586571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3691774360711169359448761 2768830770533377019586571)
            ·
              refine ⟨4153246155800065529379857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2768830770533377019586571 4153246155800065529379857)
              ·
                refine ⟨3114934616850049147034893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4153246155800065529379857 3114934616850049147034893)
                ·
                  refine ⟨1168100481318768430138085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3114934616850049147034893 1168100481318768430138085)
                  ·
                    refine ⟨219018840247269080650891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1168100481318768430138085 219018840247269080650891)
                    ·
                      rfl

theorem cell23_1279613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 2, 3, 4].length) (baseStart_1279613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1279613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1279613 prefixEnd_1279613 := by exact prefixLift 1279613
  have htrace : WordTrace (prefixWord ++ tailWord_1279613) baseStart_1279613 baseEnd_1279613 := by
    simpa [prefixWord, tailWord_1279613, baseEnd_1279613] using wordTrace_append hprefix tailTrace_1279613
  have hstable : (prefixWord ++ tailWord_1279613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279613).length < 2 ^ (prefixWord ++ tailWord_1279613).sum := by decide
  have hdescent : baseEnd_1279613 < baseStart_1279613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279620 : List Nat := [2, 3, 2, 1, 4, 2, 1, 1, 2, 1, 4]
def baseStart_1279620 : Nat := 118140960795 + 1279620 * 2 ^ 59
def prefixEnd_1279620 : Nat := 4983230072969 + 3 ^ 40 * 1279620 * 2
def baseEnd_1279620 : Nat := 657060115106388714565141

theorem tailTrace_1279620 : CollatzResearch.WordTrace tailWord_1279620 prefixEnd_1279620 657060115106388714565141 := by
  unfold tailWord_1279620
  simp only [CollatzResearch.WordTrace]
  refine ⟨23335787812081378271058157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31114383749441837694744209 23335787812081378271058157)
  ·
    refine ⟨8750920429530516851646809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23335787812081378271058157 8750920429530516851646809)
    ·
      refine ⟨6563190322147887638735107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8750920429530516851646809 6563190322147887638735107)
      ·
        refine ⟨9844785483221831458102661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6563190322147887638735107 9844785483221831458102661)
        ·
          refine ⟨1845897278104093398394249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9844785483221831458102661 1845897278104093398394249)
          ·
            refine ⟨1384422958578070048795687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1845897278104093398394249 1384422958578070048795687)
            ·
              refine ⟨2076634437867105073193531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1384422958578070048795687 2076634437867105073193531)
              ·
                refine ⟨3114951656800657609790297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2076634437867105073193531 3114951656800657609790297)
                ·
                  refine ⟨2336213742600493207342723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3114951656800657609790297 2336213742600493207342723)
                  ·
                    refine ⟨3504320613900739811014085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2336213742600493207342723 3504320613900739811014085)
                    ·
                      refine ⟨657060115106388714565141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3504320613900739811014085 657060115106388714565141)
                      ·
                        rfl

theorem cell23_1279620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 1, 2, 1, 4].length) (baseStart_1279620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1279620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1279620 prefixEnd_1279620 := by exact prefixLift 1279620
  have htrace : WordTrace (prefixWord ++ tailWord_1279620) baseStart_1279620 baseEnd_1279620 := by
    simpa [prefixWord, tailWord_1279620, baseEnd_1279620] using wordTrace_append hprefix tailTrace_1279620
  have hstable : (prefixWord ++ tailWord_1279620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279620).length < 2 ^ (prefixWord ++ tailWord_1279620).sum := by decide
  have hdescent : baseEnd_1279620 < baseStart_1279620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279623 : List Nat := [1, 1, 4, 2, 1, 3, 3, 1, 2, 2, 3]
def baseStart_1279623 : Nat := 118140960795 + 1279623 * 2 ^ 59
def prefixEnd_1279623 : Nat := 4983230072969 + 3 ^ 40 * 1279623 * 2
def baseEnd_1279623 : Nat := 657061655548352202827627

theorem tailTrace_1279623 : CollatzResearch.WordTrace tailWord_1279623 prefixEnd_1279623 657061655548352202827627 := by
  unfold tailWord_1279623
  simp only [CollatzResearch.WordTrace]
  refine ⟨46671685043151888054475523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31114456695434592036317015 46671685043151888054475523)
  ·
    refine ⟨70007527564727832081713285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46671685043151888054475523 70007527564727832081713285)
    ·
      refine ⟨13126411418386468515321241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70007527564727832081713285 13126411418386468515321241)
      ·
        refine ⟨9844808563789851386490931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13126411418386468515321241 9844808563789851386490931)
        ·
          refine ⟨14767212845684777079736397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9844808563789851386490931 14767212845684777079736397)
          ·
            refine ⟨5537704817131791404901149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14767212845684777079736397 5537704817131791404901149)
            ·
              refine ⟨2076639306424421776837931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5537704817131791404901149 2076639306424421776837931)
              ·
                refine ⟨3114958959636632665256897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2076639306424421776837931 3114958959636632665256897)
                ·
                  refine ⟨2336219219727474498942673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3114958959636632665256897 2336219219727474498942673)
                  ·
                    refine ⟨1752164414795605874207005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2336219219727474498942673 1752164414795605874207005)
                    ·
                      refine ⟨657061655548352202827627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1752164414795605874207005 657061655548352202827627)
                      ·
                        rfl

theorem cell23_1279623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 1, 2, 2, 3].length) (baseStart_1279623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1279623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1279623 prefixEnd_1279623 := by exact prefixLift 1279623
  have htrace : WordTrace (prefixWord ++ tailWord_1279623) baseStart_1279623 baseEnd_1279623 := by
    simpa [prefixWord, tailWord_1279623, baseEnd_1279623] using wordTrace_append hprefix tailTrace_1279623
  have hstable : (prefixWord ++ tailWord_1279623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279623).length < 2 ^ (prefixWord ++ tailWord_1279623).sum := by decide
  have hdescent : baseEnd_1279623 < baseStart_1279623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279630 : List Nat := [4, 1, 1, 3, 1, 2, 1, 5, 1, 4]
def baseStart_1279630 : Nat := 118140960795 + 1279630 * 2 ^ 59
def prefixEnd_1279630 : Nat := 4983230072969 + 3 ^ 40 * 1279630 * 2
def baseEnd_1279630 : Nat := 219021749970977891813365

theorem tailTrace_1279630 : CollatzResearch.WordTrace tailWord_1279630 prefixEnd_1279630 219021749970977891813365 := by
  unfold tailWord_1279630
  simp only [CollatzResearch.WordTrace]
  refine ⟨5833992544265816031247543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31114626902751018833320229 5833992544265816031247543)
  ·
    refine ⟨8750988816398724046871315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5833992544265816031247543 8750988816398724046871315)
    ·
      refine ⟨13126483224598086070306973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8750988816398724046871315 13126483224598086070306973)
      ·
        refine ⟨4922431209224282276365115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13126483224598086070306973 4922431209224282276365115)
        ·
          refine ⟨7383646813836423414547673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4922431209224282276365115 7383646813836423414547673)
          ·
            refine ⟨5537735110377317560910755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7383646813836423414547673 5537735110377317560910755)
            ·
              refine ⟨8306602665565976341366133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5537735110377317560910755 8306602665565976341366133)
              ·
                refine ⟨778743999896810282003075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8306602665565976341366133 778743999896810282003075)
                ·
                  refine ⟨1168115999845215423004613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 778743999896810282003075 1168115999845215423004613)
                  ·
                    refine ⟨219021749970977891813365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1168115999845215423004613 219021749970977891813365)
                    ·
                      rfl

theorem cell23_1279630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 5, 1, 4].length) (baseStart_1279630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1279630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1279630 prefixEnd_1279630 := by exact prefixLift 1279630
  have htrace : WordTrace (prefixWord ++ tailWord_1279630) baseStart_1279630 baseEnd_1279630 := by
    simpa [prefixWord, tailWord_1279630, baseEnd_1279630] using wordTrace_append hprefix tailTrace_1279630
  have hstable : (prefixWord ++ tailWord_1279630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279630).length < 2 ^ (prefixWord ++ tailWord_1279630).sum := by decide
  have hdescent : baseEnd_1279630 < baseStart_1279630 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279653 : List Nat := [1, 3, 1, 2, 1, 2, 3, 3, 3, 1, 3]
def baseStart_1279653 : Nat := 118140960795 + 1279653 * 2 ^ 59
def prefixEnd_1279653 : Nat := 4983230072969 + 3 ^ 40 * 1279653 * 2
def baseEnd_1279653 : Nat := 657077059967987085452489

theorem tailTrace_1279653 : CollatzResearch.WordTrace tailWord_1279653 prefixEnd_1279653 657077059967987085452489 := by
  unfold tailWord_1279653
  simp only [CollatzResearch.WordTrace]
  refine ⟨46672779233043203178067613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31115186155362135452045075 46672779233043203178067613)
  ·
    refine ⟨17502292212391201191775355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46672779233043203178067613 17502292212391201191775355)
    ·
      refine ⟨26253438318586801787663033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17502292212391201191775355 26253438318586801787663033)
      ·
        refine ⟨19690078738940101340747275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26253438318586801787663033 19690078738940101340747275)
        ·
          refine ⟨29535118108410152011120913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19690078738940101340747275 29535118108410152011120913)
          ·
            refine ⟨22151338581307614008340685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29535118108410152011120913 22151338581307614008340685)
            ·
              refine ⟨8306751967990355253127757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22151338581307614008340685 8306751967990355253127757)
              ·
                refine ⟨3115031987996383219922909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8306751967990355253127757 3115031987996383219922909)
                ·
                  refine ⟨1168136995498643707471091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3115031987996383219922909 1168136995498643707471091)
                  ·
                    refine ⟨1752205493247965561206637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1168136995498643707471091 1752205493247965561206637)
                    ·
                      refine ⟨657077059967987085452489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1752205493247965561206637 657077059967987085452489)
                      ·
                        rfl

theorem cell23_1279653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 3, 3, 1, 3].length) (baseStart_1279653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1279653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1279653 prefixEnd_1279653 := by exact prefixLift 1279653
  have htrace : WordTrace (prefixWord ++ tailWord_1279653) baseStart_1279653 baseEnd_1279653 := by
    simpa [prefixWord, tailWord_1279653, baseEnd_1279653] using wordTrace_append hprefix tailTrace_1279653
  have hstable : (prefixWord ++ tailWord_1279653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279653).length < 2 ^ (prefixWord ++ tailWord_1279653).sum := by decide
  have hdescent : baseEnd_1279653 < baseStart_1279653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279703 : List Nat := [1, 1, 3, 2, 1, 3, 2, 4, 2, 4]
def baseStart_1279703 : Nat := 118140960795 + 1279703 * 2 ^ 59
def prefixEnd_1279703 : Nat := 4983230072969 + 3 ^ 40 * 1279703 * 2
def baseEnd_1279703 : Nat := 219034244666903963275753

theorem tailTrace_1279703 : CollatzResearch.WordTrace tailWord_1279703 prefixEnd_1279703 219034244666903963275753 := by
  unfold tailWord_1279703
  simp only [CollatzResearch.WordTrace]
  refine ⟨46674602882862061717387763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31116401921908041144925175 46674602882862061717387763)
  ·
    refine ⟨70011904324293092576081645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46674602882862061717387763 70011904324293092576081645)
    ·
      refine ⟨26254464121609909716030617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70011904324293092576081645 26254464121609909716030617)
      ·
        refine ⟨19690848091207432287022963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26254464121609909716030617 19690848091207432287022963)
        ·
          refine ⟨29536272136811148430534445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19690848091207432287022963 29536272136811148430534445)
          ·
            refine ⟨11076102051304180661450417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29536272136811148430534445 11076102051304180661450417)
            ·
              refine ⟨8307076538478135496087813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11076102051304180661450417 8307076538478135496087813)
              ·
                refine ⟨1557576850964650405516465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8307076538478135496087813 1557576850964650405516465)
                ·
                  refine ⟨1168182638223487804137349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1557576850964650405516465 1168182638223487804137349)
                  ·
                    refine ⟨219034244666903963275753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1168182638223487804137349 219034244666903963275753)
                    ·
                      rfl

theorem cell23_1279703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 4, 2, 4].length) (baseStart_1279703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1279703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1279703 prefixEnd_1279703 := by exact prefixLift 1279703
  have htrace : WordTrace (prefixWord ++ tailWord_1279703) baseStart_1279703 baseEnd_1279703 := by
    simpa [prefixWord, tailWord_1279703, baseEnd_1279703] using wordTrace_append hprefix tailTrace_1279703
  have hstable : (prefixWord ++ tailWord_1279703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279703).length < 2 ^ (prefixWord ++ tailWord_1279703).sum := by decide
  have hdescent : baseEnd_1279703 < baseStart_1279703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279706 : List Nat := [3, 1, 1, 2, 2, 3, 1, 2, 1, 1, 6]
def baseStart_1279706 : Nat := 118140960795 + 1279706 * 2 ^ 59
def prefixEnd_1279706 : Nat := 4983230072969 + 3 ^ 40 * 1279706 * 2
def baseEnd_1279706 : Nat := 657104274442675378089745

theorem tailTrace_1279706 : CollatzResearch.WordTrace tailWord_1279706 prefixEnd_1279706 657104274442675378089745 := by
  unfold tailWord_1279706
  simp only [CollatzResearch.WordTrace]
  refine ⟨11668678075462798307436743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31116474867900795486497981 11668678075462798307436743)
  ·
    refine ⟨17503017113194197461155115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11668678075462798307436743 17503017113194197461155115)
    ·
      refine ⟨26254525669791296191732673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17503017113194197461155115 26254525669791296191732673)
      ·
        refine ⟨19690894252343472143799505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26254525669791296191732673 19690894252343472143799505)
        ·
          refine ⟨14768170689257604107849629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19690894252343472143799505 14768170689257604107849629)
          ·
            refine ⟨5538064008471601540443611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14768170689257604107849629 5538064008471601540443611)
            ·
              refine ⟨8307096012707402310665417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5538064008471601540443611 8307096012707402310665417)
              ·
                refine ⟨6230322009530551732999063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8307096012707402310665417 6230322009530551732999063)
                ·
                  refine ⟨9345483014295827599498595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6230322009530551732999063 9345483014295827599498595)
                  ·
                    refine ⟨14018224521443741399247893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9345483014295827599498595 14018224521443741399247893)
                    ·
                      refine ⟨657104274442675378089745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14018224521443741399247893 657104274442675378089745)
                      ·
                        rfl

theorem cell23_1279706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 2, 1, 1, 6].length) (baseStart_1279706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1279706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1279706 prefixEnd_1279706 := by exact prefixLift 1279706
  have htrace : WordTrace (prefixWord ++ tailWord_1279706) baseStart_1279706 baseEnd_1279706 := by
    simpa [prefixWord, tailWord_1279706, baseEnd_1279706] using wordTrace_append hprefix tailTrace_1279706
  have hstable : (prefixWord ++ tailWord_1279706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279706).length < 2 ^ (prefixWord ++ tailWord_1279706).sum := by decide
  have hdescent : baseEnd_1279706 < baseStart_1279706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279716 : List Nat := [2, 3, 1, 1, 1, 3, 4, 8]
def baseStart_1279716 : Nat := 118140960795 + 1279716 * 2 ^ 59
def prefixEnd_1279716 : Nat := 4983230072969 + 3 ^ 40 * 1279716 * 2
def baseEnd_1279716 : Nat := 24337385527748901443137

theorem tailTrace_1279716 : CollatzResearch.WordTrace tailWord_1279716 prefixEnd_1279716 24337385527748901443137 := by
  unfold tailWord_1279716
  simp only [CollatzResearch.WordTrace]
  refine ⟨23337538515907482468805501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31116718021209976625074001 23337538515907482468805501)
  ·
    refine ⟨8751576943465305925802063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23337538515907482468805501 8751576943465305925802063)
    ·
      refine ⟨13127365415197958888703095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8751576943465305925802063 13127365415197958888703095)
      ·
        refine ⟨19691048122796938333054643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13127365415197958888703095 19691048122796938333054643)
        ·
          refine ⟨29536572184195407499581965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19691048122796938333054643 29536572184195407499581965)
          ·
            refine ⟨11076214569073277812343237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29536572184195407499581965 11076214569073277812343237)
            ·
              refine ⟨2076790231701239589814357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11076214569073277812343237 2076790231701239589814357)
              ·
                refine ⟨24337385527748901443137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2076790231701239589814357 24337385527748901443137)
                ·
                  rfl

theorem cell23_1279716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 8].length) (baseStart_1279716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1279716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1279716 prefixEnd_1279716 := by exact prefixLift 1279716
  have htrace : WordTrace (prefixWord ++ tailWord_1279716) baseStart_1279716 baseEnd_1279716 := by
    simpa [prefixWord, tailWord_1279716, baseEnd_1279716] using wordTrace_append hprefix tailTrace_1279716
  have hstable : (prefixWord ++ tailWord_1279716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279716).length < 2 ^ (prefixWord ++ tailWord_1279716).sum := by decide
  have hdescent : baseEnd_1279716 < baseStart_1279716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279720 : List Nat := [2, 1, 4, 1, 3, 2, 1, 3, 2, 4]
def baseStart_1279720 : Nat := 118140960795 + 1279720 * 2 ^ 59
def prefixEnd_1279720 : Nat := 4983230072969 + 3 ^ 40 * 1279720 * 2
def baseEnd_1279720 : Nat := 219037154390612774438227

theorem tailTrace_1279720 : CollatzResearch.WordTrace tailWord_1279720 prefixEnd_1279720 219037154390612774438227 := by
  unfold tailWord_1279720
  simp only [CollatzResearch.WordTrace]
  refine ⟨23337611461900236810378307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31116815282533649080504409 23337611461900236810378307)
  ·
    refine ⟨35006417192850355215567461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23337611461900236810378307 35006417192850355215567461)
    ·
      refine ⟨6563703223659441602918899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35006417192850355215567461 6563703223659441602918899)
      ·
        refine ⟨9845554835489162404378349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6563703223659441602918899 9845554835489162404378349)
        ·
          refine ⟨3692083063308435901641881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9845554835489162404378349 3692083063308435901641881)
          ·
            refine ⟨2769062297481326926231411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3692083063308435901641881 2769062297481326926231411)
            ·
              refine ⟨4153593446221990389347117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2769062297481326926231411 4153593446221990389347117)
              ·
                refine ⟨1557597542333246396005169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4153593446221990389347117 1557597542333246396005169)
                ·
                  refine ⟨1168198156749934797003877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1557597542333246396005169 1168198156749934797003877)
                  ·
                    refine ⟨219037154390612774438227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1168198156749934797003877 219037154390612774438227)
                    ·
                      rfl

theorem cell23_1279720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 3, 2, 4].length) (baseStart_1279720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1279720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1279720 prefixEnd_1279720 := by exact prefixLift 1279720
  have htrace : WordTrace (prefixWord ++ tailWord_1279720) baseStart_1279720 baseEnd_1279720 := by
    simpa [prefixWord, tailWord_1279720, baseEnd_1279720] using wordTrace_append hprefix tailTrace_1279720
  have hstable : (prefixWord ++ tailWord_1279720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279720).length < 2 ^ (prefixWord ++ tailWord_1279720).sum := by decide
  have hdescent : baseEnd_1279720 < baseStart_1279720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279743 : List Nat := [1, 1, 2, 2, 1, 3, 2, 1, 6, 1, 3]
def baseStart_1279743 : Nat := 118140960795 + 1279743 * 2 ^ 59
def prefixEnd_1279743 : Nat := 4983230072969 + 3 ^ 40 * 1279743 * 2
def baseEnd_1279743 : Nat := 657123273226891733327075

theorem tailTrace_1279743 : CollatzResearch.WordTrace tailWord_1279743 prefixEnd_1279743 657123273226891733327075 := by
  unfold tailWord_1279743
  simp only [CollatzResearch.WordTrace]
  refine ⟨46676061802717148548843883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31117374535144765699229255 46676061802717148548843883)
  ·
    refine ⟨70014092704075722823265825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46676061802717148548843883 70014092704075722823265825)
    ·
      refine ⟨52510569528056792117449369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70014092704075722823265825 52510569528056792117449369)
      ·
        refine ⟨39382927146042594088087027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52510569528056792117449369 39382927146042594088087027)
        ·
          refine ⟨59074390719063891132130541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39382927146042594088087027 59074390719063891132130541)
          ·
            refine ⟨22152896519648959174548953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59074390719063891132130541 22152896519648959174548953)
            ·
              refine ⟨16614672389736719380911715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22152896519648959174548953 16614672389736719380911715)
              ·
                refine ⟨24922008584605079071367573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16614672389736719380911715 24922008584605079071367573)
                ·
                  refine ⟨1168219152403363081470355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 24922008584605079071367573 1168219152403363081470355)
                  ·
                    refine ⟨1752328728605044622205533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1168219152403363081470355 1752328728605044622205533)
                    ·
                      refine ⟨657123273226891733327075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1752328728605044622205533 657123273226891733327075)
                      ·
                        rfl

theorem cell23_1279743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 6, 1, 3].length) (baseStart_1279743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1279743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1279743 prefixEnd_1279743 := by exact prefixLift 1279743
  have htrace : WordTrace (prefixWord ++ tailWord_1279743) baseStart_1279743 baseEnd_1279743 := by
    simpa [prefixWord, tailWord_1279743, baseEnd_1279743] using wordTrace_append hprefix tailTrace_1279743
  have hstable : (prefixWord ++ tailWord_1279743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279743).length < 2 ^ (prefixWord ++ tailWord_1279743).sum := by decide
  have hdescent : baseEnd_1279743 < baseStart_1279743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279756 : List Nat := [2, 2, 1, 2, 2, 1, 2, 2, 2, 2, 5]
def baseStart_1279756 : Nat := 118140960795 + 1279756 * 2 ^ 59
def prefixEnd_1279756 : Nat := 4983230072969 + 3 ^ 40 * 1279756 * 2
def baseEnd_1279756 : Nat := 657129948475400182464515

theorem tailTrace_1279756 : CollatzResearch.WordTrace tailWord_1279756 prefixEnd_1279756 657129948475400182464515 := by
  unfold tailWord_1279756
  simp only [CollatzResearch.WordTrace]
  refine ⟨23338267975835025884533561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31117690634446701179378081 23338267975835025884533561)
  ·
    refine ⟨17503700981876269413400171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23338267975835025884533561 17503700981876269413400171)
    ·
      refine ⟨26255551472814404120100257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17503700981876269413400171 26255551472814404120100257)
      ·
        refine ⟨19691663604610803090075193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26255551472814404120100257 19691663604610803090075193)
        ·
          refine ⟨14768747703458102317556395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19691663604610803090075193 14768747703458102317556395)
          ·
            refine ⟨22153121555187153476334593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14768747703458102317556395 22153121555187153476334593)
            ·
              refine ⟨16614841166390365107250945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22153121555187153476334593 16614841166390365107250945)
              ·
                refine ⟨12461130874792773830438209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16614841166390365107250945 12461130874792773830438209)
                ·
                  refine ⟨9345848156094580372828657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12461130874792773830438209 9345848156094580372828657)
                  ·
                    refine ⟨7009386117070935279621493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9345848156094580372828657 7009386117070935279621493)
                    ·
                      refine ⟨657129948475400182464515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7009386117070935279621493 657129948475400182464515)
                      ·
                        rfl

theorem cell23_1279756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 2, 2, 5].length) (baseStart_1279756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1279756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1279756 prefixEnd_1279756 := by exact prefixLift 1279756
  have htrace : WordTrace (prefixWord ++ tailWord_1279756) baseStart_1279756 baseEnd_1279756 := by
    simpa [prefixWord, tailWord_1279756, baseEnd_1279756] using wordTrace_append hprefix tailTrace_1279756
  have hstable : (prefixWord ++ tailWord_1279756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279756).length < 2 ^ (prefixWord ++ tailWord_1279756).sum := by decide
  have hdescent : baseEnd_1279756 < baseStart_1279756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279770 : List Nat := [3, 1, 1, 3, 2, 2, 1, 2, 3, 3, 2]
def baseStart_1279770 : Nat := 118140960795 + 1279770 * 2 ^ 59
def prefixEnd_1279770 : Nat := 4983230072969 + 3 ^ 40 * 1279770 * 2
def baseEnd_1279770 : Nat := 657137137204563127689451

theorem tailTrace_1279770 : CollatzResearch.WordTrace tailWord_1279770 prefixEnd_1279770 657137137204563127689451 := by
  unfold tailWord_1279770
  simp only [CollatzResearch.WordTrace]
  refine ⟨11669261643404833040019191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31118031049079554773384509 11669261643404833040019191)
  ·
    refine ⟨17503892465107249560028787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11669261643404833040019191 17503892465107249560028787)
    ·
      refine ⟨26255838697660874340043181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17503892465107249560028787 26255838697660874340043181)
      ·
        refine ⟨9845939511622827877516193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26255838697660874340043181 9845939511622827877516193)
        ·
          refine ⟨7384454633717120908137145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9845939511622827877516193 7384454633717120908137145)
          ·
            refine ⟨5538340975287840681102859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7384454633717120908137145 5538340975287840681102859)
            ·
              refine ⟨8307511462931761021654289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5538340975287840681102859 8307511462931761021654289)
              ·
                refine ⟨6230633597198820766240717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8307511462931761021654289 6230633597198820766240717)
                ·
                  refine ⟨2336487598949557787340269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6230633597198820766240717 2336487598949557787340269)
                  ·
                    refine ⟨876182849606084170252601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2336487598949557787340269 876182849606084170252601)
                    ·
                      refine ⟨657137137204563127689451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 876182849606084170252601 657137137204563127689451)
                      ·
                        rfl

theorem cell23_1279770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 2, 3, 3, 2].length) (baseStart_1279770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1279770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1279770 prefixEnd_1279770 := by exact prefixLift 1279770
  have htrace : WordTrace (prefixWord ++ tailWord_1279770) baseStart_1279770 baseEnd_1279770 := by
    simpa [prefixWord, tailWord_1279770, baseEnd_1279770] using wordTrace_append hprefix tailTrace_1279770
  have hstable : (prefixWord ++ tailWord_1279770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279770).length < 2 ^ (prefixWord ++ tailWord_1279770).sum := by decide
  have hdescent : baseEnd_1279770 < baseStart_1279770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279774 : List Nat := [4, 3, 2, 2, 1, 1, 2, 1, 1, 2, 4]
def baseStart_1279774 : Nat := 118140960795 + 1279774 * 2 ^ 59
def prefixEnd_1279774 : Nat := 4983230072969 + 3 ^ 40 * 1279774 * 2
def baseEnd_1279774 : Nat := 657139191127181112039433

theorem tailTrace_1279774 : CollatzResearch.WordTrace tailWord_1279774 prefixEnd_1279774 657139191127181112039433 := by
  unfold tailWord_1279774
  simp only [CollatzResearch.WordTrace]
  refine ⟨5834649058200605105402797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31118128310403227228814917 5834649058200605105402797)
  ·
    refine ⟨2187993396825226914526049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5834649058200605105402797 2187993396825226914526049)
    ·
      refine ⟨1640995047618920185894537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2187993396825226914526049 1640995047618920185894537)
      ·
        refine ⟨1230746285714190139420903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1640995047618920185894537 1230746285714190139420903)
        ·
          refine ⟨1846119428571285209131355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1230746285714190139420903 1846119428571285209131355)
          ·
            refine ⟨2769179142856927813697033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1846119428571285209131355 2769179142856927813697033)
            ·
              refine ⟨2076884357142695860272775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2769179142856927813697033 2076884357142695860272775)
              ·
                refine ⟨3115326535714043790409163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2076884357142695860272775 3115326535714043790409163)
                ·
                  refine ⟨4672989803571065685613745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3115326535714043790409163 4672989803571065685613745)
                  ·
                    refine ⟨3504742352678299264210309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4672989803571065685613745 3504742352678299264210309)
                    ·
                      refine ⟨657139191127181112039433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3504742352678299264210309 657139191127181112039433)
                      ·
                        rfl

theorem cell23_1279774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_1279774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1279774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1279774 prefixEnd_1279774 := by exact prefixLift 1279774
  have htrace : WordTrace (prefixWord ++ tailWord_1279774) baseStart_1279774 baseEnd_1279774 := by
    simpa [prefixWord, tailWord_1279774, baseEnd_1279774] using wordTrace_append hprefix tailTrace_1279774
  have hstable : (prefixWord ++ tailWord_1279774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279774).length < 2 ^ (prefixWord ++ tailWord_1279774).sum := by decide
  have hdescent : baseEnd_1279774 < baseStart_1279774 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279800 : List Nat := [2, 1, 2, 1, 3, 3, 2, 2, 1, 4, 2]
def baseStart_1279800 : Nat := 118140960795 + 1279800 * 2 ^ 59
def prefixEnd_1279800 : Nat := 4983230072969 + 3 ^ 40 * 1279800 * 2
def baseEnd_1279800 : Nat := 657152541624198010314313

theorem tailTrace_1279800 : CollatzResearch.WordTrace tailWord_1279800 prefixEnd_1279800 657152541624198010314313 := by
  unfold tailWord_1279800
  simp only [CollatzResearch.WordTrace]
  refine ⟨23339070381755323641834427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31118760509007098189112569 23339070381755323641834427)
  ·
    refine ⟨35008605572632985462751641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23339070381755323641834427 35008605572632985462751641)
    ·
      refine ⟨26256454179474739097063731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35008605572632985462751641 26256454179474739097063731)
      ·
        refine ⟨39384681269212108645595597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26256454179474739097063731 39384681269212108645595597)
        ·
          refine ⟨14769255475954540742098349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39384681269212108645595597 14769255475954540742098349)
          ·
            refine ⟨5538470803482952778286881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14769255475954540742098349 5538470803482952778286881)
            ·
              refine ⟨4153853102612214583715161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5538470803482952778286881 4153853102612214583715161)
              ·
                refine ⟨3115389826959160937786371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4153853102612214583715161 3115389826959160937786371)
                ·
                  refine ⟨4673084740438741406679557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3115389826959160937786371 4673084740438741406679557)
                  ·
                    refine ⟨876203388832264013752417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4673084740438741406679557 876203388832264013752417)
                    ·
                      refine ⟨657152541624198010314313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 876203388832264013752417 657152541624198010314313)
                      ·
                        rfl

theorem cell23_1279800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 2, 1, 4, 2].length) (baseStart_1279800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1279800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1279800 prefixEnd_1279800 := by exact prefixLift 1279800
  have htrace : WordTrace (prefixWord ++ tailWord_1279800) baseStart_1279800 baseEnd_1279800 := by
    simpa [prefixWord, tailWord_1279800, baseEnd_1279800] using wordTrace_append hprefix tailTrace_1279800
  have hstable : (prefixWord ++ tailWord_1279800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279800).length < 2 ^ (prefixWord ++ tailWord_1279800).sum := by decide
  have hdescent : baseEnd_1279800 < baseStart_1279800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279833 : List Nat := [1, 2, 1, 2, 2, 3, 1, 3, 2, 3, 3]
def baseStart_1279833 : Nat := 118140960795 + 1279833 * 2 ^ 59
def prefixEnd_1279833 : Nat := 4983230072969 + 3 ^ 40 * 1279833 * 2
def baseEnd_1279833 : Nat := 657169486485796381201661

theorem tailTrace_1279833 : CollatzResearch.WordTrace tailWord_1279833 prefixEnd_1279833 657169486485796381201661 := by
  unfold tailWord_1279833
  simp only [CollatzResearch.WordTrace]
  refine ⟨46679344372391093919620153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31119562914927395946413435 46679344372391093919620153)
  ·
    refine ⟨35009508279293320439715115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46679344372391093919620153 35009508279293320439715115)
    ·
      refine ⟨52514262418939980659572673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35009508279293320439715115 52514262418939980659572673)
      ·
        refine ⟨39385696814204985494679505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52514262418939980659572673 39385696814204985494679505)
        ·
          refine ⟨29539272610653739121009629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39385696814204985494679505 29539272610653739121009629)
          ·
            refine ⟨11077227228995152170378611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29539272610653739121009629 11077227228995152170378611)
            ·
              refine ⟨16615840843492728255567917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11077227228995152170378611 16615840843492728255567917)
              ·
                refine ⟨6230940316309773095837969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16615840843492728255567917 6230940316309773095837969)
                ·
                  refine ⟨4673205237232329821878477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6230940316309773095837969 4673205237232329821878477)
                  ·
                    refine ⟨1752451963962123683204429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4673205237232329821878477 1752451963962123683204429)
                    ·
                      refine ⟨657169486485796381201661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1752451963962123683204429 657169486485796381201661)
                      ·
                        rfl

theorem cell23_1279833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 3, 2, 3, 3].length) (baseStart_1279833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1279833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1279833 prefixEnd_1279833 := by exact prefixLift 1279833
  have htrace : WordTrace (prefixWord ++ tailWord_1279833) baseStart_1279833 baseEnd_1279833 := by
    simpa [prefixWord, tailWord_1279833, baseEnd_1279833] using wordTrace_append hprefix tailTrace_1279833
  have hstable : (prefixWord ++ tailWord_1279833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279833).length < 2 ^ (prefixWord ++ tailWord_1279833).sum := by decide
  have hdescent : baseEnd_1279833 < baseStart_1279833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279834 : List Nat := [3, 1, 1, 2, 1, 3, 5, 1, 2, 2, 2]
def baseStart_1279834 : Nat := 118140960795 + 1279834 * 2 ^ 59
def prefixEnd_1279834 : Nat := 4983230072969 + 3 ^ 40 * 1279834 * 2
def baseEnd_1279834 : Nat := 657169999966450877289157

theorem tailTrace_1279834 : CollatzResearch.WordTrace tailWord_1279834 prefixEnd_1279834 657169999966450877289157 := by
  unfold tailWord_1279834
  simp only [CollatzResearch.WordTrace]
  refine ⟨11669845211346867772601639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31119587230258314060271037 11669845211346867772601639)
  ·
    refine ⟨17504767817020301658902459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11669845211346867772601639 17504767817020301658902459)
    ·
      refine ⟨26257151725530452488353689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17504767817020301658902459 26257151725530452488353689)
      ·
        refine ⟨19692863794147839366265267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26257151725530452488353689 19692863794147839366265267)
        ·
          refine ⟨29539295691221759049397901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19692863794147839366265267 29539295691221759049397901)
          ·
            refine ⟨11077235884208159643524213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29539295691221759049397901 11077235884208159643524213)
            ·
              refine ⟨1038490864144514966580395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11077235884208159643524213 1038490864144514966580395)
              ·
                refine ⟨1557736296216772449870593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1038490864144514966580395 1557736296216772449870593)
                ·
                  refine ⟨1168302222162579337402945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1557736296216772449870593 1168302222162579337402945)
                  ·
                    refine ⟨876226666621934503052209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1168302222162579337402945 876226666621934503052209)
                    ·
                      refine ⟨657169999966450877289157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 876226666621934503052209 657169999966450877289157)
                      ·
                        rfl

theorem cell23_1279834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 5, 1, 2, 2, 2].length) (baseStart_1279834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1279834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1279834 prefixEnd_1279834 := by exact prefixLift 1279834
  have htrace : WordTrace (prefixWord ++ tailWord_1279834) baseStart_1279834 baseEnd_1279834 := by
    simpa [prefixWord, tailWord_1279834, baseEnd_1279834] using wordTrace_append hprefix tailTrace_1279834
  have hstable : (prefixWord ++ tailWord_1279834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279834).length < 2 ^ (prefixWord ++ tailWord_1279834).sum := by decide
  have hdescent : baseEnd_1279834 < baseStart_1279834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279853 : List Nat := [1, 5, 1, 1, 1, 1, 4, 1, 1, 7]
def baseStart_1279853 : Nat := 118140960795 + 1279853 * 2 ^ 59
def prefixEnd_1279853 : Nat := 4983230072969 + 3 ^ 40 * 1279853 * 2
def baseEnd_1279853 : Nat := 219059918699628767650523

theorem tailTrace_1279853 : CollatzResearch.WordTrace tailWord_1279853 prefixEnd_1279853 219059918699628767650523 := by
  unfold tailWord_1279853
  simp only [CollatzResearch.WordTrace]
  refine ⟨46680073832318637335348213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31120049221545758223565475 46680073832318637335348213)
  ·
    refine ⟨4376256921779872250188895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46680073832318637335348213 4376256921779872250188895)
    ·
      refine ⟨6564385382669808375283343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4376256921779872250188895 6564385382669808375283343)
      ·
        refine ⟨9846578074004712562925015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6564385382669808375283343 9846578074004712562925015)
        ·
          refine ⟨14769867111007068844387523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9846578074004712562925015 14769867111007068844387523)
          ·
            refine ⟨22154800666510603266581285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14769867111007068844387523 22154800666510603266581285)
            ·
              refine ⟨4154025124970738112483991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22154800666510603266581285 4154025124970738112483991)
              ·
                refine ⟨6231037687456107168725987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4154025124970738112483991 6231037687456107168725987)
                ·
                  refine ⟨9346556531184160753088981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6231037687456107168725987 9346556531184160753088981)
                  ·
                    refine ⟨219059918699628767650523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9346556531184160753088981 219059918699628767650523)
                    ·
                      rfl

theorem cell23_1279853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 1, 1, 7].length) (baseStart_1279853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1279853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1279853 prefixEnd_1279853 := by exact prefixLift 1279853
  have htrace : WordTrace (prefixWord ++ tailWord_1279853) baseStart_1279853 baseEnd_1279853 := by
    simpa [prefixWord, tailWord_1279853, baseEnd_1279853] using wordTrace_append hprefix tailTrace_1279853
  have hstable : (prefixWord ++ tailWord_1279853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279853).length < 2 ^ (prefixWord ++ tailWord_1279853).sum := by decide
  have hdescent : baseEnd_1279853 < baseStart_1279853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279880 : List Nat := [2, 1, 3, 3, 3, 1, 1, 1, 1, 2, 5]
def baseStart_1279880 : Nat := 118140960795 + 1279880 * 2 ^ 59
def prefixEnd_1279880 : Nat := 4983230072969 + 3 ^ 40 * 1279880 * 2
def baseEnd_1279880 : Nat := 657193620076557697313945

theorem tailTrace_1279880 : CollatzResearch.WordTrace tailWord_1279880 prefixEnd_1279880 657193620076557697313945 := by
  unfold tailWord_1279880
  simp only [CollatzResearch.WordTrace]
  refine ⟨23340529301610410473290547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31120705735480547297720729 23340529301610410473290547)
  ·
    refine ⟨35010793952415615709935821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23340529301610410473290547 35010793952415615709935821)
    ·
      refine ⟨13129047732155855891225933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35010793952415615709935821 13129047732155855891225933)
      ·
        refine ⟨4923392899558445959209725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13129047732155855891225933 4923392899558445959209725)
        ·
          refine ⟨1846272337334417234703647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4923392899558445959209725 1846272337334417234703647)
          ·
            refine ⟨2769408506001625852055471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1846272337334417234703647 2769408506001625852055471)
            ·
              refine ⟨4154112759002438778083207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2769408506001625852055471 4154112759002438778083207)
              ·
                refine ⟨6231169138503658167124811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4154112759002438778083207 6231169138503658167124811)
                ·
                  refine ⟨9346753707755487250687217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6231169138503658167124811 9346753707755487250687217)
                  ·
                    refine ⟨7010065280816615438015413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9346753707755487250687217 7010065280816615438015413)
                    ·
                      refine ⟨657193620076557697313945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7010065280816615438015413 657193620076557697313945)
                      ·
                        rfl

theorem cell23_1279880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_1279880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1279880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1279880 prefixEnd_1279880 := by exact prefixLift 1279880
  have htrace : WordTrace (prefixWord ++ tailWord_1279880) baseStart_1279880 baseEnd_1279880 := by
    simpa [prefixWord, tailWord_1279880, baseEnd_1279880] using wordTrace_append hprefix tailTrace_1279880
  have hstable : (prefixWord ++ tailWord_1279880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279880).length < 2 ^ (prefixWord ++ tailWord_1279880).sum := by decide
  have hdescent : baseEnd_1279880 < baseStart_1279880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279934 : List Nat := [4, 2, 1, 1, 1, 4, 1, 4, 1, 4]
def baseStart_1279934 : Nat := 118140960795 + 1279934 * 2 ^ 59
def prefixEnd_1279934 : Nat := 4983230072969 + 3 ^ 40 * 1279934 * 2
def baseEnd_1279934 : Nat := 219073782677300162012899

theorem tailTrace_1279934 : CollatzResearch.WordTrace tailWord_1279934 prefixEnd_1279934 219073782677300162012899 := by
  unfold tailWord_1279934
  simp only [CollatzResearch.WordTrace]
  refine ⟨5835378518128148521130857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31122018763350125446031237 5835378518128148521130857)
  ·
    refine ⟨4376533888596111390848143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5835378518128148521130857 4376533888596111390848143)
    ·
      refine ⟨6564800832894167086272215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4376533888596111390848143 6564800832894167086272215)
      ·
        refine ⟨9847201249341250629408323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6564800832894167086272215 9847201249341250629408323)
        ·
          refine ⟨14770801874011875944112485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9847201249341250629408323 14770801874011875944112485)
          ·
            refine ⟨2769525351377226739521091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14770801874011875944112485 2769525351377226739521091)
            ·
              refine ⟨4154288027065840109281637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2769525351377226739521091 4154288027065840109281637)
              ·
                refine ⟨778929005074845020490307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4154288027065840109281637 778929005074845020490307)
                ·
                  refine ⟨1168393507612267530735461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 778929005074845020490307 1168393507612267530735461)
                  ·
                    refine ⟨219073782677300162012899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1168393507612267530735461 219073782677300162012899)
                    ·
                      rfl

theorem cell23_1279934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 4, 1, 4].length) (baseStart_1279934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1279934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1279934 prefixEnd_1279934 := by exact prefixLift 1279934
  have htrace : WordTrace (prefixWord ++ tailWord_1279934) baseStart_1279934 baseEnd_1279934 := by
    simpa [prefixWord, tailWord_1279934, baseEnd_1279934] using wordTrace_append hprefix tailTrace_1279934
  have hstable : (prefixWord ++ tailWord_1279934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279934).length < 2 ^ (prefixWord ++ tailWord_1279934).sum := by decide
  have hdescent : baseEnd_1279934 < baseStart_1279934 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279957 : List Nat := [1, 3, 2, 3, 2, 1, 1, 1, 5, 1, 3]
def baseStart_1279957 : Nat := 118140960795 + 1279957 * 2 ^ 59
def prefixEnd_1279957 : Nat := 4983230072969 + 3 ^ 40 * 1279957 * 2
def baseEnd_1279957 : Nat := 657233158086953896051091

theorem tailTrace_1279957 : CollatzResearch.WordTrace tailWord_1279957 prefixEnd_1279957 657233158086953896051091 := by
  unfold tailWord_1279957
  simp only [CollatzResearch.WordTrace]
  refine ⟨46683867023941863097134125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31122578015961242064756083 46683867023941863097134125)
  ·
    refine ⟨17506450133978198661425297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46683867023941863097134125 17506450133978198661425297)
    ·
      refine ⟨13129837600483648996068973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17506450133978198661425297 13129837600483648996068973)
      ·
        refine ⟨4923689100181368373525865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13129837600483648996068973 4923689100181368373525865)
        ·
          refine ⟨3692766825136026280144399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4923689100181368373525865 3692766825136026280144399)
          ·
            refine ⟨5539150237704039420216599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3692766825136026280144399 5539150237704039420216599)
            ·
              refine ⟨8308725356556059130324899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5539150237704039420216599 8308725356556059130324899)
              ·
                refine ⟨12463088034834088695487349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8308725356556059130324899 12463088034834088695487349)
                ·
                  refine ⟨1168414503265695815201939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12463088034834088695487349 1168414503265695815201939)
                  ·
                    refine ⟨1752621754898543722802909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1168414503265695815201939 1752621754898543722802909)
                    ·
                      refine ⟨657233158086953896051091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1752621754898543722802909 657233158086953896051091)
                      ·
                        rfl

theorem cell23_1279957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 5, 1, 3].length) (baseStart_1279957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1279957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1279957 prefixEnd_1279957 := by exact prefixLift 1279957
  have htrace : WordTrace (prefixWord ++ tailWord_1279957) baseStart_1279957 baseEnd_1279957 := by
    simpa [prefixWord, tailWord_1279957, baseEnd_1279957] using wordTrace_append hprefix tailTrace_1279957
  have hstable : (prefixWord ++ tailWord_1279957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279957).length < 2 ^ (prefixWord ++ tailWord_1279957).sum := by decide
  have hdescent : baseEnd_1279957 < baseStart_1279957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279960 : List Nat := [2, 1, 2, 2, 2, 2, 2, 4, 1, 5]
def baseStart_1279960 : Nat := 118140960795 + 1279960 * 2 ^ 59
def prefixEnd_1279960 : Nat := 4983230072969 + 3 ^ 40 * 1279960 * 2
def baseEnd_1279960 : Nat := 219078232842972461437859

theorem tailTrace_1279960 : CollatzResearch.WordTrace tailWord_1279960 prefixEnd_1279960 219078232842972461437859 := by
  unfold tailWord_1279960
  simp only [CollatzResearch.WordTrace]
  refine ⟨23341988221465497304746667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31122650961953996406328889 23341988221465497304746667)
  ·
    refine ⟨35012982332198245957120001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23341988221465497304746667 35012982332198245957120001)
    ·
      refine ⟨26259736749148684467840001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35012982332198245957120001 26259736749148684467840001)
      ·
        refine ⟨19694802561861513350880001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26259736749148684467840001 19694802561861513350880001)
        ·
          refine ⟨14771101921396135013160001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19694802561861513350880001 14771101921396135013160001)
          ·
            refine ⟨11078326441047101259870001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14771101921396135013160001 11078326441047101259870001)
            ·
              refine ⟨8308744830785325944902501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11078326441047101259870001 8308744830785325944902501)
              ·
                refine ⟨1557889655772248614669219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8308744830785325944902501 1557889655772248614669219)
                ·
                  refine ⟨2336834483658372922003829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1557889655772248614669219 2336834483658372922003829)
                  ·
                    refine ⟨219078232842972461437859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2336834483658372922003829 219078232842972461437859)
                    ·
                      rfl

theorem cell23_1279960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 4, 1, 5].length) (baseStart_1279960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1279960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1279960 prefixEnd_1279960 := by exact prefixLift 1279960
  have htrace : WordTrace (prefixWord ++ tailWord_1279960) baseStart_1279960 baseEnd_1279960 := by
    simpa [prefixWord, tailWord_1279960, baseEnd_1279960] using wordTrace_append hprefix tailTrace_1279960
  have hstable : (prefixWord ++ tailWord_1279960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279960).length < 2 ^ (prefixWord ++ tailWord_1279960).sum := by decide
  have hdescent : baseEnd_1279960 < baseStart_1279960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279967 : List Nat := [1, 1, 2, 3, 4, 2, 1, 1, 1, 5, 2]
def baseStart_1279967 : Nat := 118140960795 + 1279967 * 2 ^ 59
def prefixEnd_1279967 : Nat := 4983230072969 + 3 ^ 40 * 1279967 * 2
def baseEnd_1279967 : Nat := 657238292893498856926045

theorem tailTrace_1279967 : CollatzResearch.WordTrace tailWord_1279967 prefixEnd_1279967 657238292893498856926045 := by
  unfold tailWord_1279967
  simp only [CollatzResearch.WordTrace]
  refine ⟨46684231753905634804998155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31122821169270423203332103 46684231753905634804998155)
  ·
    refine ⟨70026347630858452207497233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46684231753905634804998155 70026347630858452207497233)
    ·
      refine ⟨52519760723143839155622925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70026347630858452207497233 52519760723143839155622925)
      ·
        refine ⟨19694910271178939683358597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52519760723143839155622925 19694910271178939683358597)
        ·
          refine ⟨3692795675846051190629737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19694910271178939683358597 3692795675846051190629737)
          ·
            refine ⟨2769596756884538392972303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3692795675846051190629737 2769596756884538392972303)
            ·
              refine ⟨4154395135326807589458455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2769596756884538392972303 4154395135326807589458455)
              ·
                refine ⟨6231592702990211384187683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4154395135326807589458455 6231592702990211384187683)
                ·
                  refine ⟨9347389054485317076281525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6231592702990211384187683 9347389054485317076281525)
                  ·
                    refine ⟨876317723857998475901393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9347389054485317076281525 876317723857998475901393)
                    ·
                      refine ⟨657238292893498856926045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 876317723857998475901393 657238292893498856926045)
                      ·
                        rfl

theorem cell23_1279967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 1, 1, 5, 2].length) (baseStart_1279967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1279967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1279967 prefixEnd_1279967 := by exact prefixLift 1279967
  have htrace : WordTrace (prefixWord ++ tailWord_1279967) baseStart_1279967 baseEnd_1279967 := by
    simpa [prefixWord, tailWord_1279967, baseEnd_1279967] using wordTrace_append hprefix tailTrace_1279967
  have hstable : (prefixWord ++ tailWord_1279967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279967).length < 2 ^ (prefixWord ++ tailWord_1279967).sum := by decide
  have hdescent : baseEnd_1279967 < baseStart_1279967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279980 : List Nat := [2, 2, 1, 1, 2, 1, 1, 2, 1, 8, 2]
def baseStart_1279980 : Nat := 118140960795 + 1279980 * 2 ^ 59
def prefixEnd_1279980 : Nat := 4983230072969 + 3 ^ 40 * 1279980 * 2
def baseEnd_1279980 : Nat := 657244968142007306063485

theorem tailTrace_1279980 : CollatzResearch.WordTrace tailWord_1279980 prefixEnd_1279980 657244968142007306063485 := by
  unfold tailWord_1279980
  simp only [CollatzResearch.WordTrace]
  refine ⟨23342352951429269012610697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31123137268572358683480929 23342352951429269012610697)
  ·
    refine ⟨17506764713571951759458023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23342352951429269012610697 17506764713571951759458023)
    ·
      refine ⟨26260147070357927639187035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17506764713571951759458023 26260147070357927639187035)
      ·
        refine ⟨39390220605536891458780553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26260147070357927639187035 39390220605536891458780553)
        ·
          refine ⟨29542665454152668594085415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39390220605536891458780553 29542665454152668594085415)
          ·
            refine ⟨44313998181229002891128123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29542665454152668594085415 44313998181229002891128123)
            ·
              refine ⟨66470997271843504336692185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44313998181229002891128123 66470997271843504336692185)
              ·
                refine ⟨49853247953882628252519139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66470997271843504336692185 49853247953882628252519139)
                ·
                  refine ⟨74779871930823942378778709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49853247953882628252519139 74779871930823942378778709)
                  ·
                    refine ⟨876326624189343074751313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 74779871930823942378778709 876326624189343074751313)
                    ·
                      refine ⟨657244968142007306063485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 876326624189343074751313 657244968142007306063485)
                      ·
                        rfl

theorem cell23_1279980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 8, 2].length) (baseStart_1279980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1279980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1279980 prefixEnd_1279980 := by exact prefixLift 1279980
  have htrace : WordTrace (prefixWord ++ tailWord_1279980) baseStart_1279980 baseEnd_1279980 := by
    simpa [prefixWord, tailWord_1279980, baseEnd_1279980] using wordTrace_append hprefix tailTrace_1279980
  have hstable : (prefixWord ++ tailWord_1279980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279980).length < 2 ^ (prefixWord ++ tailWord_1279980).sum := by decide
  have hdescent : baseEnd_1279980 < baseStart_1279980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279981 : List Nat := [1, 5, 1, 4, 2, 1, 1, 2, 6]
def baseStart_1279981 : Nat := 118140960795 + 1279981 * 2 ^ 59
def prefixEnd_1279981 : Nat := 4983230072969 + 3 ^ 40 * 1279981 * 2
def baseEnd_1279981 : Nat := 73027275735851311350109

theorem tailTrace_1279981 : CollatzResearch.WordTrace tailWord_1279981 prefixEnd_1279981 73027275735851311350109 := by
  unfold tailWord_1279981
  simp only [CollatzResearch.WordTrace]
  refine ⟨46684742375854915196007797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31123161583903276797338531 46684742375854915196007797)
  ·
    refine ⟨4376694597736398299625731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46684742375854915196007797 4376694597736398299625731)
    ·
      refine ⟨6565041896604597449438597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4376694597736398299625731 6565041896604597449438597)
      ·
        refine ⟨1230945355613362021769737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6565041896604597449438597 1230945355613362021769737)
        ·
          refine ⟨923209016710021516327303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1230945355613362021769737 923209016710021516327303)
          ·
            refine ⟨1384813525065032274490955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 923209016710021516327303 1384813525065032274490955)
            ·
              refine ⟨2077220287597548411736433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1384813525065032274490955 2077220287597548411736433)
              ·
                refine ⟨1557915215698161308802325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2077220287597548411736433 1557915215698161308802325)
                ·
                  refine ⟨73027275735851311350109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1557915215698161308802325 73027275735851311350109)
                  ·
                    rfl

theorem cell23_1279981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 2, 6].length) (baseStart_1279981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1279981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1279981 prefixEnd_1279981 := by exact prefixLift 1279981
  have htrace : WordTrace (prefixWord ++ tailWord_1279981) baseStart_1279981 baseEnd_1279981 := by
    simpa [prefixWord, tailWord_1279981, baseEnd_1279981] using wordTrace_append hprefix tailTrace_1279981
  have hstable : (prefixWord ++ tailWord_1279981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279981).length < 2 ^ (prefixWord ++ tailWord_1279981).sum := by decide
  have hdescent : baseEnd_1279981 < baseStart_1279981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280000 : List Nat := [2, 1, 1, 2, 1, 1, 1, 6, 3, 2, 3]
def baseStart_1280000 : Nat := 118140960795 + 1280000 * 2 ^ 59
def prefixEnd_1280000 : Nat := 4983230072969 + 3 ^ 40 * 1280000 * 2
def baseEnd_1280000 : Nat := 657255237755097227813393

theorem tailTrace_1280000 : CollatzResearch.WordTrace tailWord_1280000 prefixEnd_1280000 657255237755097227813393 := by
  unfold tailWord_1280000
  simp only [CollatzResearch.WordTrace]
  refine ⟨23342717681393040720474727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31123623575190720960632969 23342717681393040720474727)
  ·
    refine ⟨35014076522089561080712091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23342717681393040720474727 35014076522089561080712091)
    ·
      refine ⟨52521114783134341621068137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35014076522089561080712091 52521114783134341621068137)
      ·
        refine ⟨39390836087350756215801103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52521114783134341621068137 39390836087350756215801103)
        ·
          refine ⟨59086254131026134323701655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39390836087350756215801103 59086254131026134323701655)
          ·
            refine ⟨88629381196539201485552483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59086254131026134323701655 88629381196539201485552483)
            ·
              refine ⟨132944071794808802228328725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88629381196539201485552483 132944071794808802228328725)
              ·
                refine ⟨6231753365381662604452909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 132944071794808802228328725 6231753365381662604452909)
                ·
                  refine ⟨2336907512018123476669841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6231753365381662604452909 2336907512018123476669841)
                  ·
                    refine ⟨1752680634013592607502381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2336907512018123476669841 1752680634013592607502381)
                    ·
                      refine ⟨657255237755097227813393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1752680634013592607502381 657255237755097227813393)
                      ·
                        rfl

theorem cell23_1280000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 6, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 6, 3, 2, 3].length) (baseStart_1280000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1280000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1280000 prefixEnd_1280000 := by exact prefixLift 1280000
  have htrace : WordTrace (prefixWord ++ tailWord_1280000) baseStart_1280000 baseEnd_1280000 := by
    simpa [prefixWord, tailWord_1280000, baseEnd_1280000] using wordTrace_append hprefix tailTrace_1280000
  have hstable : (prefixWord ++ tailWord_1280000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280000).length < 2 ^ (prefixWord ++ tailWord_1280000).sum := by decide
  have hdescent : baseEnd_1280000 < baseStart_1280000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280007 : List Nat := [1, 1, 4, 3, 1, 4, 1, 1, 1, 6]
def baseStart_1280007 : Nat := 118140960795 + 1280007 * 2 ^ 59
def prefixEnd_1280007 : Nat := 4983230072969 + 3 ^ 40 * 1280007 * 2
def baseEnd_1280007 : Nat := 219086277373226233475287

theorem tailTrace_1280007 : CollatzResearch.WordTrace tailWord_1280007 prefixEnd_1280007 219086277373226233475287 := by
  unfold tailWord_1280007
  simp only [CollatzResearch.WordTrace]
  refine ⟨46685690673760721636454275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31123793782507147757636183 46685690673760721636454275)
  ·
    refine ⟨70028536010641082454681413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46685690673760721636454275 70028536010641082454681413)
    ·
      refine ⟨13130350501995202960252765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70028536010641082454681413 13130350501995202960252765)
      ·
        refine ⟨4923881438248201110094787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13130350501995202960252765 4923881438248201110094787)
        ·
          refine ⟨7385822157372301665142181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4923881438248201110094787 7385822157372301665142181)
          ·
            refine ⟨1384841654507306562214159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7385822157372301665142181 1384841654507306562214159)
            ·
              refine ⟨2077262481760959843321239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1384841654507306562214159 2077262481760959843321239)
              ·
                refine ⟨3115893722641439764981859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2077262481760959843321239 3115893722641439764981859)
                ·
                  refine ⟨4673840583962159647472789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3115893722641439764981859 4673840583962159647472789)
                  ·
                    refine ⟨219086277373226233475287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4673840583962159647472789 219086277373226233475287)
                    ·
                      rfl

theorem cell23_1280007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 1, 1, 6].length) (baseStart_1280007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1280007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1280007 prefixEnd_1280007 := by exact prefixLift 1280007
  have htrace : WordTrace (prefixWord ++ tailWord_1280007) baseStart_1280007 baseEnd_1280007 := by
    simpa [prefixWord, tailWord_1280007, baseEnd_1280007] using wordTrace_append hprefix tailTrace_1280007
  have hstable : (prefixWord ++ tailWord_1280007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280007).length < 2 ^ (prefixWord ++ tailWord_1280007).sum := by decide
  have hdescent : baseEnd_1280007 < baseStart_1280007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280014 : List Nat := [4, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2]
def baseStart_1280014 : Nat := 118140960795 + 1280014 * 2 ^ 59
def prefixEnd_1280014 : Nat := 4983230072969 + 3 ^ 40 * 1280014 * 2
def baseEnd_1280014 : Nat := 657262426484260173038329

theorem tailTrace_1280014 : CollatzResearch.WordTrace tailWord_1280014 prefixEnd_1280014 657262426484260173038329 := by
  unfold tailWord_1280014
  simp only [CollatzResearch.WordTrace]
  refine ⟨5835743248091920228994887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31123963989823574554639397 5835743248091920228994887)
  ·
    refine ⟨8753614872137880343492331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5835743248091920228994887 8753614872137880343492331)
    ·
      refine ⟨13130422308206820515238497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8753614872137880343492331 13130422308206820515238497)
      ·
        refine ⟨9847816731155115386428873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13130422308206820515238497 9847816731155115386428873)
        ·
          refine ⟨7385862548366336539821655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9847816731155115386428873 7385862548366336539821655)
          ·
            refine ⟨11078793822549504809732483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7385862548366336539821655 11078793822549504809732483)
            ·
              refine ⟨16618190733824257214598725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11078793822549504809732483 16618190733824257214598725)
              ·
                refine ⟨3115910762592048227737261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16618190733824257214598725 3115910762592048227737261)
                ·
                  refine ⟨1168466535972018085401473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3115910762592048227737261 1168466535972018085401473)
                  ·
                    refine ⟨876349901979013564051105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1168466535972018085401473 876349901979013564051105)
                    ·
                      refine ⟨657262426484260173038329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 876349901979013564051105 657262426484260173038329)
                      ·
                        rfl

theorem cell23_1280014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2].length) (baseStart_1280014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1280014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1280014 prefixEnd_1280014 := by exact prefixLift 1280014
  have htrace : WordTrace (prefixWord ++ tailWord_1280014) baseStart_1280014 baseEnd_1280014 := by
    simpa [prefixWord, tailWord_1280014, baseEnd_1280014] using wordTrace_append hprefix tailTrace_1280014
  have hstable : (prefixWord ++ tailWord_1280014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280014).length < 2 ^ (prefixWord ++ tailWord_1280014).sum := by decide
  have hdescent : baseEnd_1280014 < baseStart_1280014 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280048 : List Nat := [2, 1, 1, 1, 2, 6, 3, 2, 1, 2, 2]
def baseStart_1280048 : Nat := 118140960795 + 1280048 * 2 ^ 59
def prefixEnd_1280048 : Nat := 4983230072969 + 3 ^ 40 * 1280048 * 2
def baseEnd_1280048 : Nat := 657279884826513040013173

theorem tailTrace_1280048 : CollatzResearch.WordTrace tailWord_1280048 prefixEnd_1280048 657279884826513040013173 := by
  unfold tailWord_1280048
  simp only [CollatzResearch.WordTrace]
  refine ⟨23343593033306092819348399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31124790711074790425797865 23343593033306092819348399)
  ·
    refine ⟨35015389549959139229022599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23343593033306092819348399 35015389549959139229022599)
    ·
      refine ⟨52523084324938708843533899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35015389549959139229022599 52523084324938708843533899)
      ·
        refine ⟨78784626487408063265300849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52523084324938708843533899 78784626487408063265300849)
        ·
          refine ⟨59088469865556047448975637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78784626487408063265300849 59088469865556047448975637)
          ·
            refine ⟨2769772024947939724170733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 59088469865556047448975637 2769772024947939724170733)
            ·
              refine ⟨1038664509355477396564025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2769772024947939724170733 1038664509355477396564025)
              ·
                refine ⟨778998382016608047423019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1038664509355477396564025 778998382016608047423019)
                ·
                  refine ⟨1168497573024912071134529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 778998382016608047423019 1168497573024912071134529)
                  ·
                    refine ⟨876373179768684053350897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1168497573024912071134529 876373179768684053350897)
                    ·
                      refine ⟨657279884826513040013173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 876373179768684053350897 657279884826513040013173)
                      ·
                        rfl

theorem cell23_1280048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 3, 2, 1, 2, 2].length) (baseStart_1280048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1280048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1280048 prefixEnd_1280048 := by exact prefixLift 1280048
  have htrace : WordTrace (prefixWord ++ tailWord_1280048) baseStart_1280048 baseEnd_1280048 := by
    simpa [prefixWord, tailWord_1280048, baseEnd_1280048] using wordTrace_append hprefix tailTrace_1280048
  have hstable : (prefixWord ++ tailWord_1280048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280048).length < 2 ^ (prefixWord ++ tailWord_1280048).sum := by decide
  have hdescent : baseEnd_1280048 < baseStart_1280048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280064 : List Nat := [2, 1, 1, 2, 2, 5, 1, 3, 2, 1, 3]
def baseStart_1280064 : Nat := 118140960795 + 1280064 * 2 ^ 59
def prefixEnd_1280064 : Nat := 4983230072969 + 3 ^ 40 * 1280064 * 2
def baseEnd_1280064 : Nat := 657288100516984977413099

theorem tailTrace_1280064 : CollatzResearch.WordTrace tailWord_1280064 prefixEnd_1280064 657288100516984977413099 := by
  unfold tailWord_1280064
  simp only [CollatzResearch.WordTrace]
  refine ⟨23343884817277110185639623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31125179756369480247519497 23343884817277110185639623)
  ·
    refine ⟨35015827225915665278459435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23343884817277110185639623 35015827225915665278459435)
    ·
      refine ⟨52523740838873497917689153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35015827225915665278459435 52523740838873497917689153)
      ·
        refine ⟨39392805629155123438266865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52523740838873497917689153 39392805629155123438266865)
        ·
          refine ⟨29544604221866342578700149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39392805629155123438266865 29544604221866342578700149)
          ·
            refine ⟨2769806645799969616753139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29544604221866342578700149 2769806645799969616753139)
            ·
              refine ⟨4154709968699954425129709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2769806645799969616753139 4154709968699954425129709)
              ·
                refine ⟨1558016238262482909423641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4154709968699954425129709 1558016238262482909423641)
                ·
                  refine ⟨1168512178696862182067731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1558016238262482909423641 1168512178696862182067731)
                  ·
                    refine ⟨1752768268045293273101597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1168512178696862182067731 1752768268045293273101597)
                    ·
                      refine ⟨657288100516984977413099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1752768268045293273101597 657288100516984977413099)
                      ·
                        rfl

theorem cell23_1280064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 3, 2, 1, 3].length) (baseStart_1280064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1280064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1280064 prefixEnd_1280064 := by exact prefixLift 1280064
  have htrace : WordTrace (prefixWord ++ tailWord_1280064) baseStart_1280064 baseEnd_1280064 := by
    simpa [prefixWord, tailWord_1280064, baseEnd_1280064] using wordTrace_append hprefix tailTrace_1280064
  have hstable : (prefixWord ++ tailWord_1280064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280064).length < 2 ^ (prefixWord ++ tailWord_1280064).sum := by decide
  have hdescent : baseEnd_1280064 < baseStart_1280064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280087 : List Nat := [1, 1, 3, 2, 2, 1, 3, 1, 3, 4, 2]
def baseStart_1280087 : Nat := 118140960795 + 1280087 * 2 ^ 59
def prefixEnd_1280087 : Nat := 4983230072969 + 3 ^ 40 * 1280087 * 2
def baseEnd_1280087 : Nat := 657299910572038387425493

theorem tailTrace_1280087 : CollatzResearch.WordTrace tailWord_1280087 prefixEnd_1280087 657299910572038387425493 := by
  unfold tailWord_1280087
  simp only [CollatzResearch.WordTrace]
  refine ⟨46688608513470895299366515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31125739008980596866244343 46688608513470895299366515)
  ·
    refine ⟨70032912770206342949049773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46688608513470895299366515 70032912770206342949049773)
    ·
      refine ⟨26262342288827378605893665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70032912770206342949049773 26262342288827378605893665)
      ·
        refine ⟨19696756716620533954420249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26262342288827378605893665 19696756716620533954420249)
        ·
          refine ⟨14772567537465400465815187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19696756716620533954420249 14772567537465400465815187)
          ·
            refine ⟨22158851306198100698722781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14772567537465400465815187 22158851306198100698722781)
            ·
              refine ⟨8309569239824287762021043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22158851306198100698722781 8309569239824287762021043)
              ·
                refine ⟨12464353859736431643031565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8309569239824287762021043 12464353859736431643031565)
                ·
                  refine ⟨4674132697401161866136837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12464353859736431643031565 4674132697401161866136837)
                  ·
                    refine ⟨876399880762717849900657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4674132697401161866136837 876399880762717849900657)
                    ·
                      refine ⟨657299910572038387425493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 876399880762717849900657 657299910572038387425493)
                      ·
                        rfl

theorem cell23_1280087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 3, 4, 2].length) (baseStart_1280087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1280087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1280087 prefixEnd_1280087 := by exact prefixLift 1280087
  have htrace : WordTrace (prefixWord ++ tailWord_1280087) baseStart_1280087 baseEnd_1280087 := by
    simpa [prefixWord, tailWord_1280087, baseEnd_1280087] using wordTrace_append hprefix tailTrace_1280087
  have hstable : (prefixWord ++ tailWord_1280087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280087).length < 2 ^ (prefixWord ++ tailWord_1280087).sum := by decide
  have hdescent : baseEnd_1280087 < baseStart_1280087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280090 : List Nat := [3, 1, 1, 2, 1, 1, 3, 3, 2, 1, 5]
def baseStart_1280090 : Nat := 118140960795 + 1280090 * 2 ^ 59
def prefixEnd_1280090 : Nat := 4983230072969 + 3 ^ 40 * 1280090 * 2
def baseEnd_1280090 : Nat := 657301451014001875687979

theorem tailTrace_1280090 : CollatzResearch.WordTrace tailWord_1280090 prefixEnd_1280090 657301451014001875687979 := by
  unfold tailWord_1280090
  simp only [CollatzResearch.WordTrace]
  refine ⟨11672179483115006702931431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31125811954973351207817149 11672179483115006702931431)
  ·
    refine ⟨17508269224672510054397147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11672179483115006702931431 17508269224672510054397147)
    ·
      refine ⟨26262403837008765081595721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17508269224672510054397147 26262403837008765081595721)
      ·
        refine ⟨19696802877756573811196791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26262403837008765081595721 19696802877756573811196791)
        ·
          refine ⟨29545204316634860716795187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19696802877756573811196791 29545204316634860716795187)
          ·
            refine ⟨44317806474952291075192781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29545204316634860716795187 44317806474952291075192781)
            ·
              refine ⟨16619177428107109153197293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44317806474952291075192781 16619177428107109153197293)
              ·
                refine ⟨6232191535540165932448985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16619177428107109153197293 6232191535540165932448985)
                ·
                  refine ⟨4674143651655124449336739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6232191535540165932448985 4674143651655124449336739)
                  ·
                    refine ⟨7011215477482686674005109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4674143651655124449336739 7011215477482686674005109)
                    ·
                      refine ⟨657301451014001875687979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7011215477482686674005109 657301451014001875687979)
                      ·
                        rfl

theorem cell23_1280090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 3, 2, 1, 5].length) (baseStart_1280090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1280090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1280090 prefixEnd_1280090 := by exact prefixLift 1280090
  have htrace : WordTrace (prefixWord ++ tailWord_1280090) baseStart_1280090 baseEnd_1280090 := by
    simpa [prefixWord, tailWord_1280090, baseEnd_1280090] using wordTrace_append hprefix tailTrace_1280090
  have hstable : (prefixWord ++ tailWord_1280090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280090).length < 2 ^ (prefixWord ++ tailWord_1280090).sum := by decide
  have hdescent : baseEnd_1280090 < baseStart_1280090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280098 : List Nat := [3, 3, 2, 2, 2, 1, 2, 2, 2, 1, 3]
def baseStart_1280098 : Nat := 118140960795 + 1280098 * 2 ^ 59
def prefixEnd_1280098 : Nat := 4983230072969 + 3 ^ 40 * 1280098 * 2
def baseEnd_1280098 : Nat := 657305558859237844387943

theorem tailTrace_1280098 : CollatzResearch.WordTrace tailWord_1280098 prefixEnd_1280098 657305558859237844387943 := by
  unfold tailWord_1280098
  simp only [CollatzResearch.WordTrace]
  refine ⟨11672252429107761044504237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31126006477620696118677965 11672252429107761044504237)
  ·
    refine ⟨4377094660915410391689089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11672252429107761044504237 4377094660915410391689089)
    ·
      refine ⟨3282820995686557793766817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4377094660915410391689089 3282820995686557793766817)
      ·
        refine ⟨2462115746764918345325113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3282820995686557793766817 2462115746764918345325113)
        ·
          refine ⟨1846586810073688758993835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2462115746764918345325113 1846586810073688758993835)
          ·
            refine ⟨2769880215110533138490753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1846586810073688758993835 2769880215110533138490753)
            ·
              refine ⟨2077410161332899853868065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2769880215110533138490753 2077410161332899853868065)
              ·
                refine ⟨1558057620999674890401049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2077410161332899853868065 1558057620999674890401049)
                ·
                  refine ⟨1168543215749756167800787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1558057620999674890401049 1168543215749756167800787)
                  ·
                    refine ⟨1752814823624634251701181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1168543215749756167800787 1752814823624634251701181)
                    ·
                      refine ⟨657305558859237844387943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1752814823624634251701181 657305558859237844387943)
                      ·
                        rfl

theorem cell23_1280098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_1280098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1280098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1280098 prefixEnd_1280098 := by exact prefixLift 1280098
  have htrace : WordTrace (prefixWord ++ tailWord_1280098) baseStart_1280098 baseEnd_1280098 := by
    simpa [prefixWord, tailWord_1280098, baseEnd_1280098] using wordTrace_append hprefix tailTrace_1280098
  have hstable : (prefixWord ++ tailWord_1280098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280098).length < 2 ^ (prefixWord ++ tailWord_1280098).sum := by decide
  have hdescent : baseEnd_1280098 < baseStart_1280098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280121 : List Nat := [1, 2, 1, 3, 4, 1, 2, 3, 2, 2, 2]
def baseStart_1280121 : Nat := 118140960795 + 1280121 * 2 ^ 59
def prefixEnd_1280121 : Nat := 4983230072969 + 3 ^ 40 * 1280121 * 2
def baseEnd_1280121 : Nat := 657317368914291254400337

theorem tailTrace_1280121 : CollatzResearch.WordTrace tailWord_1280121 prefixEnd_1280121 657317368914291254400337 := by
  unfold tailWord_1280121
  simp only [CollatzResearch.WordTrace]
  refine ⟨46689848595347719106104217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31126565730231812737402811 46689848595347719106104217)
  ·
    refine ⟨35017386446510789329578163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46689848595347719106104217 35017386446510789329578163)
    ·
      refine ⟨52526079669766183994367245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35017386446510789329578163 52526079669766183994367245)
      ·
        refine ⟨19697279876162318997887717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52526079669766183994367245 19697279876162318997887717)
        ·
          refine ⟨3693239976780434812103947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19697279876162318997887717 3693239976780434812103947)
          ·
            refine ⟨5539859965170652218155921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3693239976780434812103947 5539859965170652218155921)
            ·
              refine ⟨4154894973877989163616941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5539859965170652218155921 4154894973877989163616941)
              ·
                refine ⟨1558085615204245936356353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4154894973877989163616941 1558085615204245936356353)
                ·
                  refine ⟨1168564211403184452267265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1558085615204245936356353 1168564211403184452267265)
                  ·
                    refine ⟨876423158552388339200449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1168564211403184452267265 876423158552388339200449)
                    ·
                      refine ⟨657317368914291254400337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 876423158552388339200449 657317368914291254400337)
                      ·
                        rfl

theorem cell23_1280121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 3, 2, 2, 2].length) (baseStart_1280121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1280121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1280121 prefixEnd_1280121 := by exact prefixLift 1280121
  have htrace : WordTrace (prefixWord ++ tailWord_1280121) baseStart_1280121 baseEnd_1280121 := by
    simpa [prefixWord, tailWord_1280121, baseEnd_1280121] using wordTrace_append hprefix tailTrace_1280121
  have hstable : (prefixWord ++ tailWord_1280121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280121).length < 2 ^ (prefixWord ++ tailWord_1280121).sum := by decide
  have hdescent : baseEnd_1280121 < baseStart_1280121 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280187 : List Nat := [1, 1, 1, 1, 1, 2, 5, 4, 3, 4]
def baseStart_1280187 : Nat := 118140960795 + 1280187 * 2 ^ 59
def prefixEnd_1280187 : Nat := 4983230072969 + 3 ^ 40 * 1280187 * 2
def baseEnd_1280187 : Nat := 219117086212495998725011

theorem tailTrace_1280187 : CollatzResearch.WordTrace tailWord_1280187 prefixEnd_1280187 219117086212495998725011 := by
  unfold tailWord_1280187
  simp only [CollatzResearch.WordTrace]
  refine ⟨46692255813108612378006815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31128170542072408252004543 46692255813108612378006815)
  ·
    refine ⟨70038383719662918567010223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46692255813108612378006815 70038383719662918567010223)
    ·
      refine ⟨105057575579494377850515335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70038383719662918567010223 105057575579494377850515335)
      ·
        refine ⟨157586363369241566775773003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105057575579494377850515335 157586363369241566775773003)
        ·
          refine ⟨236379545053862350163659505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157586363369241566775773003 236379545053862350163659505)
          ·
            refine ⟨177284658790396762622744629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 236379545053862350163659505 177284658790396762622744629)
            ·
              refine ⟨16620436761599696495882309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 177284658790396762622744629 16620436761599696495882309)
              ·
                refine ⟨3116331892799943092977933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16620436761599696495882309 3116331892799943092977933)
                ·
                  refine ⟨1168624459799978659866725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3116331892799943092977933 1168624459799978659866725)
                  ·
                    refine ⟨219117086212495998725011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1168624459799978659866725 219117086212495998725011)
                    ·
                      rfl

theorem cell23_1280187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 4, 3, 4].length) (baseStart_1280187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1280187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1280187 prefixEnd_1280187 := by exact prefixLift 1280187
  have htrace : WordTrace (prefixWord ++ tailWord_1280187) baseStart_1280187 baseEnd_1280187 := by
    simpa [prefixWord, tailWord_1280187, baseEnd_1280187] using wordTrace_append hprefix tailTrace_1280187
  have hstable : (prefixWord ++ tailWord_1280187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280187).length < 2 ^ (prefixWord ++ tailWord_1280187).sum := by decide
  have hdescent : baseEnd_1280187 < baseStart_1280187 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280197 : List Nat := [1, 3, 1, 1, 1, 1, 6, 1, 1, 4, 3]
def baseStart_1280197 : Nat := 118140960795 + 1280197 * 2 ^ 59
def prefixEnd_1280197 : Nat := 4983230072969 + 3 ^ 40 * 1280197 * 2
def baseEnd_1280197 : Nat := 657356393444032957049987

theorem tailTrace_1280197 : CollatzResearch.WordTrace tailWord_1280197 prefixEnd_1280197 657356393444032957049987 := by
  unfold tailWord_1280197
  simp only [CollatzResearch.WordTrace]
  refine ⟨46692620543072384085870845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31128413695381589390580563 46692620543072384085870845)
  ·
    refine ⟨17509732703652144032201567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46692620543072384085870845 17509732703652144032201567)
    ·
      refine ⟨26264599055478216048302351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17509732703652144032201567 26264599055478216048302351)
      ·
        refine ⟨39396898583217324072453527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26264599055478216048302351 39396898583217324072453527)
        ·
          refine ⟨59095347874825986108680291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39396898583217324072453527 59095347874825986108680291)
          ·
            refine ⟨88643021812238979163020437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59095347874825986108680291 88643021812238979163020437)
            ·
              refine ⟨4155141647448702148266583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 88643021812238979163020437 4155141647448702148266583)
              ·
                refine ⟨6232712471173053222399875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4155141647448702148266583 6232712471173053222399875)
                ·
                  refine ⟨9349068706759579833599813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6232712471173053222399875 9349068706759579833599813)
                  ·
                    refine ⟨1752950382517421218799965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9349068706759579833599813 1752950382517421218799965)
                    ·
                      refine ⟨657356393444032957049987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1752950382517421218799965 657356393444032957049987)
                      ·
                        rfl

theorem cell23_1280197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 1, 1, 4, 3].length) (baseStart_1280197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1280197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1280197 prefixEnd_1280197 := by exact prefixLift 1280197
  have htrace : WordTrace (prefixWord ++ tailWord_1280197) baseStart_1280197 baseEnd_1280197 := by
    simpa [prefixWord, tailWord_1280197, baseEnd_1280197] using wordTrace_append hprefix tailTrace_1280197
  have hstable : (prefixWord ++ tailWord_1280197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280197).length < 2 ^ (prefixWord ++ tailWord_1280197).sum := by decide
  have hdescent : baseEnd_1280197 < baseStart_1280197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280221 : List Nat := [1, 4, 3, 2, 1, 1, 3, 1, 3, 4]
def baseStart_1280221 : Nat := 118140960795 + 1280221 * 2 ^ 59
def prefixEnd_1280221 : Nat := 4983230072969 + 3 ^ 40 * 1280221 * 2
def baseEnd_1280221 : Nat := 219122905659913621049959

theorem tailTrace_1280221 : CollatzResearch.WordTrace tailWord_1280221 prefixEnd_1280221 219122905659913621049959 := by
  unfold tailWord_1280221
  simp only [CollatzResearch.WordTrace]
  refine ⟨46693495894985436184744517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31128997263323624123163011 46693495894985436184744517)
  ·
    refine ⟨8755030480309769284639597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46693495894985436184744517 8755030480309769284639597)
    ·
      refine ⟨3283136430116163481739849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8755030480309769284639597 3283136430116163481739849)
      ·
        refine ⟨2462352322587122611304887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3283136430116163481739849 2462352322587122611304887)
        ·
          refine ⟨3693528483880683916957331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2462352322587122611304887 3693528483880683916957331)
          ·
            refine ⟨5540292725821025875435997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3693528483880683916957331 5540292725821025875435997)
            ·
              refine ⟨2077609772182884703288499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5540292725821025875435997 2077609772182884703288499)
              ·
                refine ⟨3116414658274327054932749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2077609772182884703288499 3116414658274327054932749)
                ·
                  refine ⟨1168655496852872645599781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3116414658274327054932749 1168655496852872645599781)
                  ·
                    refine ⟨219122905659913621049959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1168655496852872645599781 219122905659913621049959)
                    ·
                      rfl

theorem cell23_1280221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_1280221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1280221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1280221 prefixEnd_1280221 := by exact prefixLift 1280221
  have htrace : WordTrace (prefixWord ++ tailWord_1280221) baseStart_1280221 baseEnd_1280221 := by
    simpa [prefixWord, tailWord_1280221, baseEnd_1280221] using wordTrace_append hprefix tailTrace_1280221
  have hstable : (prefixWord ++ tailWord_1280221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280221).length < 2 ^ (prefixWord ++ tailWord_1280221).sum := by decide
  have hdescent : baseEnd_1280221 < baseStart_1280221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280284 : List Nat := [2, 2, 3, 1, 1, 1, 1, 2, 2, 6, 2]
def baseStart_1280284 : Nat := 118140960795 + 1280284 * 2 ^ 59
def prefixEnd_1280284 : Nat := 4983230072969 + 3 ^ 40 * 1280284 * 2
def baseEnd_1280284 : Nat := 657401066260974116662087

theorem tailTrace_1280284 : CollatzResearch.WordTrace tailWord_1280284 prefixEnd_1280284 657401066260974116662087 := by
  unfold tailWord_1280284
  simp only [CollatzResearch.WordTrace]
  refine ⟨23347896846878598972143953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31130529129171465296191937 23347896846878598972143953)
  ·
    refine ⟨17510922635158949229107965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23347896846878598972143953 17510922635158949229107965)
    ·
      refine ⟨6566595988184605960915487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17510922635158949229107965 6566595988184605960915487)
      ·
        refine ⟨9849893982276908941373231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6566595988184605960915487 9849893982276908941373231)
        ·
          refine ⟨14774840973415363412059847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9849893982276908941373231 14774840973415363412059847)
          ·
            refine ⟨22162261460123045118089771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14774840973415363412059847 22162261460123045118089771)
            ·
              refine ⟨33243392190184567677134657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22162261460123045118089771 33243392190184567677134657)
              ·
                refine ⟨24932544142638425757850993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33243392190184567677134657 24932544142638425757850993)
                ·
                  refine ⟨18699408106978819318388245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24932544142638425757850993 18699408106978819318388245)
                  ·
                    refine ⟨876534755014632155549449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18699408106978819318388245 876534755014632155549449)
                    ·
                      refine ⟨657401066260974116662087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 876534755014632155549449 657401066260974116662087)
                      ·
                        rfl

theorem cell23_1280284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 2, 6, 2].length) (baseStart_1280284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1280284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1280284 prefixEnd_1280284 := by exact prefixLift 1280284
  have htrace : WordTrace (prefixWord ++ tailWord_1280284) baseStart_1280284 baseEnd_1280284 := by
    simpa [prefixWord, tailWord_1280284, baseEnd_1280284] using wordTrace_append hprefix tailTrace_1280284
  have hstable : (prefixWord ++ tailWord_1280284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280284).length < 2 ^ (prefixWord ++ tailWord_1280284).sum := by decide
  have hdescent : baseEnd_1280284 < baseStart_1280284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280305 : List Nat := [1, 2, 2, 3, 5, 1, 1, 1, 2, 3, 2]
def baseStart_1280305 : Nat := 118140960795 + 1280305 * 2 ^ 59
def prefixEnd_1280305 : Nat := 4983230072969 + 3 ^ 40 * 1280305 * 2
def baseEnd_1280305 : Nat := 657411849354718534499491

theorem tailTrace_1280305 : CollatzResearch.WordTrace tailWord_1280305 prefixEnd_1280305 657411849354718534499491 := by
  unfold tailWord_1280305
  simp only [CollatzResearch.WordTrace]
  refine ⟨46696559626681118530802369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31131039751120745687201579 46696559626681118530802369)
  ·
    refine ⟨35022419720010838898101777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46696559626681118530802369 35022419720010838898101777)
    ·
      refine ⟨26266814790008129173576333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35022419720010838898101777 26266814790008129173576333)
      ·
        refine ⟨9850055546253048440091125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26266814790008129173576333 9850055546253048440091125)
        ·
          refine ⟨923442707461223291258543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9850055546253048440091125 923442707461223291258543)
          ·
            refine ⟨1385164061191834936887815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 923442707461223291258543 1385164061191834936887815)
            ·
              refine ⟨2077746091787752405331723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1385164061191834936887815 2077746091787752405331723)
              ·
                refine ⟨3116619137681628607997585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2077746091787752405331723 3116619137681628607997585)
                ·
                  refine ⟨2337464353261221455998189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3116619137681628607997585 2337464353261221455998189)
                  ·
                    refine ⟨876549132472958045999321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2337464353261221455998189 876549132472958045999321)
                    ·
                      refine ⟨657411849354718534499491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 876549132472958045999321 657411849354718534499491)
                      ·
                        rfl

theorem cell23_1280305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 1, 2, 3, 2].length) (baseStart_1280305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1280305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1280305 prefixEnd_1280305 := by exact prefixLift 1280305
  have htrace : WordTrace (prefixWord ++ tailWord_1280305) baseStart_1280305 baseEnd_1280305 := by
    simpa [prefixWord, tailWord_1280305, baseEnd_1280305] using wordTrace_append hprefix tailTrace_1280305
  have hstable : (prefixWord ++ tailWord_1280305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280305).length < 2 ^ (prefixWord ++ tailWord_1280305).sum := by decide
  have hdescent : baseEnd_1280305 < baseStart_1280305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280314 : List Nat := [3, 1, 1, 1, 4, 2, 2, 2, 1, 2, 4]
def baseStart_1280314 : Nat := 118140960795 + 1280314 * 2 ^ 59
def prefixEnd_1280314 : Nat := 4983230072969 + 3 ^ 40 * 1280314 * 2
def baseEnd_1280314 : Nat := 657416470680608999286949

theorem tailTrace_1280314 : CollatzResearch.WordTrace tailWord_1280314 prefixEnd_1280314 657416470680608999286949 := by
  unfold tailWord_1280314
  simp only [CollatzResearch.WordTrace]
  refine ⟨11674221970912128266969999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31131258589099008711919997 11674221970912128266969999)
  ·
    refine ⟨17511332956368192400454999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11674221970912128266969999 17511332956368192400454999)
    ·
      refine ⟨26266999434552288600682499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17511332956368192400454999 26266999434552288600682499)
      ·
        refine ⟨39400499151828432901023749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26266999434552288600682499 39400499151828432901023749)
        ·
          refine ⟨7387593590967831168941953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39400499151828432901023749 7387593590967831168941953)
          ·
            refine ⟨5540695193225873376706465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7387593590967831168941953 5540695193225873376706465)
            ·
              refine ⟨4155521394919405032529849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5540695193225873376706465 4155521394919405032529849)
              ·
                refine ⟨3116641046189553774397387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4155521394919405032529849 3116641046189553774397387)
                ·
                  refine ⟨4674961569284330661596081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3116641046189553774397387 4674961569284330661596081)
                  ·
                    refine ⟨3506221176963247996197061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4674961569284330661596081 3506221176963247996197061)
                    ·
                      refine ⟨657416470680608999286949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3506221176963247996197061 657416470680608999286949)
                      ·
                        rfl

theorem cell23_1280314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 2, 1, 2, 4].length) (baseStart_1280314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1280314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1280314 prefixEnd_1280314 := by exact prefixLift 1280314
  have htrace : WordTrace (prefixWord ++ tailWord_1280314) baseStart_1280314 baseEnd_1280314 := by
    simpa [prefixWord, tailWord_1280314, baseEnd_1280314] using wordTrace_append hprefix tailTrace_1280314
  have hstable : (prefixWord ++ tailWord_1280314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280314).length < 2 ^ (prefixWord ++ tailWord_1280314).sum := by decide
  have hdescent : baseEnd_1280314 < baseStart_1280314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280318 : List Nat := [4, 2, 1, 2, 1, 2, 4, 1, 1, 1, 4]
def baseStart_1280318 : Nat := 118140960795 + 1280318 * 2 ^ 59
def prefixEnd_1280318 : Nat := 4983230072969 + 3 ^ 40 * 1280318 * 2
def baseEnd_1280318 : Nat := 657418524603226983636931

theorem tailTrace_1280318 : CollatzResearch.WordTrace tailWord_1280318 prefixEnd_1280318 657418524603226983636931 := by
  unfold tailWord_1280318
  simp only [CollatzResearch.WordTrace]
  refine ⟨5837129221954252718878201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31131355850422681167350405 5837129221954252718878201)
  ·
    refine ⟨4377846916465689539158651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5837129221954252718878201 4377846916465689539158651)
    ·
      refine ⟨6566770374698534308737977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4377846916465689539158651 6566770374698534308737977)
      ·
        refine ⟨4925077781023900731553483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6566770374698534308737977 4925077781023900731553483)
        ·
          refine ⟨7387616671535851097330225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4925077781023900731553483 7387616671535851097330225)
          ·
            refine ⟨5540712503651888322997669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7387616671535851097330225 5540712503651888322997669)
            ·
              refine ⟨1038883594434729060562063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5540712503651888322997669 1038883594434729060562063)
              ·
                refine ⟨1558325391652093590843095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1038883594434729060562063 1558325391652093590843095)
                ·
                  refine ⟨2337488087478140386264643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1558325391652093590843095 2337488087478140386264643)
                  ·
                    refine ⟨3506232131217210579396965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2337488087478140386264643 3506232131217210579396965)
                    ·
                      refine ⟨657418524603226983636931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3506232131217210579396965 657418524603226983636931)
                      ·
                        rfl

theorem cell23_1280318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 4, 1, 1, 1, 4].length) (baseStart_1280318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1280318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1280318 prefixEnd_1280318 := by exact prefixLift 1280318
  have htrace : WordTrace (prefixWord ++ tailWord_1280318) baseStart_1280318 baseEnd_1280318 := by
    simpa [prefixWord, tailWord_1280318, baseEnd_1280318] using wordTrace_append hprefix tailTrace_1280318
  have hstable : (prefixWord ++ tailWord_1280318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280318).length < 2 ^ (prefixWord ++ tailWord_1280318).sum := by decide
  have hdescent : baseEnd_1280318 < baseStart_1280318 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280344 : List Nat := [2, 1, 2, 2, 1, 1, 2, 1, 2, 7, 2]
def baseStart_1280344 : Nat := 118140960795 + 1280344 * 2 ^ 59
def prefixEnd_1280344 : Nat := 4983230072969 + 3 ^ 40 * 1280344 * 2
def baseEnd_1280344 : Nat := 657431875100243881911811

theorem tailTrace_1280344 : CollatzResearch.WordTrace tailWord_1280344 prefixEnd_1280344 657431875100243881911811 := by
  unfold tailWord_1280344
  simp only [CollatzResearch.WordTrace]
  refine ⟨23348991036769914095736043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31131988049026552127648057 23348991036769914095736043)
  ·
    refine ⟨35023486555154871143604065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23348991036769914095736043 35023486555154871143604065)
    ·
      refine ⟨26267614916366153357703049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35023486555154871143604065 26267614916366153357703049)
      ·
        refine ⟨19700711187274615018277287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26267614916366153357703049 19700711187274615018277287)
        ·
          refine ⟨29551066780911922527415931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19700711187274615018277287 29551066780911922527415931)
          ·
            refine ⟨44326600171367883791123897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29551066780911922527415931 44326600171367883791123897)
            ·
              refine ⟨33244950128525912843342923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44326600171367883791123897 33244950128525912843342923)
              ·
                refine ⟨49867425192788869265014385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33244950128525912843342923 49867425192788869265014385)
                ·
                  refine ⟨37400568894591651948760789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49867425192788869265014385 37400568894591651948760789)
                  ·
                    refine ⟨876575833466991842549081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37400568894591651948760789 876575833466991842549081)
                    ·
                      refine ⟨657431875100243881911811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 876575833466991842549081 657431875100243881911811)
                      ·
                        rfl

theorem cell23_1280344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 2, 7, 2].length) (baseStart_1280344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1280344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1280344 prefixEnd_1280344 := by exact prefixLift 1280344
  have htrace : WordTrace (prefixWord ++ tailWord_1280344) baseStart_1280344 baseEnd_1280344 := by
    simpa [prefixWord, tailWord_1280344, baseEnd_1280344] using wordTrace_append hprefix tailTrace_1280344
  have hstable : (prefixWord ++ tailWord_1280344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280344).length < 2 ^ (prefixWord ++ tailWord_1280344).sum := by decide
  have hdescent : baseEnd_1280344 < baseStart_1280344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280351 : List Nat := [1, 1, 2, 3, 1, 2, 2, 5, 2, 1, 3]
def baseStart_1280351 : Nat := 118140960795 + 1280351 * 2 ^ 59
def prefixEnd_1280351 : Nat := 4983230072969 + 3 ^ 40 * 1280351 * 2
def baseEnd_1280351 : Nat := 657435469464825354524279

theorem tailTrace_1280351 : CollatzResearch.WordTrace tailWord_1280351 prefixEnd_1280351 657435469464825354524279 := by
  unfold tailWord_1280351
  simp only [CollatzResearch.WordTrace]
  refine ⟨46698237384514468386976907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31132158256342978924651271 46698237384514468386976907)
  ·
    refine ⟨70047356076771702580465361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46698237384514468386976907 70047356076771702580465361)
    ·
      refine ⟨52535517057578776935349021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70047356076771702580465361 52535517057578776935349021)
      ·
        refine ⟨19700818896592041350755883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52535517057578776935349021 19700818896592041350755883)
        ·
          refine ⟨29551228344888062026133825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19700818896592041350755883 29551228344888062026133825)
          ·
            refine ⟨22163421258666046519600369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29551228344888062026133825 22163421258666046519600369)
            ·
              refine ⟨16622565943999534889700277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22163421258666046519600369 16622565943999534889700277)
              ·
                refine ⟨1558365557249956395909401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16622565943999534889700277 1558365557249956395909401)
                ·
                  refine ⟨1168774167937467296932051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1558365557249956395909401 1168774167937467296932051)
                  ·
                    refine ⟨1753161251906200945398077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1168774167937467296932051 1753161251906200945398077)
                    ·
                      refine ⟨657435469464825354524279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1753161251906200945398077 657435469464825354524279)
                      ·
                        rfl

theorem cell23_1280351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 5, 2, 1, 3].length) (baseStart_1280351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1280351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1280351 prefixEnd_1280351 := by exact prefixLift 1280351
  have htrace : WordTrace (prefixWord ++ tailWord_1280351) baseStart_1280351 baseEnd_1280351 := by
    simpa [prefixWord, tailWord_1280351, baseEnd_1280351] using wordTrace_append hprefix tailTrace_1280351
  have hstable : (prefixWord ++ tailWord_1280351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280351).length < 2 ^ (prefixWord ++ tailWord_1280351).sum := by decide
  have hdescent : baseEnd_1280351 < baseStart_1280351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280367 : List Nat := [1, 1, 2, 1, 3, 1, 2, 2, 4, 6]
def baseStart_1280367 : Nat := 118140960795 + 1280367 * 2 ^ 59
def prefixEnd_1280367 : Nat := 4983230072969 + 3 ^ 40 * 1280367 * 2
def baseEnd_1280367 : Nat := 219147895051765763974735

theorem tailTrace_1280367 : CollatzResearch.WordTrace tailWord_1280367 prefixEnd_1280367 219147895051765763974735 := by
  unfold tailWord_1280367
  simp only [CollatzResearch.WordTrace]
  refine ⟨46698820952456503119559355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31132547301637668746372903 46698820952456503119559355)
  ·
    refine ⟨70048231428684754679339033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46698820952456503119559355 70048231428684754679339033)
    ·
      refine ⟨52536173571513566009504275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70048231428684754679339033 52536173571513566009504275)
      ·
        refine ⟨78804260357270349014256413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52536173571513566009504275 78804260357270349014256413)
        ·
          refine ⟨29551597633976380880346155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78804260357270349014256413 29551597633976380880346155)
          ·
            refine ⟨44327396450964571320519233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29551597633976380880346155 44327396450964571320519233)
            ·
              refine ⟨33245547338223428490389425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44327396450964571320519233 33245547338223428490389425)
              ·
                refine ⟨24934160503667571367792069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33245547338223428490389425 24934160503667571367792069)
                ·
                  refine ⟨4675155094437669631461013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24934160503667571367792069 4675155094437669631461013)
                  ·
                    refine ⟨219147895051765763974735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4675155094437669631461013 219147895051765763974735)
                    ·
                      rfl

theorem cell23_1280367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 4, 6].length) (baseStart_1280367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1280367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1280367 prefixEnd_1280367 := by exact prefixLift 1280367
  have htrace : WordTrace (prefixWord ++ tailWord_1280367) baseStart_1280367 baseEnd_1280367 := by
    simpa [prefixWord, tailWord_1280367, baseEnd_1280367] using wordTrace_append hprefix tailTrace_1280367
  have hstable : (prefixWord ++ tailWord_1280367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280367).length < 2 ^ (prefixWord ++ tailWord_1280367).sum := by decide
  have hdescent : baseEnd_1280367 < baseStart_1280367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280386 : List Nat := [3, 4, 2, 1, 2, 1, 3, 2, 1, 2, 2]
def baseStart_1280386 : Nat := 118140960795 + 1280386 * 2 ^ 59
def prefixEnd_1280386 : Nat := 4983230072969 + 3 ^ 40 * 1280386 * 2
def baseEnd_1280386 : Nat := 657453441287732717586619

theorem tailTrace_1280386 : CollatzResearch.WordTrace tailWord_1280386 prefixEnd_1280386 657453441287732717586619 := by
  unfold tailWord_1280386
  simp only [CollatzResearch.WordTrace]
  refine ⟨11674878484846917341125253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31133009292925112909667341 11674878484846917341125253)
  ·
    refine ⟨2189039715908797001460985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11674878484846917341125253 2189039715908797001460985)
    ·
      refine ⟨1641779786931597751095739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2189039715908797001460985 1641779786931597751095739)
      ·
        refine ⟨2462669680397396626643609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1641779786931597751095739 2462669680397396626643609)
        ·
          refine ⟨1847002260298047469982707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2462669680397396626643609 1847002260298047469982707)
          ·
            refine ⟨2770503390447071204974061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1847002260298047469982707 2770503390447071204974061)
            ·
              refine ⟨1038938771417651701865273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2770503390447071204974061 1038938771417651701865273)
              ·
                refine ⟨779204078563238776398955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1038938771417651701865273 779204078563238776398955)
                ·
                  refine ⟨1168806117844858164598433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 779204078563238776398955 1168806117844858164598433)
                  ·
                    refine ⟨876604588383643623448825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1168806117844858164598433 876604588383643623448825)
                    ·
                      refine ⟨657453441287732717586619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 876604588383643623448825 657453441287732717586619)
                      ·
                        rfl

theorem cell23_1280386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 3, 2, 1, 2, 2].length) (baseStart_1280386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1280386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1280386 prefixEnd_1280386 := by exact prefixLift 1280386
  have htrace : WordTrace (prefixWord ++ tailWord_1280386) baseStart_1280386 baseEnd_1280386 := by
    simpa [prefixWord, tailWord_1280386, baseEnd_1280386] using wordTrace_append hprefix tailTrace_1280386
  have hstable : (prefixWord ++ tailWord_1280386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280386).length < 2 ^ (prefixWord ++ tailWord_1280386).sum := by decide
  have hdescent : baseEnd_1280386 < baseStart_1280386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280406 : List Nat := [5, 3, 1, 2, 2, 1, 1, 2, 1, 2, 3]
def baseStart_1280406 : Nat := 118140960795 + 1280406 * 2 ^ 59
def prefixEnd_1280406 : Nat := 4983230072969 + 3 ^ 40 * 1280406 * 2
def baseEnd_1280406 : Nat := 657463710900822639336527

theorem tailTrace_1280406 : CollatzResearch.WordTrace tailWord_1280406 prefixEnd_1280406 657463710900822639336527 := by
  unfold tailWord_1280406
  simp only [CollatzResearch.WordTrace]
  refine ⟨2918765212457200798764317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31133495599543475186819381 2918765212457200798764317)
  ·
    refine ⟨1094536954671450299536619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2918765212457200798764317 1094536954671450299536619)
    ·
      refine ⟨1641805432007175449304929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1094536954671450299536619 1641805432007175449304929)
      ·
        refine ⟨1231354074005381586978697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1641805432007175449304929 1231354074005381586978697)
        ·
          refine ⟨923515555504036190234023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1231354074005381586978697 923515555504036190234023)
          ·
            refine ⟨1385273333256054285351035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 923515555504036190234023 1385273333256054285351035)
            ·
              refine ⟨2077909999884081428026553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1385273333256054285351035 2077909999884081428026553)
              ·
                refine ⟨1558432499913061071019915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2077909999884081428026553 1558432499913061071019915)
                ·
                  refine ⟨2337648749869591606529873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1558432499913061071019915 2337648749869591606529873)
                  ·
                    refine ⟨1753236562402193704897405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2337648749869591606529873 1753236562402193704897405)
                    ·
                      refine ⟨657463710900822639336527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1753236562402193704897405 657463710900822639336527)
                      ·
                        rfl

theorem cell23_1280406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_1280406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1280406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1280406 prefixEnd_1280406 := by exact prefixLift 1280406
  have htrace : WordTrace (prefixWord ++ tailWord_1280406) baseStart_1280406 baseEnd_1280406 := by
    simpa [prefixWord, tailWord_1280406, baseEnd_1280406] using wordTrace_append hprefix tailTrace_1280406
  have hstable : (prefixWord ++ tailWord_1280406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280406).length < 2 ^ (prefixWord ++ tailWord_1280406).sum := by decide
  have hdescent : baseEnd_1280406 < baseStart_1280406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280481 : List Nat := [1, 2, 3, 1, 2, 2, 1, 2, 1, 6, 2]
def baseStart_1280481 : Nat := 118140960795 + 1280481 * 2 ^ 59
def prefixEnd_1280481 : Nat := 4983230072969 + 3 ^ 40 * 1280481 * 2
def baseEnd_1280481 : Nat := 657502221949909845898681

theorem tailTrace_1280481 : CollatzResearch.WordTrace tailWord_1280481 prefixEnd_1280481 657502221949909845898681 := by
  unfold tailWord_1280481
  simp only [CollatzResearch.WordTrace]
  refine ⟨46702978874043500589209297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31135319249362333726139531 46702978874043500589209297)
  ·
    refine ⟨35027234155532625441906973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46702978874043500589209297 35027234155532625441906973)
    ·
      refine ⟨13135212808324734540715115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35027234155532625441906973 13135212808324734540715115)
      ·
        refine ⟨19702819212487101811072673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13135212808324734540715115 19702819212487101811072673)
        ·
          refine ⟨14777114409365326358304505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19702819212487101811072673 14777114409365326358304505)
          ·
            refine ⟨11082835807023994768728379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14777114409365326358304505 11082835807023994768728379)
            ·
              refine ⟨16624253710535992153092569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11082835807023994768728379 16624253710535992153092569)
              ·
                refine ⟨12468190282901994114819427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16624253710535992153092569 12468190282901994114819427)
                ·
                  refine ⟨18702285424352991172229141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12468190282901994114819427 18702285424352991172229141)
                  ·
                    refine ⟨876669629266546461198241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18702285424352991172229141 876669629266546461198241)
                    ·
                      refine ⟨657502221949909845898681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 876669629266546461198241 657502221949909845898681)
                      ·
                        rfl

theorem cell23_1280481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 6, 2].length) (baseStart_1280481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1280481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1280481 prefixEnd_1280481 := by exact prefixLift 1280481
  have htrace : WordTrace (prefixWord ++ tailWord_1280481) baseStart_1280481 baseEnd_1280481 := by
    simpa [prefixWord, tailWord_1280481, baseEnd_1280481] using wordTrace_append hprefix tailTrace_1280481
  have hstable : (prefixWord ++ tailWord_1280481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280481).length < 2 ^ (prefixWord ++ tailWord_1280481).sum := by decide
  have hdescent : baseEnd_1280481 < baseStart_1280481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280482 : List Nat := [3, 3, 3, 2, 1, 1, 2, 3, 5]
def baseStart_1280482 : Nat := 118140960795 + 1280482 * 2 ^ 59
def prefixEnd_1280482 : Nat := 4983230072969 + 3 ^ 40 * 1280482 * 2
def baseEnd_1280482 : Nat := 73055859492284926887353

theorem tailTrace_1280482 : CollatzResearch.WordTrace tailWord_1280482 prefixEnd_1280482 73055859492284926887353 := by
  unfold tailWord_1280482
  simp only [CollatzResearch.WordTrace]
  refine ⟨11675753836759969439998925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31135343564693251839997133 11675753836759969439998925)
  ·
    refine ⟨4378407688784988539999597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11675753836759969439998925 4378407688784988539999597)
    ·
      refine ⟨1641902883294370702499849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4378407688784988539999597 1641902883294370702499849)
      ·
        refine ⟨1231427162470778026874887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1641902883294370702499849 1231427162470778026874887)
        ·
          refine ⟨1847140743706167040312331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1231427162470778026874887 1847140743706167040312331)
          ·
            refine ⟨2770711115559250560468497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1847140743706167040312331 2770711115559250560468497)
            ·
              refine ⟨2078033336669437920351373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2770711115559250560468497 2078033336669437920351373)
              ·
                refine ⟨779262501251039220131765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2078033336669437920351373 779262501251039220131765)
                ·
                  refine ⟨73055859492284926887353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 779262501251039220131765 73055859492284926887353)
                  ·
                    rfl

theorem cell23_1280482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 3, 5].length) (baseStart_1280482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1280482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1280482 prefixEnd_1280482 := by exact prefixLift 1280482
  have htrace : WordTrace (prefixWord ++ tailWord_1280482) baseStart_1280482 baseEnd_1280482 := by
    simpa [prefixWord, tailWord_1280482, baseEnd_1280482] using wordTrace_append hprefix tailTrace_1280482
  have hstable : (prefixWord ++ tailWord_1280482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280482).length < 2 ^ (prefixWord ++ tailWord_1280482).sum := by decide
  have hdescent : baseEnd_1280482 < baseStart_1280482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280504 : List Nat := [2, 1, 2, 1, 1, 4, 3, 1, 8]
def baseStart_1280504 : Nat := 118140960795 + 1280504 * 2 ^ 59
def prefixEnd_1280504 : Nat := 4983230072969 + 3 ^ 40 * 1280504 * 2
def baseEnd_1280504 : Nat := 73057114667218139545675

theorem tailTrace_1280504 : CollatzResearch.WordTrace tailWord_1280504 prefixEnd_1280504 73057114667218139545675 := by
  unfold tailWord_1280504
  simp only [CollatzResearch.WordTrace]
  refine ⟨23351908876480087758648283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31135878501973450344864377 23351908876480087758648283)
  ·
    refine ⟨35027863314720131637972425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23351908876480087758648283 35027863314720131637972425)
    ·
      refine ⟨26270897486040098728479319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35027863314720131637972425 26270897486040098728479319)
      ·
        refine ⟨39406346229060148092718979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26270897486040098728479319 39406346229060148092718979)
        ·
          refine ⟨59109519343590222139078469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39406346229060148092718979 59109519343590222139078469)
          ·
            refine ⟨11083034876923166651077213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59109519343590222139078469 11083034876923166651077213)
            ·
              refine ⟨4156138078846187494153955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11083034876923166651077213 4156138078846187494153955)
              ·
                refine ⟨6234207118269281241230933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4156138078846187494153955 6234207118269281241230933)
                ·
                  refine ⟨73057114667218139545675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6234207118269281241230933 73057114667218139545675)
                  ·
                    rfl

theorem cell23_1280504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 1, 8].length) (baseStart_1280504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1280504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1280504 prefixEnd_1280504 := by exact prefixLift 1280504
  have htrace : WordTrace (prefixWord ++ tailWord_1280504) baseStart_1280504 baseEnd_1280504 := by
    simpa [prefixWord, tailWord_1280504, baseEnd_1280504] using wordTrace_append hprefix tailTrace_1280504
  have hstable : (prefixWord ++ tailWord_1280504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280504).length < 2 ^ (prefixWord ++ tailWord_1280504).sum := by decide
  have hdescent : baseEnd_1280504 < baseStart_1280504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280571 : List Nat := [1, 1, 1, 1, 1, 2, 1, 2, 3, 8, 2]
def baseStart_1280571 : Nat := 118140960795 + 1280571 * 2 ^ 59
def prefixEnd_1280571 : Nat := 4983230072969 + 3 ^ 40 * 1280571 * 2
def baseEnd_1280571 : Nat := 657548435208814493773267

theorem tailTrace_1280571 : CollatzResearch.WordTrace tailWord_1280571 prefixEnd_1280571 657548435208814493773267 := by
  unfold tailWord_1280571
  simp only [CollatzResearch.WordTrace]
  refine ⟨46706261443717445959985567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31137507629144963973323711 46706261443717445959985567)
  ·
    refine ⟨70059392165576168939978351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46706261443717445959985567 70059392165576168939978351)
    ·
      refine ⟨105089088248364253409967527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70059392165576168939978351 105089088248364253409967527)
      ·
        refine ⟨157633632372546380114951291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105089088248364253409967527 157633632372546380114951291)
        ·
          refine ⟨236450448558819570172426937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157633632372546380114951291 236450448558819570172426937)
          ·
            refine ⟨177337836419114677629320203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 236450448558819570172426937 177337836419114677629320203)
            ·
              refine ⟨266006754628672016443980305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 177337836419114677629320203 266006754628672016443980305)
              ·
                refine ⟨199505065971504012332985229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 266006754628672016443980305 199505065971504012332985229)
                ·
                  refine ⟨74814399739314004624869461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 199505065971504012332985229 74814399739314004624869461)
                  ·
                    refine ⟨876731246945085991697689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 74814399739314004624869461 876731246945085991697689)
                    ·
                      refine ⟨657548435208814493773267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 876731246945085991697689 657548435208814493773267)
                      ·
                        rfl

theorem cell23_1280571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 8, 2].length) (baseStart_1280571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1280571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1280571 prefixEnd_1280571 := by exact prefixLift 1280571
  have htrace : WordTrace (prefixWord ++ tailWord_1280571) baseStart_1280571 baseEnd_1280571 := by
    simpa [prefixWord, tailWord_1280571, baseEnd_1280571] using wordTrace_append hprefix tailTrace_1280571
  have hstable : (prefixWord ++ tailWord_1280571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280571).length < 2 ^ (prefixWord ++ tailWord_1280571).sum := by decide
  have hdescent : baseEnd_1280571 < baseStart_1280571 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280608 : List Nat := [2, 1, 1, 3, 2, 1, 2, 5, 1, 2, 3]
def baseStart_1280608 : Nat := 118140960795 + 1280608 * 2 ^ 59
def prefixEnd_1280608 : Nat := 4983230072969 + 3 ^ 40 * 1280608 * 2
def baseEnd_1280608 : Nat := 657567433993030849010597

theorem tailTrace_1280608 : CollatzResearch.WordTrace tailWord_1280608 prefixEnd_1280608 657567433993030849010597 := by
  unfold tailWord_1280608
  simp only [CollatzResearch.WordTrace]
  refine ⟨23353805472291700639541239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31138407296388934186054985 23353805472291700639541239)
  ·
    refine ⟨35030708208437550959311859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23353805472291700639541239 35030708208437550959311859)
    ·
      refine ⟨52546062312656326438967789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35030708208437550959311859 52546062312656326438967789)
      ·
        refine ⟨19704773367246122414612921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52546062312656326438967789 19704773367246122414612921)
        ·
          refine ⟨14778580025434591810959691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19704773367246122414612921 14778580025434591810959691)
          ·
            refine ⟨22167870038151887716439537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14778580025434591810959691 22167870038151887716439537)
            ·
              refine ⟨16625902528613915787329653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22167870038151887716439537 16625902528613915787329653)
              ·
                refine ⟨1558678362057554605062155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16625902528613915787329653 1558678362057554605062155)
                ·
                  refine ⟨2338017543086331907593233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1558678362057554605062155 2338017543086331907593233)
                  ·
                    refine ⟨1753513157314748930694925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2338017543086331907593233 1753513157314748930694925)
                    ·
                      refine ⟨657567433993030849010597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1753513157314748930694925 657567433993030849010597)
                      ·
                        rfl

theorem cell23_1280608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 5, 1, 2, 3].length) (baseStart_1280608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1280608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1280608 prefixEnd_1280608 := by exact prefixLift 1280608
  have htrace : WordTrace (prefixWord ++ tailWord_1280608) baseStart_1280608 baseEnd_1280608 := by
    simpa [prefixWord, tailWord_1280608, baseEnd_1280608] using wordTrace_append hprefix tailTrace_1280608
  have hstable : (prefixWord ++ tailWord_1280608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280608).length < 2 ^ (prefixWord ++ tailWord_1280608).sum := by decide
  have hdescent : baseEnd_1280608 < baseStart_1280608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280616 : List Nat := [2, 1, 4, 3, 2, 2, 2, 2, 1, 1, 3]
def baseStart_1280616 : Nat := 118140960795 + 1280616 * 2 ^ 59
def prefixEnd_1280616 : Nat := 4983230072969 + 3 ^ 40 * 1280616 * 2
def baseEnd_1280616 : Nat := 657571541838266817710561

theorem tailTrace_1280616 : CollatzResearch.WordTrace tailWord_1280616 prefixEnd_1280616 657571541838266817710561 := by
  unfold tailWord_1280616
  simp only [CollatzResearch.WordTrace]
  refine ⟨23353951364277209322686851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31138601819036279096915801 23353951364277209322686851)
  ·
    refine ⟨35030927046415813984030277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23353951364277209322686851 35030927046415813984030277)
    ·
      refine ⟨6568298821202965122005677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35030927046415813984030277 6568298821202965122005677)
      ·
        refine ⟨2463112057951111920752129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6568298821202965122005677 2463112057951111920752129)
        ·
          refine ⟨1847334043463333940564097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2463112057951111920752129 1847334043463333940564097)
          ·
            refine ⟨1385500532597500455423073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1847334043463333940564097 1385500532597500455423073)
            ·
              refine ⟨1039125399448125341567305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1385500532597500455423073 1039125399448125341567305)
              ·
                refine ⟨779344049586094006175479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1039125399448125341567305 779344049586094006175479)
                ·
                  refine ⟨1169016074379141009263219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 779344049586094006175479 1169016074379141009263219)
                  ·
                    refine ⟨1753524111568711513894829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1169016074379141009263219 1753524111568711513894829)
                    ·
                      refine ⟨657571541838266817710561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1753524111568711513894829 657571541838266817710561)
                      ·
                        rfl

theorem cell23_1280616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 2, 2, 1, 1, 3].length) (baseStart_1280616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1280616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1280616 prefixEnd_1280616 := by exact prefixLift 1280616
  have htrace : WordTrace (prefixWord ++ tailWord_1280616) baseStart_1280616 baseEnd_1280616 := by
    simpa [prefixWord, tailWord_1280616, baseEnd_1280616] using wordTrace_append hprefix tailTrace_1280616
  have hstable : (prefixWord ++ tailWord_1280616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280616).length < 2 ^ (prefixWord ++ tailWord_1280616).sum := by decide
  have hdescent : baseEnd_1280616 < baseStart_1280616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280641 : List Nat := [1, 2, 4, 2, 1, 1, 1, 2, 2, 7]
def baseStart_1280641 : Nat := 118140960795 + 1280641 * 2 ^ 59
def prefixEnd_1280641 : Nat := 4983230072969 + 3 ^ 40 * 1280641 * 2
def baseEnd_1280641 : Nat := 219194792951543073299315

theorem tailTrace_1280641 : CollatzResearch.WordTrace tailWord_1280641 prefixEnd_1280641 219194792951543073299315 := by
  unfold tailWord_1280641
  simp only [CollatzResearch.WordTrace]
  refine ⟨46708814553463847915033777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31139209702309231943355851 46708814553463847915033777)
  ·
    refine ⟨35031610915097885936275333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46708814553463847915033777 35031610915097885936275333)
    ·
      refine ⟨6568427046580853613051625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35031610915097885936275333 6568427046580853613051625)
      ·
        refine ⟨4926320284935640209788719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6568427046580853613051625 4926320284935640209788719)
        ·
          refine ⟨7389480427403460314683079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4926320284935640209788719 7389480427403460314683079)
          ·
            refine ⟨11084220641105190472024619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7389480427403460314683079 11084220641105190472024619)
            ·
              refine ⟨16626330961657785708036929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11084220641105190472024619 16626330961657785708036929)
              ·
                refine ⟨12469748221243339281027697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16626330961657785708036929 12469748221243339281027697)
                ·
                  refine ⟨9352311165932504460770773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12469748221243339281027697 9352311165932504460770773)
                  ·
                    refine ⟨219194792951543073299315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9352311165932504460770773 219194792951543073299315)
                    ·
                      rfl

theorem cell23_1280641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 2, 7].length) (baseStart_1280641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1280641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1280641 prefixEnd_1280641 := by exact prefixLift 1280641
  have htrace : WordTrace (prefixWord ++ tailWord_1280641) baseStart_1280641 baseEnd_1280641 := by
    simpa [prefixWord, tailWord_1280641, baseEnd_1280641] using wordTrace_append hprefix tailTrace_1280641
  have hstable : (prefixWord ++ tailWord_1280641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280641).length < 2 ^ (prefixWord ++ tailWord_1280641).sum := by decide
  have hdescent : baseEnd_1280641 < baseStart_1280641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280665 : List Nat := [1, 2, 1, 2, 1, 2, 5, 3, 1, 3, 2]
def baseStart_1280665 : Nat := 118140960795 + 1280665 * 2 ^ 59
def prefixEnd_1280665 : Nat := 4983230072969 + 3 ^ 40 * 1280665 * 2
def baseEnd_1280665 : Nat := 657596702390337125997835

theorem tailTrace_1280665 : CollatzResearch.WordTrace tailWord_1280665 prefixEnd_1280665 657596702390337125997835 := by
  unfold tailWord_1280665
  simp only [CollatzResearch.WordTrace]
  refine ⟨46709689905376900013907449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31139793270251266675938299 46709689905376900013907449)
  ·
    refine ⟨35032267429032675010430587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46709689905376900013907449 35032267429032675010430587)
    ·
      refine ⟨52548401143549012515645881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35032267429032675010430587 52548401143549012515645881)
      ·
        refine ⟨39411300857661759386734411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52548401143549012515645881 39411300857661759386734411)
        ·
          refine ⟨59116951286492639080101617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39411300857661759386734411 59116951286492639080101617)
          ·
            refine ⟨44337713464869479310076213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59116951286492639080101617 44337713464869479310076213)
            ·
              refine ⟨4156660637331513685319645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44337713464869479310076213 4156660637331513685319645)
              ·
                refine ⟨1558747738999317631994867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4156660637331513685319645 1558747738999317631994867)
                ·
                  refine ⟨2338121608498976447992301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1558747738999317631994867 2338121608498976447992301)
                  ·
                    refine ⟨876795603187116167997113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2338121608498976447992301 876795603187116167997113)
                    ·
                      refine ⟨657596702390337125997835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 876795603187116167997113 657596702390337125997835)
                      ·
                        rfl

theorem cell23_1280665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 3, 1, 3, 2].length) (baseStart_1280665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1280665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1280665 prefixEnd_1280665 := by exact prefixLift 1280665
  have htrace : WordTrace (prefixWord ++ tailWord_1280665) baseStart_1280665 baseEnd_1280665 := by
    simpa [prefixWord, tailWord_1280665, baseEnd_1280665] using wordTrace_append hprefix tailTrace_1280665
  have hstable : (prefixWord ++ tailWord_1280665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280665).length < 2 ^ (prefixWord ++ tailWord_1280665).sum := by decide
  have hdescent : baseEnd_1280665 < baseStart_1280665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280689 : List Nat := [1, 2, 2, 6, 2, 1, 1, 1, 1, 3, 3]
def baseStart_1280689 : Nat := 118140960795 + 1280689 * 2 ^ 59
def prefixEnd_1280689 : Nat := 4983230072969 + 3 ^ 40 * 1280689 * 2
def baseEnd_1280689 : Nat := 657609025926045032097725

theorem tailTrace_1280689 : CollatzResearch.WordTrace tailWord_1280689 prefixEnd_1280689 657609025926045032097725 := by
  unfold tailWord_1280689
  simp only [CollatzResearch.WordTrace]
  refine ⟨46710565257289952112781121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31140376838193301408520747 46710565257289952112781121)
  ·
    refine ⟨35032923942967464084585841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46710565257289952112781121 35032923942967464084585841)
    ·
      refine ⟨26274692957225598063439381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35032923942967464084585841 26274692957225598063439381)
      ·
        refine ⟨1231626232369949909223721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 26274692957225598063439381 1231626232369949909223721)
        ·
          refine ⟨923719674277462431917791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1231626232369949909223721 923719674277462431917791)
          ·
            refine ⟨1385579511416193647876687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 923719674277462431917791 1385579511416193647876687)
            ·
              refine ⟨2078369267124290471815031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1385579511416193647876687 2078369267124290471815031)
              ·
                refine ⟨3117553900686435707722547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2078369267124290471815031 3117553900686435707722547)
                ·
                  refine ⟨4676330851029653561583821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3117553900686435707722547 4676330851029653561583821)
                  ·
                    refine ⟨1753624069136120085593933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4676330851029653561583821 1753624069136120085593933)
                    ·
                      refine ⟨657609025926045032097725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1753624069136120085593933 657609025926045032097725)
                      ·
                        rfl

theorem cell23_1280689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_1280689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1280689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1280689 prefixEnd_1280689 := by exact prefixLift 1280689
  have htrace : WordTrace (prefixWord ++ tailWord_1280689) baseStart_1280689 baseEnd_1280689 := by
    simpa [prefixWord, tailWord_1280689, baseEnd_1280689] using wordTrace_append hprefix tailTrace_1280689
  have hstable : (prefixWord ++ tailWord_1280689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280689).length < 2 ^ (prefixWord ++ tailWord_1280689).sum := by decide
  have hdescent : baseEnd_1280689 < baseStart_1280689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280758 : List Nat := [5, 1, 1, 1, 1, 2, 1, 2, 1, 1, 7]
def baseStart_1280758 : Nat := 118140960795 + 1280758 * 2 ^ 59
def prefixEnd_1280758 : Nat := 4983230072969 + 3 ^ 40 * 1280758 * 2
def baseEnd_1280758 : Nat := 657644456091205262134907

theorem tailTrace_1280758 : CollatzResearch.WordTrace tailWord_1280758 prefixEnd_1280758 657644456091205262134907 := by
  unfold tailWord_1280758
  simp only [CollatzResearch.WordTrace]
  refine ⟨2919567618377498556065183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31142054596026651264695285 2919567618377498556065183)
  ·
    refine ⟨4379351427566247834097775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2919567618377498556065183 4379351427566247834097775)
    ·
      refine ⟨6569027141349371751146663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4379351427566247834097775 6569027141349371751146663)
      ·
        refine ⟨9853540712024057626719995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6569027141349371751146663 9853540712024057626719995)
        ·
          refine ⟨14780311068036086440079993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9853540712024057626719995 14780311068036086440079993)
          ·
            refine ⟨11085233301027064830059995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14780311068036086440079993 11085233301027064830059995)
            ·
              refine ⟨16627849951540597245089993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11085233301027064830059995 16627849951540597245089993)
              ·
                refine ⟨12470887463655447933817495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16627849951540597245089993 12470887463655447933817495)
                ·
                  refine ⟨18706331195483171900726243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12470887463655447933817495 18706331195483171900726243)
                  ·
                    refine ⟨28059496793224757851089365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18706331195483171900726243 28059496793224757851089365)
                    ·
                      refine ⟨657644456091205262134907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 28059496793224757851089365 657644456091205262134907)
                      ·
                        rfl

theorem cell23_1280758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_1280758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1280758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1280758 prefixEnd_1280758 := by exact prefixLift 1280758
  have htrace : WordTrace (prefixWord ++ tailWord_1280758) baseStart_1280758 baseEnd_1280758 := by
    simpa [prefixWord, tailWord_1280758, baseEnd_1280758] using wordTrace_append hprefix tailTrace_1280758
  have hstable : (prefixWord ++ tailWord_1280758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280758).length < 2 ^ (prefixWord ++ tailWord_1280758).sum := by decide
  have hdescent : baseEnd_1280758 < baseStart_1280758 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280761 : List Nat := [1, 2, 1, 3, 1, 1, 1, 3, 2, 8]
def baseStart_1280761 : Nat := 118140960795 + 1280761 * 2 ^ 59
def prefixEnd_1280761 : Nat := 4983230072969 + 3 ^ 40 * 1280761 * 2
def baseEnd_1280761 : Nat := 219215332177722916799131

theorem tailTrace_1280761 : CollatzResearch.WordTrace tailWord_1280761 prefixEnd_1280761 219215332177722916799131 := by
  unfold tailWord_1280761
  simp only [CollatzResearch.WordTrace]
  refine ⟨46713191313029108409402137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31142127542019405606268091 46713191313029108409402137)
  ·
    refine ⟨35034893484771831307051603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46713191313029108409402137 35034893484771831307051603)
    ·
      refine ⟨52552340227157746960577405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35034893484771831307051603 52552340227157746960577405)
      ·
        refine ⟨19707127585184155110216527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52552340227157746960577405 19707127585184155110216527)
        ·
          refine ⟨29560691377776232665324791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19707127585184155110216527 29560691377776232665324791)
          ·
            refine ⟨44341037066664348997987187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29560691377776232665324791 44341037066664348997987187)
            ·
              refine ⟨66511555599996523496980781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44341037066664348997987187 66511555599996523496980781)
              ·
                refine ⟨24941833349998696311367793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66511555599996523496980781 24941833349998696311367793)
                ·
                  refine ⟨18706375012499022233525845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24941833349998696311367793 18706375012499022233525845)
                  ·
                    refine ⟨219215332177722916799131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 18706375012499022233525845 219215332177722916799131)
                    ·
                      rfl

theorem cell23_1280761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 8].length) (baseStart_1280761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1280761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1280761 prefixEnd_1280761 := by exact prefixLift 1280761
  have htrace : WordTrace (prefixWord ++ tailWord_1280761) baseStart_1280761 baseEnd_1280761 := by
    simpa [prefixWord, tailWord_1280761, baseEnd_1280761] using wordTrace_append hprefix tailTrace_1280761
  have hstable : (prefixWord ++ tailWord_1280761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280761).length < 2 ^ (prefixWord ++ tailWord_1280761).sum := by decide
  have hdescent : baseEnd_1280761 < baseStart_1280761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280786 : List Nat := [3, 2, 4, 1, 2, 2, 2, 2, 5]
def baseStart_1280786 : Nat := 118140960795 + 1280786 * 2 ^ 59
def prefixEnd_1280786 : Nat := 4983230072969 + 3 ^ 40 * 1280786 * 2
def baseEnd_1280786 : Nat := 73073203727725683620531

theorem tailTrace_1280786 : CollatzResearch.WordTrace tailWord_1280786 prefixEnd_1280786 73073203727725683620531 := by
  unfold tailWord_1280786
  simp only [CollatzResearch.WordTrace]
  refine ⟨11678525784484634419765553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31142735425292358452708141 11678525784484634419765553)
  ·
    refine ⟨8758894338363475814824165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11678525784484634419765553 8758894338363475814824165)
    ·
      refine ⟨1642292688443151715279531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8758894338363475814824165 1642292688443151715279531)
      ·
        refine ⟨2463439032664727572919297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1642292688443151715279531 2463439032664727572919297)
        ·
          refine ⟨1847579274498545679689473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2463439032664727572919297 1847579274498545679689473)
          ·
            refine ⟨1385684455873909259767105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1847579274498545679689473 1385684455873909259767105)
            ·
              refine ⟨1039263341905431944825329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1385684455873909259767105 1039263341905431944825329)
              ·
                refine ⟨779447506429073958618997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1039263341905431944825329 779447506429073958618997)
                ·
                  refine ⟨73073203727725683620531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 779447506429073958618997 73073203727725683620531)
                  ·
                    rfl

theorem cell23_1280786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 2, 2, 5].length) (baseStart_1280786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1280786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1280786 prefixEnd_1280786 := by exact prefixLift 1280786
  have htrace : WordTrace (prefixWord ++ tailWord_1280786) baseStart_1280786 baseEnd_1280786 := by
    simpa [prefixWord, tailWord_1280786, baseEnd_1280786] using wordTrace_append hprefix tailTrace_1280786
  have hstable : (prefixWord ++ tailWord_1280786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280786).length < 2 ^ (prefixWord ++ tailWord_1280786).sum := by decide
  have hdescent : baseEnd_1280786 < baseStart_1280786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280802 : List Nat := [3, 3, 1, 1, 2, 3, 1, 1, 2, 4, 2]
def baseStart_1280802 : Nat := 118140960795 + 1280802 * 2 ^ 59
def prefixEnd_1280802 : Nat := 4983230072969 + 3 ^ 40 * 1280802 * 2
def baseEnd_1280802 : Nat := 657667049240003089984705

theorem tailTrace_1280802 : CollatzResearch.WordTrace tailWord_1280802 prefixEnd_1280802 657667049240003089984705 := by
  unfold tailWord_1280802
  simp only [CollatzResearch.WordTrace]
  refine ⟨11678671676470143102911165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31143124470587048274429773 11678671676470143102911165)
  ·
    refine ⟨4379501878676303663591687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11678671676470143102911165 4379501878676303663591687)
    ·
      refine ⟨6569252818014455495387531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4379501878676303663591687 6569252818014455495387531)
      ·
        refine ⟨9853879227021683243081297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6569252818014455495387531 9853879227021683243081297)
        ·
          refine ⟨7390409420266262432310973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9853879227021683243081297 7390409420266262432310973)
          ·
            refine ⟨2771403532599848412116615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7390409420266262432310973 2771403532599848412116615)
            ·
              refine ⟨4157105298899772618174923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2771403532599848412116615 4157105298899772618174923)
              ·
                refine ⟨6235657948349658927262385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4157105298899772618174923 6235657948349658927262385)
                ·
                  refine ⟨4676743461262244195446789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6235657948349658927262385 4676743461262244195446789)
                  ·
                    refine ⟨876889398986670786646273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4676743461262244195446789 876889398986670786646273)
                    ·
                      refine ⟨657667049240003089984705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 876889398986670786646273 657667049240003089984705)
                      ·
                        rfl

theorem cell23_1280802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 1, 2, 4, 2].length) (baseStart_1280802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1280802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1280802 prefixEnd_1280802 := by exact prefixLift 1280802
  have htrace : WordTrace (prefixWord ++ tailWord_1280802) baseStart_1280802 baseEnd_1280802 := by
    simpa [prefixWord, tailWord_1280802, baseEnd_1280802] using wordTrace_append hprefix tailTrace_1280802
  have hstable : (prefixWord ++ tailWord_1280802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280802).length < 2 ^ (prefixWord ++ tailWord_1280802).sum := by decide
  have hdescent : baseEnd_1280802 < baseStart_1280802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280835 : List Nat := [1, 1, 1, 3, 1, 4, 1, 2, 5, 1, 3]
def baseStart_1280835 : Nat := 118140960795 + 1280835 * 2 ^ 59
def prefixEnd_1280835 : Nat := 4983230072969 + 3 ^ 40 * 1280835 * 2
def baseEnd_1280835 : Nat := 657683994101601460872053

theorem tailTrace_1280835 : CollatzResearch.WordTrace tailWord_1280835 prefixEnd_1280835 657683994101601460872053 := by
  unfold tailWord_1280835
  simp only [CollatzResearch.WordTrace]
  refine ⟨46715890314761019047595959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31143926876507346031730639 46715890314761019047595959)
  ·
    refine ⟨70073835472141528571393939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46715890314761019047595959 70073835472141528571393939)
    ·
      refine ⟨105110753208212292857090909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70073835472141528571393939 105110753208212292857090909)
      ·
        refine ⟨39416532453079609821409091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105110753208212292857090909 39416532453079609821409091)
        ·
          refine ⟨59124798679619414732113637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39416532453079609821409091 59124798679619414732113637)
          ·
            refine ⟨11085899752428640262271307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59124798679619414732113637 11085899752428640262271307)
            ·
              refine ⟨16628849628642960393406961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11085899752428640262271307 16628849628642960393406961)
              ·
                refine ⟨12471637221482220295055221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16628849628642960393406961 12471637221482220295055221)
                ·
                  refine ⟨1169215989513958152661427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12471637221482220295055221 1169215989513958152661427)
                  ·
                    refine ⟨1753823984270937228992141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1169215989513958152661427 1753823984270937228992141)
                    ·
                      refine ⟨657683994101601460872053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1753823984270937228992141 657683994101601460872053)
                      ·
                        rfl

theorem cell23_1280835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 5, 1, 3].length) (baseStart_1280835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1280835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1280835 prefixEnd_1280835 := by exact prefixLift 1280835
  have htrace : WordTrace (prefixWord ++ tailWord_1280835) baseStart_1280835 baseEnd_1280835 := by
    simpa [prefixWord, tailWord_1280835, baseEnd_1280835] using wordTrace_append hprefix tailTrace_1280835
  have hstable : (prefixWord ++ tailWord_1280835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280835).length < 2 ^ (prefixWord ++ tailWord_1280835).sum := by decide
  have hdescent : baseEnd_1280835 < baseStart_1280835 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280872 : List Nat := [2, 1, 4, 2, 1, 3, 2, 2, 1, 5]
def baseStart_1280872 : Nat := 118140960795 + 1280872 * 2 ^ 59
def prefixEnd_1280872 : Nat := 4983230072969 + 3 ^ 40 * 1280872 * 2
def baseEnd_1280872 : Nat := 219234330961939272036461

theorem tailTrace_1280872 : CollatzResearch.WordTrace tailWord_1280872 prefixEnd_1280872 219234330961939272036461 := by
  unfold tailWord_1280872
  simp only [CollatzResearch.WordTrace]
  refine ⟨23358619907813487183346435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31144826543751316244461913 23358619907813487183346435)
  ·
    refine ⟨35037929861720230775019653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23358619907813487183346435 35037929861720230775019653)
    ·
      refine ⟨6569611849072543270316185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35037929861720230775019653 6569611849072543270316185)
      ·
        refine ⟨4927208886804407452737139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6569611849072543270316185 4927208886804407452737139)
        ·
          refine ⟨7390813330206611179105709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4927208886804407452737139 7390813330206611179105709)
          ·
            refine ⟨2771554998827479192164641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7390813330206611179105709 2771554998827479192164641)
            ·
              refine ⟨2078666249120609394123481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2771554998827479192164641 2078666249120609394123481)
              ·
                refine ⟨1558999686840457045592611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2078666249120609394123481 1558999686840457045592611)
                ·
                  refine ⟨2338499530260685568388917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1558999686840457045592611 2338499530260685568388917)
                  ·
                    refine ⟨219234330961939272036461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2338499530260685568388917 219234330961939272036461)
                    ·
                      rfl

theorem cell23_1280872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 2, 1, 5].length) (baseStart_1280872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1280872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1280872 prefixEnd_1280872 := by exact prefixLift 1280872
  have htrace : WordTrace (prefixWord ++ tailWord_1280872) baseStart_1280872 baseEnd_1280872 := by
    simpa [prefixWord, tailWord_1280872, baseEnd_1280872] using wordTrace_append hprefix tailTrace_1280872
  have hstable : (prefixWord ++ tailWord_1280872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280872).length < 2 ^ (prefixWord ++ tailWord_1280872).sum := by decide
  have hdescent : baseEnd_1280872 < baseStart_1280872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280875 : List Nat := [1, 1, 1, 1, 2, 2, 5, 4, 1, 1, 4]
def baseStart_1280875 : Nat := 118140960795 + 1280875 * 2 ^ 59
def prefixEnd_1280875 : Nat := 4983230072969 + 3 ^ 40 * 1280875 * 2
def baseEnd_1280875 : Nat := 657704533327781304371869

theorem tailTrace_1280875 : CollatzResearch.WordTrace tailWord_1280875 prefixEnd_1280875 657704533327781304371869 := by
  unfold tailWord_1280875
  simp only [CollatzResearch.WordTrace]
  refine ⟨46717349234616105879052079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31144899489744070586034719 46717349234616105879052079)
  ·
    refine ⟨70076023851924158818578119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46717349234616105879052079 70076023851924158818578119)
    ·
      refine ⟨105114035777886238227867179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70076023851924158818578119 105114035777886238227867179)
      ·
        refine ⟨157671053666829357341800769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105114035777886238227867179 157671053666829357341800769)
        ·
          refine ⟨118253290250122018006350577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157671053666829357341800769 118253290250122018006350577)
          ·
            refine ⟨88689967687591513504762933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118253290250122018006350577 88689967687591513504762933)
            ·
              refine ⟨8314684470711704391071525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 88689967687591513504762933 8314684470711704391071525)
              ·
                refine ⟨1559003338258444573325911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8314684470711704391071525 1559003338258444573325911)
                ·
                  refine ⟨2338505007387666859988867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1559003338258444573325911 2338505007387666859988867)
                  ·
                    refine ⟨3507757511081500289983301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2338505007387666859988867 3507757511081500289983301)
                    ·
                      refine ⟨657704533327781304371869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3507757511081500289983301 657704533327781304371869)
                      ·
                        rfl

theorem cell23_1280875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 4, 1, 1, 4].length) (baseStart_1280875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1280875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1280875 prefixEnd_1280875 := by exact prefixLift 1280875
  have htrace : WordTrace (prefixWord ++ tailWord_1280875) baseStart_1280875 baseEnd_1280875 := by
    simpa [prefixWord, tailWord_1280875, baseEnd_1280875] using wordTrace_append hprefix tailTrace_1280875
  have hstable : (prefixWord ++ tailWord_1280875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280875).length < 2 ^ (prefixWord ++ tailWord_1280875).sum := by decide
  have hdescent : baseEnd_1280875 < baseStart_1280875 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280892 : List Nat := [2, 2, 2, 1, 1, 1, 1, 4, 5, 2, 2]
def baseStart_1280892 : Nat := 118140960795 + 1280892 * 2 ^ 59
def prefixEnd_1280892 : Nat := 4983230072969 + 3 ^ 40 * 1280892 * 2
def baseEnd_1280892 : Nat := 657713262498907737859291

theorem tailTrace_1280892 : CollatzResearch.WordTrace tailWord_1280892 prefixEnd_1280892 657713262498907737859291 := by
  unfold tailWord_1280892
  simp only [CollatzResearch.WordTrace]
  refine ⟨23358984637777258891210465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31145312850369678521613953 23358984637777258891210465)
  ·
    refine ⟨17519238478332944168407849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23358984637777258891210465 17519238478332944168407849)
    ·
      refine ⟨13139428858749708126305887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17519238478332944168407849 13139428858749708126305887)
      ·
        refine ⟨19709143288124562189458831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13139428858749708126305887 19709143288124562189458831)
        ·
          refine ⟨29563714932186843284188247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19709143288124562189458831 29563714932186843284188247)
          ·
            refine ⟨44345572398280264926282371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29563714932186843284188247 44345572398280264926282371)
            ·
              refine ⟨66518358597420397389423557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44345572398280264926282371 66518358597420397389423557)
              ·
                refine ⟨12472192237016324510516917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66518358597420397389423557 12472192237016324510516917)
                ·
                  refine ⟨1169268022220280422860961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12472192237016324510516917 1169268022220280422860961)
                  ·
                    refine ⟨876951016665210317145721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1169268022220280422860961 876951016665210317145721)
                    ·
                      refine ⟨657713262498907737859291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 876951016665210317145721 657713262498907737859291)
                      ·
                        rfl

theorem cell23_1280892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 5, 2, 2].length) (baseStart_1280892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1280892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1280892 prefixEnd_1280892 := by exact prefixLift 1280892
  have htrace : WordTrace (prefixWord ++ tailWord_1280892) baseStart_1280892 baseEnd_1280892 := by
    simpa [prefixWord, tailWord_1280892, baseEnd_1280892] using wordTrace_append hprefix tailTrace_1280892
  have hstable : (prefixWord ++ tailWord_1280892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280892).length < 2 ^ (prefixWord ++ tailWord_1280892).sum := by decide
  have hdescent : baseEnd_1280892 < baseStart_1280892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280929 : List Nat := [1, 2, 3, 4, 1, 1, 3, 2, 1, 2, 3]
def baseStart_1280929 : Nat := 118140960795 + 1280929 * 2 ^ 59
def prefixEnd_1280929 : Nat := 4983230072969 + 3 ^ 40 * 1280929 * 2
def baseEnd_1280929 : Nat := 657732261283124093096621

theorem tailTrace_1280929 : CollatzResearch.WordTrace tailWord_1280929 prefixEnd_1280929 657732261283124093096621 := by
  unfold tailWord_1280929
  simp only [CollatzResearch.WordTrace]
  refine ⟨46719318776420473101517841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31146212517613648734345227 46719318776420473101517841)
  ·
    refine ⟨35039489082315354826138381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46719318776420473101517841 35039489082315354826138381)
    ·
      refine ⟨13139808405868258059801893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35039489082315354826138381 13139808405868258059801893)
      ·
        refine ⟨2463714076100298386212855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13139808405868258059801893 2463714076100298386212855)
        ·
          refine ⟨3695571114150447579319283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2463714076100298386212855 3695571114150447579319283)
          ·
            refine ⟨5543356671225671368978925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3695571114150447579319283 5543356671225671368978925)
            ·
              refine ⟨2078758751709626763367097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5543356671225671368978925 2078758751709626763367097)
              ·
                refine ⟨1559069063782220072525323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2078758751709626763367097 1559069063782220072525323)
                ·
                  refine ⟨2338603595673330108787985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1559069063782220072525323 2338603595673330108787985)
                  ·
                    refine ⟨1753952696754997581590989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2338603595673330108787985 1753952696754997581590989)
                    ·
                      refine ⟨657732261283124093096621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1753952696754997581590989 657732261283124093096621)
                      ·
                        rfl

theorem cell23_1280929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_1280929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1280929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1280929 prefixEnd_1280929 := by exact prefixLift 1280929
  have htrace : WordTrace (prefixWord ++ tailWord_1280929) baseStart_1280929 baseEnd_1280929 := by
    simpa [prefixWord, tailWord_1280929, baseEnd_1280929] using wordTrace_append hprefix tailTrace_1280929
  have hstable : (prefixWord ++ tailWord_1280929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280929).length < 2 ^ (prefixWord ++ tailWord_1280929).sum := by decide
  have hdescent : baseEnd_1280929 < baseStart_1280929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280973 : List Nat := [1, 6, 3, 1, 1, 1, 2, 1, 1, 2, 4]
def baseStart_1280973 : Nat := 118140960795 + 1280973 * 2 ^ 59
def prefixEnd_1280973 : Nat := 4983230072969 + 3 ^ 40 * 1280973 * 2
def baseEnd_1280973 : Nat := 657754854431921920946419

theorem tailTrace_1280973 : CollatzResearch.WordTrace tailWord_1280973 prefixEnd_1280973 657754854431921920946419 := by
  unfold tailWord_1280973
  simp only [CollatzResearch.WordTrace]
  refine ⟨46720923588261068616119573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31147282392174045744079715 46720923588261068616119573)
  ·
    refine ⟨2190043293199737591380605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 46720923588261068616119573 2190043293199737591380605)
    ·
      refine ⟨821266234949901596767727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2190043293199737591380605 821266234949901596767727)
      ·
        refine ⟨1231899352424852395151591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 821266234949901596767727 1231899352424852395151591)
        ·
          refine ⟨1847849028637278592727387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1231899352424852395151591 1847849028637278592727387)
          ·
            refine ⟨2771773542955917889091081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1847849028637278592727387 2771773542955917889091081)
            ·
              refine ⟨2078830157216938416818311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2771773542955917889091081 2078830157216938416818311)
              ·
                refine ⟨3118245235825407625227467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2078830157216938416818311 3118245235825407625227467)
                ·
                  refine ⟨4677367853738111437841201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3118245235825407625227467 4677367853738111437841201)
                  ·
                    refine ⟨3508025890303583578380901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4677367853738111437841201 3508025890303583578380901)
                    ·
                      refine ⟨657754854431921920946419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3508025890303583578380901 657754854431921920946419)
                      ·
                        rfl

theorem cell23_1280973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_1280973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1280973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1280973 prefixEnd_1280973 := by exact prefixLift 1280973
  have htrace : WordTrace (prefixWord ++ tailWord_1280973) baseStart_1280973 baseEnd_1280973 := by
    simpa [prefixWord, tailWord_1280973, baseEnd_1280973] using wordTrace_append hprefix tailTrace_1280973
  have hstable : (prefixWord ++ tailWord_1280973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280973).length < 2 ^ (prefixWord ++ tailWord_1280973).sum := by decide
  have hdescent : baseEnd_1280973 < baseStart_1280973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280975 : List Nat := [1, 1, 2, 1, 1, 7, 1, 1, 2, 6]
def baseStart_1280975 : Nat := 118140960795 + 1280975 * 2 ^ 59
def prefixEnd_1280975 : Nat := 4983230072969 + 3 ^ 40 * 1280975 * 2
def baseEnd_1280975 : Nat := 219251960464410304373803

theorem tailTrace_1280975 : CollatzResearch.WordTrace tailWord_1280975 prefixEnd_1280975 219251960464410304373803 := by
  unfold tailWord_1280975
  simp only [CollatzResearch.WordTrace]
  refine ⟨46720996534253822957692379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31147331022835881971794919 46720996534253822957692379)
  ·
    refine ⟨70081494801380734436538569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46720996534253822957692379 70081494801380734436538569)
    ·
      refine ⟨52561121101035550827403927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70081494801380734436538569 52561121101035550827403927)
      ·
        refine ⟨78841681651553326241105891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52561121101035550827403927 78841681651553326241105891)
        ·
          refine ⟨118262522477329989361658837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78841681651553326241105891 118262522477329989361658837)
          ·
            refine ⟨2771777870562421625663879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 118262522477329989361658837 2771777870562421625663879)
            ·
              refine ⟨4157666805843632438495819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2771777870562421625663879 4157666805843632438495819)
              ·
                refine ⟨6236500208765448657743729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4157666805843632438495819 6236500208765448657743729)
                ·
                  refine ⟨4677375156574086493307797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6236500208765448657743729 4677375156574086493307797)
                  ·
                    refine ⟨219251960464410304373803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4677375156574086493307797 219251960464410304373803)
                    ·
                      rfl

theorem cell23_1280975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 1, 2, 6].length) (baseStart_1280975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1280975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1280975 prefixEnd_1280975 := by exact prefixLift 1280975
  have htrace : WordTrace (prefixWord ++ tailWord_1280975) baseStart_1280975 baseEnd_1280975 := by
    simpa [prefixWord, tailWord_1280975, baseEnd_1280975] using wordTrace_append hprefix tailTrace_1280975
  have hstable : (prefixWord ++ tailWord_1280975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280975).length < 2 ^ (prefixWord ++ tailWord_1280975).sum := by decide
  have hdescent : baseEnd_1280975 < baseStart_1280975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280995 : List Nat := [1, 1, 1, 6, 1, 1, 1, 2, 1, 4, 4]
def baseStart_1280995 : Nat := 118140960795 + 1280995 * 2 ^ 59
def prefixEnd_1280995 : Nat := 4983230072969 + 3 ^ 40 * 1280995 * 2
def baseEnd_1280995 : Nat := 657766151006320834871317

theorem tailTrace_1280995 : CollatzResearch.WordTrace tailWord_1280995 prefixEnd_1280995 657766151006320834871317 := by
  unfold tailWord_1280995
  simp only [CollatzResearch.WordTrace]
  refine ⟨46721725994181366373420439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31147817329454244248946959 46721725994181366373420439)
  ·
    refine ⟨70082588991272049560130659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46721725994181366373420439 70082588991272049560130659)
    ·
      refine ⟨105123883486908074340195989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70082588991272049560130659 105123883486908074340195989)
      ·
        refine ⟨4927682038448815984696687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 105123883486908074340195989 4927682038448815984696687)
        ·
          refine ⟨7391523057673223977045031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4927682038448815984696687 7391523057673223977045031)
          ·
            refine ⟨11087284586509835965567547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7391523057673223977045031 11087284586509835965567547)
            ·
              refine ⟨16630926879764753948351321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11087284586509835965567547 16630926879764753948351321)
              ·
                refine ⟨12473195159823565461263491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16630926879764753948351321 12473195159823565461263491)
                ·
                  refine ⟨18709792739735348191895237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12473195159823565461263491 18709792739735348191895237)
                  ·
                    refine ⟨3508086138700377785980357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18709792739735348191895237 3508086138700377785980357)
                    ·
                      refine ⟨657766151006320834871317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3508086138700377785980357 657766151006320834871317)
                      ·
                        rfl

theorem cell23_1280995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_1280995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1280995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1280995 prefixEnd_1280995 := by exact prefixLift 1280995
  have htrace : WordTrace (prefixWord ++ tailWord_1280995) baseStart_1280995 baseEnd_1280995 := by
    simpa [prefixWord, tailWord_1280995, baseEnd_1280995] using wordTrace_append hprefix tailTrace_1280995
  have hstable : (prefixWord ++ tailWord_1280995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280995).length < 2 ^ (prefixWord ++ tailWord_1280995).sum := by decide
  have hdescent : baseEnd_1280995 < baseStart_1280995 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280999 : List Nat := [1, 1, 5, 2, 2, 1, 2, 2, 1, 4, 2]
def baseStart_1280999 : Nat := 118140960795 + 1280999 * 2 ^ 59
def prefixEnd_1280999 : Nat := 4983230072969 + 3 ^ 40 * 1280999 * 2
def baseEnd_1280999 : Nat := 657768204928938819221299

theorem tailTrace_1280999 : CollatzResearch.WordTrace tailWord_1280999 prefixEnd_1280999 657768204928938819221299 := by
  unfold tailWord_1280999
  simp only [CollatzResearch.WordTrace]
  refine ⟨46721871886166875056566051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31147914590777916704377367 46721871886166875056566051)
  ·
    refine ⟨70082807829250312584849077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46721871886166875056566051 70082807829250312584849077)
    ·
      refine ⟨6570263233992216804829601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 70082807829250312584849077 6570263233992216804829601)
      ·
        refine ⟨4927697425494162603622201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6570263233992216804829601 4927697425494162603622201)
        ·
          refine ⟨3695773069120621952716651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4927697425494162603622201 3695773069120621952716651)
          ·
            refine ⟨5543659603680932929074977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3695773069120621952716651 5543659603680932929074977)
            ·
              refine ⟨4157744702760699696806233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5543659603680932929074977 4157744702760699696806233)
              ·
                refine ⟨3118308527070524772604675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4157744702760699696806233 3118308527070524772604675)
                ·
                  refine ⟨4677462790605787158907013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3118308527070524772604675 4677462790605787158907013)
                  ·
                    refine ⟨877024273238585092295065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4677462790605787158907013 877024273238585092295065)
                    ·
                      refine ⟨657768204928938819221299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 877024273238585092295065 657768204928938819221299)
                      ·
                        rfl

theorem cell23_1280999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 2, 1, 4, 2].length) (baseStart_1280999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1280999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1280999 prefixEnd_1280999 := by exact prefixLift 1280999
  have htrace : WordTrace (prefixWord ++ tailWord_1280999) baseStart_1280999 baseEnd_1280999 := by
    simpa [prefixWord, tailWord_1280999, baseEnd_1280999] using wordTrace_append hprefix tailTrace_1280999
  have hstable : (prefixWord ++ tailWord_1280999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280999).length < 2 ^ (prefixWord ++ tailWord_1280999).sum := by decide
  have hdescent : baseEnd_1280999 < baseStart_1280999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281010 : List Nat := [3, 2, 1, 5, 2, 1, 1, 2, 2, 1, 3]
def baseStart_1281010 : Nat := 118140960795 + 1281010 * 2 ^ 59
def prefixEnd_1281010 : Nat := 4983230072969 + 3 ^ 40 * 1281010 * 2
def baseEnd_1281010 : Nat := 657773853216138276183749

theorem tailTrace_1281010 : CollatzResearch.WordTrace tailWord_1281010 prefixEnd_1281010 657773853216138276183749 := by
  unfold tailWord_1281010
  simp only [CollatzResearch.WordTrace]
  refine ⟨11680568272281755983804121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31148182059418015956810989 11680568272281755983804121)
  ·
    refine ⟨8760426204211316987853091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11680568272281755983804121 8760426204211316987853091)
    ·
      refine ⟨13140639306316975481779637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8760426204211316987853091 13140639306316975481779637)
      ·
        refine ⟨1231934934967216451416841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13140639306316975481779637 1231934934967216451416841)
        ·
          refine ⟨923951201225412338562631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1231934934967216451416841 923951201225412338562631)
          ·
            refine ⟨1385926801838118507843947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 923951201225412338562631 1385926801838118507843947)
            ·
              refine ⟨2078890202757177761765921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1385926801838118507843947 2078890202757177761765921)
              ·
                refine ⟨1559167652067883321324441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2078890202757177761765921 1559167652067883321324441)
                ·
                  refine ⟨1169375739050912490993331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1559167652067883321324441 1169375739050912490993331)
                  ·
                    refine ⟨1754063608576368736489997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1169375739050912490993331 1754063608576368736489997)
                    ·
                      refine ⟨657773853216138276183749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1754063608576368736489997 657773853216138276183749)
                      ·
                        rfl

theorem cell23_1281010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_1281010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1281010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1281010 prefixEnd_1281010 := by exact prefixLift 1281010
  have htrace : WordTrace (prefixWord ++ tailWord_1281010) baseStart_1281010 baseEnd_1281010 := by
    simpa [prefixWord, tailWord_1281010, baseEnd_1281010] using wordTrace_append hprefix tailTrace_1281010
  have hstable : (prefixWord ++ tailWord_1281010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281010).length < 2 ^ (prefixWord ++ tailWord_1281010).sum := by decide
  have hdescent : baseEnd_1281010 < baseStart_1281010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281032 : List Nat := [2, 1, 3, 2, 1, 3, 2, 1, 2, 3, 3]
def baseStart_1281032 : Nat := 118140960795 + 1281032 * 2 ^ 59
def prefixEnd_1281032 : Nat := 4983230072969 + 3 ^ 40 * 1281032 * 2
def baseEnd_1281032 : Nat := 657785149790537190108647

theorem tailTrace_1281032 : CollatzResearch.WordTrace tailWord_1281032 prefixEnd_1281032 657785149790537190108647 := by
  unfold tailWord_1281032
  simp only [CollatzResearch.WordTrace]
  refine ⟨23361537747523660846258675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31148716996698214461678233 23361537747523660846258675)
  ·
    refine ⟨35042306621285491269388013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23361537747523660846258675 35042306621285491269388013)
    ·
      refine ⟨13140864982982059226020505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35042306621285491269388013 13140864982982059226020505)
      ·
        refine ⟨9855648737236544419515379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13140864982982059226020505 9855648737236544419515379)
        ·
          refine ⟨14783473105854816629273069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9855648737236544419515379 14783473105854816629273069)
          ·
            refine ⟨5543802414695556235977401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14783473105854816629273069 5543802414695556235977401)
            ·
              refine ⟨4157851811021667176983051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5543802414695556235977401 4157851811021667176983051)
              ·
                refine ⟨6236777716532500765474577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4157851811021667176983051 6236777716532500765474577)
                ·
                  refine ⟨4677583287399375574105933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6236777716532500765474577 4677583287399375574105933)
                  ·
                    refine ⟨1754093732774765840289725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4677583287399375574105933 1754093732774765840289725)
                    ·
                      refine ⟨657785149790537190108647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1754093732774765840289725 657785149790537190108647)
                      ·
                        rfl

theorem cell23_1281032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 1, 2, 3, 3].length) (baseStart_1281032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1281032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1281032 prefixEnd_1281032 := by exact prefixLift 1281032
  have htrace : WordTrace (prefixWord ++ tailWord_1281032) baseStart_1281032 baseEnd_1281032 := by
    simpa [prefixWord, tailWord_1281032, baseEnd_1281032] using wordTrace_append hprefix tailTrace_1281032
  have hstable : (prefixWord ++ tailWord_1281032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281032).length < 2 ^ (prefixWord ++ tailWord_1281032).sum := by decide
  have hdescent : baseEnd_1281032 < baseStart_1281032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281035 : List Nat := [1, 1, 1, 1, 6, 2, 1, 2, 1, 7]
def baseStart_1281035 : Nat := 118140960795 + 1281035 * 2 ^ 59
def prefixEnd_1281035 : Nat := 4983230072969 + 3 ^ 40 * 1281035 * 2
def baseEnd_1281035 : Nat := 219262230077500226123711

theorem tailTrace_1281035 : CollatzResearch.WordTrace tailWord_1281035 prefixEnd_1281035 219262230077500226123711 := by
  unfold tailWord_1281035
  simp only [CollatzResearch.WordTrace]
  refine ⟨46723184914036453204876559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31148789942690968803251039 46723184914036453204876559)
  ·
    refine ⟨70084777371054679807314839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46723184914036453204876559 70084777371054679807314839)
    ·
      refine ⟨105127166056582019710972259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70084777371054679807314839 105127166056582019710972259)
      ·
        refine ⟨157690749084873029566458389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105127166056582019710972259 157690749084873029566458389)
        ·
          refine ⟨7391753863353423260927737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 157690749084873029566458389 7391753863353423260927737)
          ·
            refine ⟨5543815397515067445695803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7391753863353423260927737 5543815397515067445695803)
            ·
              refine ⟨8315723096272601168543705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5543815397515067445695803 8315723096272601168543705)
              ·
                refine ⟨6236792322204450876407779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8315723096272601168543705 6236792322204450876407779)
                ·
                  refine ⟨9355188483306676314611669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6236792322204450876407779 9355188483306676314611669)
                  ·
                    refine ⟨219262230077500226123711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9355188483306676314611669 219262230077500226123711)
                    ·
                      rfl

theorem cell23_1281035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 2, 1, 7].length) (baseStart_1281035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1281035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1281035 prefixEnd_1281035 := by exact prefixLift 1281035
  have htrace : WordTrace (prefixWord ++ tailWord_1281035) baseStart_1281035 baseEnd_1281035 := by
    simpa [prefixWord, tailWord_1281035, baseEnd_1281035] using wordTrace_append hprefix tailTrace_1281035
  have hstable : (prefixWord ++ tailWord_1281035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281035).length < 2 ^ (prefixWord ++ tailWord_1281035).sum := by decide
  have hdescent : baseEnd_1281035 < baseStart_1281035 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281072 : List Nat := [2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 4]
def baseStart_1281072 : Nat := 118140960795 + 1281072 * 2 ^ 59
def prefixEnd_1281072 : Nat := 4983230072969 + 3 ^ 40 * 1281072 * 2
def baseEnd_1281072 : Nat := 657805689016717033608463

theorem tailTrace_1281072 : CollatzResearch.WordTrace tailWord_1281072 prefixEnd_1281072 657805689016717033608463 := by
  unfold tailWord_1281072
  simp only [CollatzResearch.WordTrace]
  refine ⟨23362267207451204261986735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31149689609934939015982313 23362267207451204261986735)
  ·
    refine ⟨35043400811176806392980103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23362267207451204261986735 35043400811176806392980103)
    ·
      refine ⟨52565101216765209589470155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35043400811176806392980103 52565101216765209589470155)
      ·
        refine ⟨78847651825147814384205233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52565101216765209589470155 78847651825147814384205233)
        ·
          refine ⟨59135738868860860788153925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78847651825147814384205233 59135738868860860788153925)
          ·
            refine ⟨11087951037911411397778861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59135738868860860788153925 11087951037911411397778861)
            ·
              refine ⟨4157981639216779274167073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11087951037911411397778861 4157981639216779274167073)
              ·
                refine ⟨3118486229412584455625305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4157981639216779274167073 3118486229412584455625305)
                ·
                  refine ⟨2338864672059438341718979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3118486229412584455625305 2338864672059438341718979)
                  ·
                    refine ⟨3508297008089157512578469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2338864672059438341718979 3508297008089157512578469)
                    ·
                      refine ⟨657805689016717033608463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3508297008089157512578469 657805689016717033608463)
                      ·
                        rfl

theorem cell23_1281072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 4].length) (baseStart_1281072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1281072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1281072 prefixEnd_1281072 := by exact prefixLift 1281072
  have htrace : WordTrace (prefixWord ++ tailWord_1281072) baseStart_1281072 baseEnd_1281072 := by
    simpa [prefixWord, tailWord_1281072, baseEnd_1281072] using wordTrace_append hprefix tailTrace_1281072
  have hstable : (prefixWord ++ tailWord_1281072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281072).length < 2 ^ (prefixWord ++ tailWord_1281072).sum := by decide
  have hdescent : baseEnd_1281072 < baseStart_1281072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281109 : List Nat := [1, 3, 2, 2, 1, 2, 4, 1, 2, 2, 3]
def baseStart_1281109 : Nat := 118140960795 + 1281109 * 2 ^ 59
def prefixEnd_1281109 : Nat := 4983230072969 + 3 ^ 40 * 1281109 * 2
def baseEnd_1281109 : Nat := 657824687800933388845793

theorem tailTrace_1281109 : CollatzResearch.WordTrace tailWord_1281109 prefixEnd_1281109 657824687800933388845793 := by
  unfold tailWord_1281109
  simp only [CollatzResearch.WordTrace]
  refine ⟨46725883915768363843070381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31150589277178909228713587 46725883915768363843070381)
  ·
    refine ⟨17522206468413136441151393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46725883915768363843070381 17522206468413136441151393)
    ·
      refine ⟨13141654851309852330863545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17522206468413136441151393 13141654851309852330863545)
      ·
        refine ⟨9856241138482389248147659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13141654851309852330863545 9856241138482389248147659)
        ·
          refine ⟨14784361707723583872221489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9856241138482389248147659 14784361707723583872221489)
          ·
            refine ⟨11088271280792687904166117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14784361707723583872221489 11088271280792687904166117)
            ·
              refine ⟨2079050865148628982031147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11088271280792687904166117 2079050865148628982031147)
              ·
                refine ⟨3118576297722943473046721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2079050865148628982031147 3118576297722943473046721)
                ·
                  refine ⟨2338932223292207604785041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3118576297722943473046721 2338932223292207604785041)
                  ·
                    refine ⟨1754199167469155703588781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2338932223292207604785041 1754199167469155703588781)
                    ·
                      refine ⟨657824687800933388845793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1754199167469155703588781 657824687800933388845793)
                      ·
                        rfl

theorem cell23_1281109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 1, 2, 2, 3].length) (baseStart_1281109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1281109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1281109 prefixEnd_1281109 := by exact prefixLift 1281109
  have htrace : WordTrace (prefixWord ++ tailWord_1281109) baseStart_1281109 baseEnd_1281109 := by
    simpa [prefixWord, tailWord_1281109, baseEnd_1281109] using wordTrace_append hprefix tailTrace_1281109
  have hstable : (prefixWord ++ tailWord_1281109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281109).length < 2 ^ (prefixWord ++ tailWord_1281109).sum := by decide
  have hdescent : baseEnd_1281109 < baseStart_1281109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281116 : List Nat := [2, 2, 4, 1, 1, 1, 2, 5, 1, 4]
def baseStart_1281116 : Nat := 118140960795 + 1281116 * 2 ^ 59
def prefixEnd_1281116 : Nat := 4983230072969 + 3 ^ 40 * 1281116 * 2
def baseEnd_1281116 : Nat := 219276094055171620486087

theorem tailTrace_1281116 : CollatzResearch.WordTrace tailWord_1281116 prefixEnd_1281116 219276094055171620486087 := by
  unfold tailWord_1281116
  simp only [CollatzResearch.WordTrace]
  refine ⟨23363069613371502019287601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31150759484495336025716801 23363069613371502019287601)
  ·
    refine ⟨17522302210028626514465701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23363069613371502019287601 17522302210028626514465701)
    ·
      refine ⟨3285431664380367471462319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17522302210028626514465701 3285431664380367471462319)
      ·
        refine ⟨4928147496570551207193479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3285431664380367471462319 4928147496570551207193479)
        ·
          refine ⟨7392221244855826810790219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4928147496570551207193479 7392221244855826810790219)
          ·
            refine ⟨11088331867283740216185329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7392221244855826810790219 11088331867283740216185329)
            ·
              refine ⟨8316248900462805162138997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11088331867283740216185329 8316248900462805162138997)
              ·
                refine ⟨779648334418387983950531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8316248900462805162138997 779648334418387983950531)
                ·
                  refine ⟨1169472501627581975925797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 779648334418387983950531 1169472501627581975925797)
                  ·
                    refine ⟨219276094055171620486087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1169472501627581975925797 219276094055171620486087)
                    ·
                      rfl

theorem cell23_1281116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 5, 1, 4].length) (baseStart_1281116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1281116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1281116 prefixEnd_1281116 := by exact prefixLift 1281116
  have htrace : WordTrace (prefixWord ++ tailWord_1281116) baseStart_1281116 baseEnd_1281116 := by
    simpa [prefixWord, tailWord_1281116, baseEnd_1281116] using wordTrace_append hprefix tailTrace_1281116
  have hstable : (prefixWord ++ tailWord_1281116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281116).length < 2 ^ (prefixWord ++ tailWord_1281116).sum := by decide
  have hdescent : baseEnd_1281116 < baseStart_1281116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281133 : List Nat := [1, 5, 1, 1, 2, 2, 4, 2, 1, 4]
def baseStart_1281133 : Nat := 118140960795 + 1281133 * 2 ^ 59
def prefixEnd_1281133 : Nat := 4983230072969 + 3 ^ 40 * 1281133 * 2
def baseEnd_1281133 : Nat := 219279003778880431648561

theorem tailTrace_1281133 : CollatzResearch.WordTrace tailWord_1281133 prefixEnd_1281133 219279003778880431648561 := by
  unfold tailWord_1281133
  simp only [CollatzResearch.WordTrace]
  refine ⟨46726759267681415941944053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31151172845120943961296035 46726759267681415941944053)
  ·
    refine ⟨4380633681345132744557255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46726759267681415941944053 4380633681345132744557255)
    ·
      refine ⟨6570950522017699116835883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4380633681345132744557255 6570950522017699116835883)
      ·
        refine ⟨9856425783026548675253825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6570950522017699116835883 9856425783026548675253825)
        ·
          refine ⟨7392319337269911506440369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9856425783026548675253825 7392319337269911506440369)
          ·
            refine ⟨5544239502952433629830277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7392319337269911506440369 5544239502952433629830277)
            ·
              refine ⟨1039544906803581305593177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5544239502952433629830277 1039544906803581305593177)
              ·
                refine ⟨779658680102685979194883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1039544906803581305593177 779658680102685979194883)
                ·
                  refine ⟨1169488020154028968792325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 779658680102685979194883 1169488020154028968792325)
                  ·
                    refine ⟨219279003778880431648561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1169488020154028968792325 219279003778880431648561)
                    ·
                      rfl

theorem cell23_1281133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 4, 2, 1, 4].length) (baseStart_1281133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1281133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1281133 prefixEnd_1281133 := by exact prefixLift 1281133
  have htrace : WordTrace (prefixWord ++ tailWord_1281133) baseStart_1281133 baseEnd_1281133 := by
    simpa [prefixWord, tailWord_1281133, baseEnd_1281133] using wordTrace_append hprefix tailTrace_1281133
  have hstable : (prefixWord ++ tailWord_1281133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281133).length < 2 ^ (prefixWord ++ tailWord_1281133).sum := by decide
  have hdescent : baseEnd_1281133 < baseStart_1281133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281149 : List Nat := [1, 4, 1, 1, 3, 1, 2, 2, 1, 5, 2]
def baseStart_1281149 : Nat := 118140960795 + 1281149 * 2 ^ 59
def prefixEnd_1281149 : Nat := 4983230072969 + 3 ^ 40 * 1281149 * 2
def baseEnd_1281149 : Nat := 657845227027113232345609

theorem tailTrace_1281149 : CollatzResearch.WordTrace tailWord_1281149 prefixEnd_1281149 657845227027113232345609 := by
  unfold tailWord_1281149
  simp only [CollatzResearch.WordTrace]
  refine ⟨46727342835623450674526501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31151561890415633783017667 46727342835623450674526501)
  ·
    refine ⟨8761376781679397001473719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46727342835623450674526501 8761376781679397001473719)
    ·
      refine ⟨13142065172519095502210579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8761376781679397001473719 13142065172519095502210579)
      ·
        refine ⟨19713097758778643253315869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13142065172519095502210579 19713097758778643253315869)
        ·
          refine ⟨7392411659541991219993451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19713097758778643253315869 7392411659541991219993451)
          ·
            refine ⟨11088617489312986829990177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7392411659541991219993451 11088617489312986829990177)
            ·
              refine ⟨8316463116984740122492633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11088617489312986829990177 8316463116984740122492633)
              ·
                refine ⟨6237347337738555091869475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8316463116984740122492633 6237347337738555091869475)
                ·
                  refine ⟨9356021006607832637804213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6237347337738555091869475 9356021006607832637804213)
                  ·
                    refine ⟨877126969369484309794145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9356021006607832637804213 877126969369484309794145)
                    ·
                      refine ⟨657845227027113232345609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 877126969369484309794145 657845227027113232345609)
                      ·
                        rfl

theorem cell23_1281149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 2, 1, 5, 2].length) (baseStart_1281149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1281149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1281149 prefixEnd_1281149 := by exact prefixLift 1281149
  have htrace : WordTrace (prefixWord ++ tailWord_1281149) baseStart_1281149 baseEnd_1281149 := by
    simpa [prefixWord, tailWord_1281149, baseEnd_1281149] using wordTrace_append hprefix tailTrace_1281149
  have hstable : (prefixWord ++ tailWord_1281149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281149).length < 2 ^ (prefixWord ++ tailWord_1281149).sum := by decide
  have hdescent : baseEnd_1281149 < baseStart_1281149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281150 : List Nat := [4, 2, 4, 1, 1, 1, 1, 2, 3, 4]
def baseStart_1281150 : Nat := 118140960795 + 1281150 * 2 ^ 59
def prefixEnd_1281150 : Nat := 4983230072969 + 3 ^ 40 * 1281150 * 2
def baseEnd_1281150 : Nat := 219281913502589242811035

theorem tailTrace_1281150 : CollatzResearch.WordTrace tailWord_1281150 prefixEnd_1281150 219281913502589242811035 := by
  unfold tailWord_1281150
  simp only [CollatzResearch.WordTrace]
  refine ⟨5840922413577478480664113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31151586205746551896875269 5840922413577478480664113)
  ·
    refine ⟨4380691810183108860498085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5840922413577478480664113 4380691810183108860498085)
    ·
      refine ⟨821379714409332911343391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4380691810183108860498085 821379714409332911343391)
      ·
        refine ⟨1232069571613999367015087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 821379714409332911343391 1232069571613999367015087)
        ·
          refine ⟨1848104357420999050522631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1232069571613999367015087 1848104357420999050522631)
          ·
            refine ⟨2772156536131498575783947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1848104357420999050522631 2772156536131498575783947)
            ·
              refine ⟨4158234804197247863675921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2772156536131498575783947 4158234804197247863675921)
              ·
                refine ⟨3118676103147935897756941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4158234804197247863675921 3118676103147935897756941)
                ·
                  refine ⟨1169503538680475961658853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3118676103147935897756941 1169503538680475961658853)
                  ·
                    refine ⟨219281913502589242811035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1169503538680475961658853 219281913502589242811035)
                    ·
                      rfl

theorem cell23_1281150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_1281150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1281150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1281150 prefixEnd_1281150 := by exact prefixLift 1281150
  have htrace : WordTrace (prefixWord ++ tailWord_1281150) baseStart_1281150 baseEnd_1281150 := by
    simpa [prefixWord, tailWord_1281150, baseEnd_1281150] using wordTrace_append hprefix tailTrace_1281150
  have hstable : (prefixWord ++ tailWord_1281150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281150).length < 2 ^ (prefixWord ++ tailWord_1281150).sum := by decide
  have hdescent : baseEnd_1281150 < baseStart_1281150 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281156 : List Nat := [2, 3, 2, 1, 2, 3, 1, 2, 3, 1, 3]
def baseStart_1281156 : Nat := 118140960795 + 1281156 * 2 ^ 59
def prefixEnd_1281156 : Nat := 4983230072969 + 3 ^ 40 * 1281156 * 2
def baseEnd_1281156 : Nat := 657848821391694704958077

theorem tailTrace_1281156 : CollatzResearch.WordTrace tailWord_1281156 prefixEnd_1281156 657848821391694704958077 := by
  unfold tailWord_1281156
  simp only [CollatzResearch.WordTrace]
  refine ⟨23363799073299045435015661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31151732097732060580020881 23363799073299045435015661)
  ·
    refine ⟨8761424652487142038130873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23363799073299045435015661 8761424652487142038130873)
    ·
      refine ⟨6571068489365356528598155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8761424652487142038130873 6571068489365356528598155)
      ·
        refine ⟨9856602734048034792897233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6571068489365356528598155 9856602734048034792897233)
        ·
          refine ⟨7392452050536026094672925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9856602734048034792897233 7392452050536026094672925)
          ·
            refine ⟨2772169518951009785502347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7392452050536026094672925 2772169518951009785502347)
            ·
              refine ⟨4158254278426514678253521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2772169518951009785502347 4158254278426514678253521)
              ·
                refine ⟨3118690708819886008690141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4158254278426514678253521 3118690708819886008690141)
                ·
                  refine ⟨1169509015807457253258803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3118690708819886008690141 1169509015807457253258803)
                  ·
                    refine ⟨1754263523711185879888205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1169509015807457253258803 1754263523711185879888205)
                    ·
                      refine ⟨657848821391694704958077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1754263523711185879888205 657848821391694704958077)
                      ·
                        rfl

theorem cell23_1281156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 2, 3, 1, 3].length) (baseStart_1281156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1281156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1281156 prefixEnd_1281156 := by exact prefixLift 1281156
  have htrace : WordTrace (prefixWord ++ tailWord_1281156) baseStart_1281156 baseEnd_1281156 := by
    simpa [prefixWord, tailWord_1281156, baseEnd_1281156] using wordTrace_append hprefix tailTrace_1281156
  have hstable : (prefixWord ++ tailWord_1281156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281156).length < 2 ^ (prefixWord ++ tailWord_1281156).sum := by decide
  have hdescent : baseEnd_1281156 < baseStart_1281156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281166 : List Nat := [4, 1, 1, 3, 2, 2, 1, 1, 1, 5, 2]
def baseStart_1281166 : Nat := 118140960795 + 1281166 * 2 ^ 59
def prefixEnd_1281166 : Nat := 4983230072969 + 3 ^ 40 * 1281166 * 2
def baseEnd_1281166 : Nat := 657853956198239665833031

theorem tailTrace_1281166 : CollatzResearch.WordTrace tailWord_1281166 prefixEnd_1281166 657853956198239665833031 := by
  unfold tailWord_1281166
  simp only [CollatzResearch.WordTrace]
  refine ⟨5840995359570232822236919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31151975251041241718596901 5840995359570232822236919)
  ·
    refine ⟨8761493039355349233355379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5840995359570232822236919 8761493039355349233355379)
    ·
      refine ⟨13142239559033023850033069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8761493039355349233355379 13142239559033023850033069)
      ·
        refine ⟨4928339834637383943762401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13142239559033023850033069 4928339834637383943762401)
        ·
          refine ⟨3696254875978037957821801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4928339834637383943762401 3696254875978037957821801)
          ·
            refine ⟨2772191156983528468366351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3696254875978037957821801 2772191156983528468366351)
            ·
              refine ⟨4158286735475292702549527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2772191156983528468366351 4158286735475292702549527)
              ·
                refine ⟨6237430103212939053824291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4158286735475292702549527 6237430103212939053824291)
                ·
                  refine ⟨9356145154819408580736437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6237430103212939053824291 9356145154819408580736437)
                  ·
                    refine ⟨877138608264319554444041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9356145154819408580736437 877138608264319554444041)
                    ·
                      refine ⟨657853956198239665833031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 877138608264319554444041 657853956198239665833031)
                      ·
                        rfl

theorem cell23_1281166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 1, 1, 5, 2].length) (baseStart_1281166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1281166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1281166 prefixEnd_1281166 := by exact prefixLift 1281166
  have htrace : WordTrace (prefixWord ++ tailWord_1281166) baseStart_1281166 baseEnd_1281166 := by
    simpa [prefixWord, tailWord_1281166, baseEnd_1281166] using wordTrace_append hprefix tailTrace_1281166
  have hstable : (prefixWord ++ tailWord_1281166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281166).length < 2 ^ (prefixWord ++ tailWord_1281166).sum := by decide
  have hdescent : baseEnd_1281166 < baseStart_1281166 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281176 : List Nat := [2, 1, 2, 4, 2, 1, 4, 1, 1, 5]
def baseStart_1281176 : Nat := 118140960795 + 1281176 * 2 ^ 59
def prefixEnd_1281176 : Nat := 4983230072969 + 3 ^ 40 * 1281176 * 2
def baseEnd_1281176 : Nat := 219286363668261542235995

theorem tailTrace_1281176 : CollatzResearch.WordTrace tailWord_1281176 prefixEnd_1281176 219286363668261542235995 := by
  unfold tailWord_1281176
  simp only [CollatzResearch.WordTrace]
  refine ⟨23364163803262817142879691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31152218404350422857172921 23364163803262817142879691)
  ·
    refine ⟨35046245704894225714319537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23364163803262817142879691 35046245704894225714319537)
    ·
      refine ⟨26284684278670669285739653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35046245704894225714319537 26284684278670669285739653)
      ·
        refine ⟨4928378302250750491076185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26284684278670669285739653 4928378302250750491076185)
        ·
          refine ⟨3696283726688062868307139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4928378302250750491076185 3696283726688062868307139)
          ·
            refine ⟨5544425590032094302460709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3696283726688062868307139 5544425590032094302460709)
            ·
              refine ⟨1039579798131017681711383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5544425590032094302460709 1039579798131017681711383)
              ·
                refine ⟨1559369697196526522567075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1039579798131017681711383 1559369697196526522567075)
                ·
                  refine ⟨2339054545794789783850613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1559369697196526522567075 2339054545794789783850613)
                  ·
                    refine ⟨219286363668261542235995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2339054545794789783850613 219286363668261542235995)
                    ·
                      rfl

theorem cell23_1281176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 4, 1, 1, 5].length) (baseStart_1281176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1281176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1281176 prefixEnd_1281176 := by exact prefixLift 1281176
  have htrace : WordTrace (prefixWord ++ tailWord_1281176) baseStart_1281176 baseEnd_1281176 := by
    simpa [prefixWord, tailWord_1281176, baseEnd_1281176] using wordTrace_append hprefix tailTrace_1281176
  have hstable : (prefixWord ++ tailWord_1281176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281176).length < 2 ^ (prefixWord ++ tailWord_1281176).sum := by decide
  have hdescent : baseEnd_1281176 < baseStart_1281176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281189 : List Nat := [1, 3, 1, 2, 1, 5, 1, 1, 4, 4]
def baseStart_1281189 : Nat := 118140960795 + 1281189 * 2 ^ 59
def prefixEnd_1281189 : Nat := 4983230072969 + 3 ^ 40 * 1281189 * 2
def baseEnd_1281189 : Nat := 219288588751097691948475

theorem tailTrace_1281189 : CollatzResearch.WordTrace tailWord_1281189 prefixEnd_1281189 219288588751097691948475 := by
  unfold tailWord_1281189
  simp only [CollatzResearch.WordTrace]
  refine ⟨46728801755478537505982621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31152534503652358337321747 46728801755478537505982621)
  ·
    refine ⟨17523300658304451564743483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46728801755478537505982621 17523300658304451564743483)
    ·
      refine ⟨26284950987456677347115225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17523300658304451564743483 26284950987456677347115225)
      ·
        refine ⟨19713713240592508010336419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26284950987456677347115225 19713713240592508010336419)
        ·
          refine ⟨29570569860888762015504629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19713713240592508010336419 29570569860888762015504629)
          ·
            refine ⟨2772240924458321438953559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29570569860888762015504629 2772240924458321438953559)
            ·
              refine ⟨4158361386687482158430339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2772240924458321438953559 4158361386687482158430339)
              ·
                refine ⟨6237542080031223237645509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4158361386687482158430339 6237542080031223237645509)
                ·
                  refine ⟨1169539140005854357058533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6237542080031223237645509 1169539140005854357058533)
                  ·
                    refine ⟨219288588751097691948475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1169539140005854357058533 219288588751097691948475)
                    ·
                      rfl

theorem cell23_1281189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 1, 4, 4].length) (baseStart_1281189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1281189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1281189 prefixEnd_1281189 := by exact prefixLift 1281189
  have htrace : WordTrace (prefixWord ++ tailWord_1281189) baseStart_1281189 baseEnd_1281189 := by
    simpa [prefixWord, tailWord_1281189, baseEnd_1281189] using wordTrace_append hprefix tailTrace_1281189
  have hstable : (prefixWord ++ tailWord_1281189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281189).length < 2 ^ (prefixWord ++ tailWord_1281189).sum := by decide
  have hdescent : baseEnd_1281189 < baseStart_1281189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281209 : List Nat := [1, 2, 1, 4, 1, 3, 3, 1, 1, 2, 4]
def baseStart_1281209 : Nat := 118140960795 + 1281209 * 2 ^ 59
def prefixEnd_1281209 : Nat := 4983230072969 + 3 ^ 40 * 1281209 * 2
def baseEnd_1281209 : Nat := 657876035866382997595333

theorem tailTrace_1281209 : CollatzResearch.WordTrace tailWord_1281209 prefixEnd_1281209 657876035866382997595333 := by
  unfold tailWord_1281209
  simp only [CollatzResearch.WordTrace]
  refine ⟨46729531215406080921710681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31153020810270720614473787 46729531215406080921710681)
  ·
    refine ⟨35047148411554560691283011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46729531215406080921710681 35047148411554560691283011)
    ·
      refine ⟨52570722617331841036924517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35047148411554560691283011 52570722617331841036924517)
      ·
        refine ⟨9857010490749720194423347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52570722617331841036924517 9857010490749720194423347)
        ·
          refine ⟨14785515736124580291635021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9857010490749720194423347 14785515736124580291635021)
          ·
            refine ⟨5544568401046717609363133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14785515736124580291635021 5544568401046717609363133)
            ·
              refine ⟨2079213150392519103511175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5544568401046717609363133 2079213150392519103511175)
              ·
                refine ⟨3118819725588778655266763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2079213150392519103511175 3118819725588778655266763)
                ·
                  refine ⟨4678229588383167982900145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3118819725588778655266763 4678229588383167982900145)
                  ·
                    refine ⟨3508672191287375987175109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4678229588383167982900145 3508672191287375987175109)
                    ·
                      refine ⟨657876035866382997595333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3508672191287375987175109 657876035866382997595333)
                      ·
                        rfl

theorem cell23_1281209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 1, 1, 2, 4].length) (baseStart_1281209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1281209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1281209 prefixEnd_1281209 := by exact prefixLift 1281209
  have htrace : WordTrace (prefixWord ++ tailWord_1281209) baseStart_1281209 baseEnd_1281209 := by
    simpa [prefixWord, tailWord_1281209, baseEnd_1281209] using wordTrace_append hprefix tailTrace_1281209
  have hstable : (prefixWord ++ tailWord_1281209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281209).length < 2 ^ (prefixWord ++ tailWord_1281209).sum := by decide
  have hdescent : baseEnd_1281209 < baseStart_1281209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281236 : List Nat := [2, 4, 1, 4, 1, 2, 9]
def baseStart_1281236 : Nat := 118140960795 + 1281236 * 2 ^ 59
def prefixEnd_1281236 : Nat := 4983230072969 + 3 ^ 40 * 1281236 * 2
def baseEnd_1281236 : Nat := 8122097528938943110589

theorem tailTrace_1281236 : CollatzResearch.WordTrace tailWord_1281236 prefixEnd_1281236 8122097528938943110589 := by
  unfold tailWord_1281236
  simp only [CollatzResearch.WordTrace]
  refine ⟨23365257993154132266471781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31153677324205509688629041 23365257993154132266471781)
  ·
    refine ⟨4380985873716399799963459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23365257993154132266471781 4380985873716399799963459)
    ·
      refine ⟨6571478810574599699945189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4380985873716399799963459 6571478810574599699945189)
      ·
        refine ⟨1232152276982737443739723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6571478810574599699945189 1232152276982737443739723)
        ·
          refine ⟨1848228415474106165609585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1232152276982737443739723 1848228415474106165609585)
          ·
            refine ⟨1386171311605579624207189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1848228415474106165609585 1386171311605579624207189)
            ·
              refine ⟨8122097528938943110589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1386171311605579624207189 8122097528938943110589)
              ·
                rfl

theorem cell23_1281236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 9].length) (baseStart_1281236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1281236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1281236 prefixEnd_1281236 := by exact prefixLift 1281236
  have htrace : WordTrace (prefixWord ++ tailWord_1281236) baseStart_1281236 baseEnd_1281236 := by
    simpa [prefixWord, tailWord_1281236, baseEnd_1281236] using wordTrace_append hprefix tailTrace_1281236
  have hstable : (prefixWord ++ tailWord_1281236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281236).length < 2 ^ (prefixWord ++ tailWord_1281236).sum := by decide
  have hdescent : baseEnd_1281236 < baseStart_1281236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281242 : List Nat := [3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 5]
def baseStart_1281242 : Nat := 118140960795 + 1281242 * 2 ^ 59
def prefixEnd_1281242 : Nat := 4983230072969 + 3 ^ 40 * 1281242 * 2
def baseEnd_1281242 : Nat := 657892980727981368482681

theorem tailTrace_1281242 : CollatzResearch.WordTrace tailWord_1281242 prefixEnd_1281242 657892980727981368482681 := by
  unfold tailWord_1281242
  simp only [CollatzResearch.WordTrace]
  refine ⟨11682683706071631889415495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31153823216191018371774653 11682683706071631889415495)
  ·
    refine ⟨17524025559107447834123243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11682683706071631889415495 17524025559107447834123243)
    ·
      refine ⟨26286038338661171751184865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17524025559107447834123243 26286038338661171751184865)
      ·
        refine ⟨19714528753995878813388649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26286038338661171751184865 19714528753995878813388649)
        ·
          refine ⟨14785896565496909110041487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19714528753995878813388649 14785896565496909110041487)
          ·
            refine ⟨22178844848245363665062231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14785896565496909110041487 22178844848245363665062231)
            ·
              refine ⟨33268267272368045497593347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22178844848245363665062231 33268267272368045497593347)
              ·
                refine ⟨49902400908552068246390021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33268267272368045497593347 49902400908552068246390021)
                ·
                  refine ⟨9356700170353512796198129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49902400908552068246390021 9356700170353512796198129)
                  ·
                    refine ⟨7017525127765134597148597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9356700170353512796198129 7017525127765134597148597)
                    ·
                      refine ⟨657892980727981368482681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7017525127765134597148597 657892980727981368482681)
                      ·
                        rfl

theorem cell23_1281242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 5].length) (baseStart_1281242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1281242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1281242 prefixEnd_1281242 := by exact prefixLift 1281242
  have htrace : WordTrace (prefixWord ++ tailWord_1281242) baseStart_1281242 baseEnd_1281242 := by
    simpa [prefixWord, tailWord_1281242, baseEnd_1281242] using wordTrace_append hprefix tailTrace_1281242
  have hstable : (prefixWord ++ tailWord_1281242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281242).length < 2 ^ (prefixWord ++ tailWord_1281242).sum := by decide
  have hdescent : baseEnd_1281242 < baseStart_1281242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281256 : List Nat := [2, 1, 4, 1, 2, 1, 2, 2, 3, 3, 2]
def baseStart_1281256 : Nat := 118140960795 + 1281256 * 2 ^ 59
def prefixEnd_1281256 : Nat := 4983230072969 + 3 ^ 40 * 1281256 * 2
def baseEnd_1281256 : Nat := 657900169457144313707617

theorem tailTrace_1281256 : CollatzResearch.WordTrace tailWord_1281256 prefixEnd_1281256 657900169457144313707617 := by
  unfold tailWord_1281256
  simp only [CollatzResearch.WordTrace]
  refine ⟨23365622723117903974335811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31154163630823871965781081 23365622723117903974335811)
  ·
    refine ⟨35048434084676855961503717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23365622723117903974335811 35048434084676855961503717)
    ·
      refine ⟨6571581390876910492781947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35048434084676855961503717 6571581390876910492781947)
      ·
        refine ⟨9857372086315365739172921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6571581390876910492781947 9857372086315365739172921)
        ·
          refine ⟨7393029064736524304379691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9857372086315365739172921 7393029064736524304379691)
          ·
            refine ⟨11089543597104786456569537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7393029064736524304379691 11089543597104786456569537)
            ·
              refine ⟨8317157697828589842427153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11089543597104786456569537 8317157697828589842427153)
              ·
                refine ⟨6237868273371442381820365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8317157697828589842427153 6237868273371442381820365)
                ·
                  refine ⟨2339200602514290893182637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6237868273371442381820365 2339200602514290893182637)
                  ·
                    refine ⟨877200225942859084943489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2339200602514290893182637 877200225942859084943489)
                    ·
                      refine ⟨657900169457144313707617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 877200225942859084943489 657900169457144313707617)
                      ·
                        rfl

theorem cell23_1281256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 2, 3, 3, 2].length) (baseStart_1281256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1281256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1281256 prefixEnd_1281256 := by exact prefixLift 1281256
  have htrace : WordTrace (prefixWord ++ tailWord_1281256) baseStart_1281256 baseEnd_1281256 := by
    simpa [prefixWord, tailWord_1281256, baseEnd_1281256] using wordTrace_append hprefix tailTrace_1281256
  have hstable : (prefixWord ++ tailWord_1281256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281256).length < 2 ^ (prefixWord ++ tailWord_1281256).sum := by decide
  have hdescent : baseEnd_1281256 < baseStart_1281256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281263 : List Nat := [1, 1, 2, 1, 7, 1, 1, 3, 2, 1, 3]
def baseStart_1281263 : Nat := 118140960795 + 1281263 * 2 ^ 59
def prefixEnd_1281263 : Nat := 4983230072969 + 3 ^ 40 * 1281263 * 2
def baseEnd_1281263 : Nat := 657903763821725786320085

theorem tailTrace_1281263 : CollatzResearch.WordTrace tailWord_1281263 prefixEnd_1281263 657903763821725786320085 := by
  unfold tailWord_1281263
  simp only [CollatzResearch.WordTrace]
  refine ⟨46731500757210448144176443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31154333838140298762784295 46731500757210448144176443)
  ·
    refine ⟨70097251135815672216264665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46731500757210448144176443 70097251135815672216264665)
    ·
      refine ⟨52572938351861754162198499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70097251135815672216264665 52572938351861754162198499)
      ·
        refine ⟨78859407527792631243297749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52572938351861754162198499 78859407527792631243297749)
        ·
          refine ⟨1848267363932639794764791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 78859407527792631243297749 1848267363932639794764791)
          ·
            refine ⟨2772401045898959692147187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1848267363932639794764791 2772401045898959692147187)
            ·
              refine ⟨4158601568848439538220781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2772401045898959692147187 4158601568848439538220781)
              ·
                refine ⟨1559475588318164826832793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4158601568848439538220781 1559475588318164826832793)
                ·
                  refine ⟨1169606691238623620124595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1559475588318164826832793 1169606691238623620124595)
                  ·
                    refine ⟨1754410036857935430186893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1169606691238623620124595 1754410036857935430186893)
                    ·
                      refine ⟨657903763821725786320085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1754410036857935430186893 657903763821725786320085)
                      ·
                        rfl

theorem cell23_1281263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 3, 2, 1, 3].length) (baseStart_1281263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1281263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1281263 prefixEnd_1281263 := by exact prefixLift 1281263
  have htrace : WordTrace (prefixWord ++ tailWord_1281263) baseStart_1281263 baseEnd_1281263 := by
    simpa [prefixWord, tailWord_1281263, baseEnd_1281263] using wordTrace_append hprefix tailTrace_1281263
  have hstable : (prefixWord ++ tailWord_1281263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281263).length < 2 ^ (prefixWord ++ tailWord_1281263).sum := by decide
  have hdescent : baseEnd_1281263 < baseStart_1281263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281298 : List Nat := [3, 2, 4, 2, 2, 1, 2, 2, 1, 2, 2]
def baseStart_1281298 : Nat := 118140960795 + 1281298 * 2 ^ 59
def prefixEnd_1281298 : Nat := 4983230072969 + 3 ^ 40 * 1281298 * 2
def baseEnd_1281298 : Nat := 657921735644633149382425

theorem tailTrace_1281298 : CollatzResearch.WordTrace tailWord_1281298 prefixEnd_1281298 657921735644633149382425 := by
  unfold tailWord_1281298
  simp only [CollatzResearch.WordTrace]
  refine ⟨11683194328020912280425137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31155184874722432747800365 11683194328020912280425137)
  ·
    refine ⟨8762395746015684210318853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11683194328020912280425137 8762395746015684210318853)
    ·
      refine ⟨1642949202377940789434785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8762395746015684210318853 1642949202377940789434785)
      ·
        refine ⟨1232211901783455592076089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1642949202377940789434785 1232211901783455592076089)
        ·
          refine ⟨924158926337591694057067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1232211901783455592076089 924158926337591694057067)
          ·
            refine ⟨1386238389506387541085601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 924158926337591694057067 1386238389506387541085601)
            ·
              refine ⟨1039678792129790655814201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1386238389506387541085601 1039678792129790655814201)
              ·
                refine ⟨779759094097342991860651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1039678792129790655814201 779759094097342991860651)
                ·
                  refine ⟨1169638641146014487790977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 779759094097342991860651 1169638641146014487790977)
                  ·
                    refine ⟨877228980859510865843233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1169638641146014487790977 877228980859510865843233)
                    ·
                      refine ⟨657921735644633149382425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 877228980859510865843233 657921735644633149382425)
                      ·
                        rfl

theorem cell23_1281298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_1281298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1281298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1281298 prefixEnd_1281298 := by exact prefixLift 1281298
  have htrace : WordTrace (prefixWord ++ tailWord_1281298) baseStart_1281298 baseEnd_1281298 := by
    simpa [prefixWord, tailWord_1281298, baseEnd_1281298] using wordTrace_append hprefix tailTrace_1281298
  have hstable : (prefixWord ++ tailWord_1281298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281298).length < 2 ^ (prefixWord ++ tailWord_1281298).sum := by decide
  have hdescent : baseEnd_1281298 < baseStart_1281298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281320 : List Nat := [2, 1, 5, 1, 2, 1, 2, 3, 2, 2, 2]
def baseStart_1281320 : Nat := 118140960795 + 1281320 * 2 ^ 59
def prefixEnd_1281320 : Nat := 4983230072969 + 3 ^ 40 * 1281320 * 2
def baseEnd_1281320 : Nat := 657933032219032063307323

theorem tailTrace_1281320 : CollatzResearch.WordTrace tailWord_1281320 prefixEnd_1281320 657933032219032063307323 := by
  unfold tailWord_1281320
  simp only [CollatzResearch.WordTrace]
  refine ⟨23366789859001973439500707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31155719812002631252667609 23366789859001973439500707)
  ·
    refine ⟨35050184788502960159251061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23366789859001973439500707 35050184788502960159251061)
    ·
      refine ⟨3285954823922152514929787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35050184788502960159251061 3285954823922152514929787)
      ·
        refine ⟨4928932235883228772394681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3285954823922152514929787 4928932235883228772394681)
        ·
          refine ⟨3696699176912421579296011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4928932235883228772394681 3696699176912421579296011)
          ·
            refine ⟨5545048765368632368944017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3696699176912421579296011 5545048765368632368944017)
            ·
              refine ⟨4158786574026474276708013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5545048765368632368944017 4158786574026474276708013)
              ·
                refine ⟨1559544965259927853765505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4158786574026474276708013 1559544965259927853765505)
                ·
                  refine ⟨1169658723944945890324129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1559544965259927853765505 1169658723944945890324129)
                  ·
                    refine ⟨877244042958709417743097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1169658723944945890324129 877244042958709417743097)
                    ·
                      refine ⟨657933032219032063307323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 877244042958709417743097 657933032219032063307323)
                      ·
                        rfl

theorem cell23_1281320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 3, 2, 2, 2].length) (baseStart_1281320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1281320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1281320 prefixEnd_1281320 := by exact prefixLift 1281320
  have htrace : WordTrace (prefixWord ++ tailWord_1281320) baseStart_1281320 baseEnd_1281320 := by
    simpa [prefixWord, tailWord_1281320, baseEnd_1281320] using wordTrace_append hprefix tailTrace_1281320
  have hstable : (prefixWord ++ tailWord_1281320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281320).length < 2 ^ (prefixWord ++ tailWord_1281320).sum := by decide
  have hdescent : baseEnd_1281320 < baseStart_1281320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281410 : List Nat := [3, 4, 2, 1, 1, 2, 1, 2, 2, 1, 4]
def baseStart_1281410 : Nat := 118140960795 + 1281410 * 2 ^ 59
def prefixEnd_1281410 : Nat := 4983230072969 + 3 ^ 40 * 1281410 * 2
def baseEnd_1281410 : Nat := 657979245477936711181909

theorem tailTrace_1281410 : CollatzResearch.WordTrace tailWord_1281410 prefixEnd_1281410 657979245477936711181909 := by
  unfold tailWord_1281410
  simp only [CollatzResearch.WordTrace]
  refine ⟨11684215571919473062444421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31157908191785261499851789 11684215571919473062444421)
  ·
    refine ⟨2190790419734901199208329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11684215571919473062444421 2190790419734901199208329)
    ·
      refine ⟨1643092814801175899406247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2190790419734901199208329 1643092814801175899406247)
      ·
        refine ⟨2464639222201763849109371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1643092814801175899406247 2464639222201763849109371)
        ·
          refine ⟨3696958833302645773664057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2464639222201763849109371 3696958833302645773664057)
          ·
            refine ⟨2772719124976984330248043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3696958833302645773664057 2772719124976984330248043)
            ·
              refine ⟨4159078687465476495372065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2772719124976984330248043 4159078687465476495372065)
              ·
                refine ⟨3119309015599107371529049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4159078687465476495372065 3119309015599107371529049)
                ·
                  refine ⟨2339481761699330528646787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3119309015599107371529049 2339481761699330528646787)
                  ·
                    refine ⟨3509222642548995792970181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2339481761699330528646787 3509222642548995792970181)
                    ·
                      refine ⟨657979245477936711181909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3509222642548995792970181 657979245477936711181909)
                      ·
                        rfl

theorem cell23_1281410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_1281410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1281410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1281410 prefixEnd_1281410 := by exact prefixLift 1281410
  have htrace : WordTrace (prefixWord ++ tailWord_1281410) baseStart_1281410 baseEnd_1281410 := by
    simpa [prefixWord, tailWord_1281410, baseEnd_1281410] using wordTrace_append hprefix tailTrace_1281410
  have hstable : (prefixWord ++ tailWord_1281410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281410).length < 2 ^ (prefixWord ++ tailWord_1281410).sum := by decide
  have hdescent : baseEnd_1281410 < baseStart_1281410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281420 : List Nat := [2, 2, 1, 2, 1, 3, 5, 2, 1, 4]
def baseStart_1281420 : Nat := 118140960795 + 1281420 * 2 ^ 59
def prefixEnd_1281420 : Nat := 4983230072969 + 3 ^ 40 * 1281420 * 2
def baseEnd_1281420 : Nat := 219328126761493890685621

theorem tailTrace_1281420 : CollatzResearch.WordTrace tailWord_1281420 prefixEnd_1281420 219328126761493890685621 := by
  unfold tailWord_1281420
  simp only [CollatzResearch.WordTrace]
  refine ⟨23368613508820831978820857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31158151345094442638427809 23368613508820831978820857)
  ·
    refine ⟨17526460131615623984115643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23368613508820831978820857 17526460131615623984115643)
    ·
      refine ⟨26289690197423435976173465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17526460131615623984115643 26289690197423435976173465)
      ·
        refine ⟨19717267648067576982130099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26289690197423435976173465 19717267648067576982130099)
        ·
          refine ⟨29575901472101365473195149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19717267648067576982130099 29575901472101365473195149)
          ·
            refine ⟨11090963052038012052448181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29575901472101365473195149 11090963052038012052448181)
            ·
              refine ⟨1039777786128563629917017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11090963052038012052448181 1039777786128563629917017)
              ·
                refine ⟨779833339596422722437763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1039777786128563629917017 779833339596422722437763)
                ·
                  refine ⟨1169750009394634083656645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 779833339596422722437763 1169750009394634083656645)
                  ·
                    refine ⟨219328126761493890685621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1169750009394634083656645 219328126761493890685621)
                    ·
                      rfl

theorem cell23_1281420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 5, 2, 1, 4].length) (baseStart_1281420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1281420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1281420 prefixEnd_1281420 := by exact prefixLift 1281420
  have htrace : WordTrace (prefixWord ++ tailWord_1281420) baseStart_1281420 baseEnd_1281420 := by
    simpa [prefixWord, tailWord_1281420, baseEnd_1281420] using wordTrace_append hprefix tailTrace_1281420
  have hstable : (prefixWord ++ tailWord_1281420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281420).length < 2 ^ (prefixWord ++ tailWord_1281420).sum := by decide
  have hdescent : baseEnd_1281420 < baseStart_1281420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281433 : List Nat := [1, 2, 1, 2, 1, 7, 2, 1, 6]
def baseStart_1281433 : Nat := 118140960795 + 1281433 * 2 ^ 59
def prefixEnd_1281433 : Nat := 4983230072969 + 3 ^ 40 * 1281433 * 2
def baseEnd_1281433 : Nat := 73110117281443346799367

theorem tailTrace_1281433 : CollatzResearch.WordTrace tailWord_1281433 prefixEnd_1281433 73110117281443346799367 := by
  unfold tailWord_1281433
  simp only [CollatzResearch.WordTrace]
  refine ⟨46737701166594567177864953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31158467444396378118576635 46737701166594567177864953)
  ·
    refine ⟨35053275874945925383398715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46737701166594567177864953 35053275874945925383398715)
    ·
      refine ⟨52579913812418888075098073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35053275874945925383398715 52579913812418888075098073)
      ·
        refine ⟨39434935359314166056323555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52579913812418888075098073 39434935359314166056323555)
        ·
          refine ⟨59152403038971249084485333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39434935359314166056323555 59152403038971249084485333)
          ·
            refine ⟨1386384446225888650417625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 59152403038971249084485333 1386384446225888650417625)
            ·
              refine ⟨1039788334669416487813219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1386384446225888650417625 1039788334669416487813219)
              ·
                refine ⟨1559682502004124731719829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1039788334669416487813219 1559682502004124731719829)
                ·
                  refine ⟨73110117281443346799367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1559682502004124731719829 73110117281443346799367)
                  ·
                    rfl

theorem cell23_1281433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 2, 1, 6].length) (baseStart_1281433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1281433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1281433 prefixEnd_1281433 := by exact prefixLift 1281433
  have htrace : WordTrace (prefixWord ++ tailWord_1281433) baseStart_1281433 baseEnd_1281433 := by
    simpa [prefixWord, tailWord_1281433, baseEnd_1281433] using wordTrace_append hprefix tailTrace_1281433
  have hstable : (prefixWord ++ tailWord_1281433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281433).length < 2 ^ (prefixWord ++ tailWord_1281433).sum := by decide
  have hdescent : baseEnd_1281433 < baseStart_1281433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281463 : List Nat := [1, 1, 3, 1, 3, 2, 5, 1, 1, 5]
def baseStart_1281463 : Nat := 118140960795 + 1281463 * 2 ^ 59
def prefixEnd_1281463 : Nat := 4983230072969 + 3 ^ 40 * 1281463 * 2
def baseEnd_1281463 : Nat := 219335486650875001273055

theorem tailTrace_1281463 : CollatzResearch.WordTrace tailWord_1281463 prefixEnd_1281463 219335486650875001273055 := by
  unfold tailWord_1281463
  simp only [CollatzResearch.WordTrace]
  refine ⟨46738795356485882301457043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31159196904323921534304695 46738795356485882301457043)
  ·
    refine ⟨70108193034728823452185565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46738795356485882301457043 70108193034728823452185565)
    ·
      refine ⟨26290572388023308794569587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70108193034728823452185565 26290572388023308794569587)
      ·
        refine ⟨39435858582034963191854381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26290572388023308794569587 39435858582034963191854381)
        ·
          refine ⟨14788446968263111196945393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39435858582034963191854381 14788446968263111196945393)
          ·
            refine ⟨11091335226197333397709045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14788446968263111196945393 11091335226197333397709045)
            ·
              refine ⟨1039812677456000006035223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11091335226197333397709045 1039812677456000006035223)
              ·
                refine ⟨1559719016184000009052835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1039812677456000006035223 1559719016184000009052835)
                ·
                  refine ⟨2339578524276000013579253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1559719016184000009052835 2339578524276000013579253)
                  ·
                    refine ⟨219335486650875001273055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2339578524276000013579253 219335486650875001273055)
                    ·
                      rfl

theorem cell23_1281463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 5, 1, 1, 5].length) (baseStart_1281463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1281463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1281463 prefixEnd_1281463 := by exact prefixLift 1281463
  have htrace : WordTrace (prefixWord ++ tailWord_1281463) baseStart_1281463 baseEnd_1281463 := by
    simpa [prefixWord, tailWord_1281463, baseEnd_1281463] using wordTrace_append hprefix tailTrace_1281463
  have hstable : (prefixWord ++ tailWord_1281463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281463).length < 2 ^ (prefixWord ++ tailWord_1281463).sum := by decide
  have hdescent : baseEnd_1281463 < baseStart_1281463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281486 : List Nat := [4, 1, 1, 1, 2, 1, 2, 4, 1, 1, 5]
def baseStart_1281486 : Nat := 118140960795 + 1281486 * 2 ^ 59
def prefixEnd_1281486 : Nat := 4983230072969 + 3 ^ 40 * 1281486 * 2
def baseEnd_1281486 : Nat := 658018270007678413831559

theorem tailTrace_1281486 : CollatzResearch.WordTrace tailWord_1281486 prefixEnd_1281486 658018270007678413831559 := by
  unfold tailWord_1281486
  simp only [CollatzResearch.WordTrace]
  refine ⟨5842454279425319653693039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31159756156935038153029541 5842454279425319653693039)
  ·
    refine ⟨8763681419137979480539559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5842454279425319653693039 8763681419137979480539559)
    ·
      refine ⟨13145522128706969220809339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8763681419137979480539559 13145522128706969220809339)
      ·
        refine ⟨19718283193060453831214009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13145522128706969220809339 19718283193060453831214009)
        ·
          refine ⟨14788712394795340373410507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19718283193060453831214009 14788712394795340373410507)
          ·
            refine ⟨22183068592193010560115761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14788712394795340373410507 22183068592193010560115761)
            ·
              refine ⟨16637301444144757920086821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22183068592193010560115761 16637301444144757920086821)
              ·
                refine ⟨3119494020777142110016279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16637301444144757920086821 3119494020777142110016279)
                ·
                  refine ⟨4679241031165713165024419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3119494020777142110016279 4679241031165713165024419)
                  ·
                    refine ⟨7018861546748569747536629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4679241031165713165024419 7018861546748569747536629)
                    ·
                      refine ⟨658018270007678413831559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7018861546748569747536629 658018270007678413831559)
                      ·
                        rfl

theorem cell23_1281486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 4, 1, 1, 5].length) (baseStart_1281486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1281486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1281486 prefixEnd_1281486 := by exact prefixLift 1281486
  have htrace : WordTrace (prefixWord ++ tailWord_1281486) baseStart_1281486 baseEnd_1281486 := by
    simpa [prefixWord, tailWord_1281486, baseEnd_1281486] using wordTrace_append hprefix tailTrace_1281486
  have hstable : (prefixWord ++ tailWord_1281486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281486).length < 2 ^ (prefixWord ++ tailWord_1281486).sum := by decide
  have hdescent : baseEnd_1281486 < baseStart_1281486 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281493 : List Nat := [1, 3, 2, 3, 1, 1, 1, 5, 2, 4]
def baseStart_1281493 : Nat := 118140960795 + 1281493 * 2 ^ 59
def prefixEnd_1281493 : Nat := 4983230072969 + 3 ^ 40 * 1281493 * 2
def baseEnd_1281493 : Nat := 219340621457419962148009

theorem tailTrace_1281493 : CollatzResearch.WordTrace tailWord_1281493 prefixEnd_1281493 219340621457419962148009 := by
  unfold tailWord_1281493
  simp only [CollatzResearch.WordTrace]
  refine ⟨46739889546377197425049133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31159926364251464950032755 46739889546377197425049133)
  ·
    refine ⟨17527458579891449034393425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46739889546377197425049133 17527458579891449034393425)
    ·
      refine ⟨13145593934918586775795069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17527458579891449034393425 13145593934918586775795069)
      ·
        refine ⟨4929597725594470040923151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13145593934918586775795069 4929597725594470040923151)
        ·
          refine ⟨7394396588391705061384727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4929597725594470040923151 7394396588391705061384727)
          ·
            refine ⟨11091594882587557592077091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7394396588391705061384727 11091594882587557592077091)
            ·
              refine ⟨16637392323881336388115637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11091594882587557592077091 16637392323881336388115637)
              ·
                refine ⟨1559755530363875286385841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16637392323881336388115637 1559755530363875286385841)
                ·
                  refine ⟨1169816647772906464789381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1559755530363875286385841 1169816647772906464789381)
                  ·
                    refine ⟨219340621457419962148009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1169816647772906464789381 219340621457419962148009)
                    ·
                      rfl

theorem cell23_1281493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 5, 2, 4].length) (baseStart_1281493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1281493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1281493 prefixEnd_1281493 := by exact prefixLift 1281493
  have htrace : WordTrace (prefixWord ++ tailWord_1281493) baseStart_1281493 baseEnd_1281493 := by
    simpa [prefixWord, tailWord_1281493, baseEnd_1281493] using wordTrace_append hprefix tailTrace_1281493
  have hstable : (prefixWord ++ tailWord_1281493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281493).length < 2 ^ (prefixWord ++ tailWord_1281493).sum := by decide
  have hdescent : baseEnd_1281493 < baseStart_1281493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281496 : List Nat := [2, 1, 2, 2, 2, 1, 3, 3, 1, 2, 4]
def baseStart_1281496 : Nat := 118140960795 + 1281496 * 2 ^ 59
def prefixEnd_1281496 : Nat := 4983230072969 + 3 ^ 40 * 1281496 * 2
def baseEnd_1281496 : Nat := 658023404814223374706513

theorem tailTrace_1281496 : CollatzResearch.WordTrace tailWord_1281496 prefixEnd_1281496 658023404814223374706513 := by
  unfold tailWord_1281496
  simp only [CollatzResearch.WordTrace]
  refine ⟨23369999482683164468704171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31159999310244219291605561 23369999482683164468704171)
  ·
    refine ⟨35054999224024746703056257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23369999482683164468704171 35054999224024746703056257)
    ·
      refine ⟨26291249418018560027292193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35054999224024746703056257 26291249418018560027292193)
      ·
        refine ⟨19718437063513920020469145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26291249418018560027292193 19718437063513920020469145)
        ·
          refine ⟨14788827797635440015351859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19718437063513920020469145 14788827797635440015351859)
          ·
            refine ⟨22183241696453160023027789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14788827797635440015351859 22183241696453160023027789)
            ·
              refine ⟨8318715636169935008635421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22183241696453160023027789 8318715636169935008635421)
              ·
                refine ⟨3119518363563725628238283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8318715636169935008635421 3119518363563725628238283)
                ·
                  refine ⟨4679277545345588442357425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3119518363563725628238283 4679277545345588442357425)
                  ·
                    refine ⟨3509458159009191331768069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4679277545345588442357425 3509458159009191331768069)
                    ·
                      refine ⟨658023404814223374706513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3509458159009191331768069 658023404814223374706513)
                      ·
                        rfl

theorem cell23_1281496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 3, 1, 2, 4].length) (baseStart_1281496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1281496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1281496 prefixEnd_1281496 := by exact prefixLift 1281496
  have htrace : WordTrace (prefixWord ++ tailWord_1281496) baseStart_1281496 baseEnd_1281496 := by
    simpa [prefixWord, tailWord_1281496, baseEnd_1281496] using wordTrace_append hprefix tailTrace_1281496
  have hstable : (prefixWord ++ tailWord_1281496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281496).length < 2 ^ (prefixWord ++ tailWord_1281496).sum := by decide
  have hdescent : baseEnd_1281496 < baseStart_1281496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281503 : List Nat := [1, 1, 2, 3, 3, 1, 2, 4, 1, 2, 3]
def baseStart_1281503 : Nat := 118140960795 + 1281503 * 2 ^ 59
def prefixEnd_1281503 : Nat := 4983230072969 + 3 ^ 40 * 1281503 * 2
def baseEnd_1281503 : Nat := 658026999178804847318981

theorem tailTrace_1281503 : CollatzResearch.WordTrace tailWord_1281503 prefixEnd_1281503 658026999178804847318981 := by
  unfold tailWord_1281503
  simp only [CollatzResearch.WordTrace]
  refine ⟨46740254276340969132913163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31160169517560646088608775 46740254276340969132913163)
  ·
    refine ⟨70110381414511453699369745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46740254276340969132913163 70110381414511453699369745)
    ·
      refine ⟨52582786060883590274527309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70110381414511453699369745 52582786060883590274527309)
      ·
        refine ⟨19718544772831346352947741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52582786060883590274527309 19718544772831346352947741)
        ·
          refine ⟨7394454289811754882355403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19718544772831346352947741 7394454289811754882355403)
          ·
            refine ⟨11091681434717632323533105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7394454289811754882355403 11091681434717632323533105)
            ·
              refine ⟨8318761076038224242649829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11091681434717632323533105 8318761076038224242649829)
              ·
                refine ⟨1559767701757167045496843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8318761076038224242649829 1559767701757167045496843)
                ·
                  refine ⟨2339651552635750568245265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1559767701757167045496843 2339651552635750568245265)
                  ·
                    refine ⟨1754738664476812926183949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2339651552635750568245265 1754738664476812926183949)
                    ·
                      refine ⟨658026999178804847318981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1754738664476812926183949 658026999178804847318981)
                      ·
                        rfl

theorem cell23_1281503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 4, 1, 2, 3].length) (baseStart_1281503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1281503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1281503 prefixEnd_1281503 := by exact prefixLift 1281503
  have htrace : WordTrace (prefixWord ++ tailWord_1281503) baseStart_1281503 baseEnd_1281503 := by
    simpa [prefixWord, tailWord_1281503, baseEnd_1281503] using wordTrace_append hprefix tailTrace_1281503
  have hstable : (prefixWord ++ tailWord_1281503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281503).length < 2 ^ (prefixWord ++ tailWord_1281503).sum := by decide
  have hdescent : baseEnd_1281503 < baseStart_1281503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281516 : List Nat := [2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 3]
def baseStart_1281516 : Nat := 118140960795 + 1281516 * 2 ^ 59
def prefixEnd_1281516 : Nat := 4983230072969 + 3 ^ 40 * 1281516 * 2
def baseEnd_1281516 : Nat := 658033674427313296456421

theorem tailTrace_1281516 : CollatzResearch.WordTrace tailWord_1281516 prefixEnd_1281516 658033674427313296456421 := by
  unfold tailWord_1281516
  simp only [CollatzResearch.WordTrace]
  refine ⟨23370364212646936176568201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31160485616862581568757601 23370364212646936176568201)
  ·
    refine ⟨17527773159485202132426151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23370364212646936176568201 17527773159485202132426151)
    ·
      refine ⟨26291659739227803198639227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17527773159485202132426151 26291659739227803198639227)
      ·
        refine ⟨39437489608841704797958841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26291659739227803198639227 39437489608841704797958841)
        ·
          refine ⟨29578117206631278598469131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39437489608841704797958841 29578117206631278598469131)
          ·
            refine ⟨44367175809946917897703697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29578117206631278598469131 44367175809946917897703697)
            ·
              refine ⟨33275381857460188423277773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44367175809946917897703697 33275381857460188423277773)
              ·
                refine ⟨12478268196547570658729165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33275381857460188423277773 12478268196547570658729165)
                ·
                  refine ⟨4679350573705338997023437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12478268196547570658729165 4679350573705338997023437)
                  ·
                    refine ⟨1754756465139502123883789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4679350573705338997023437 1754756465139502123883789)
                    ·
                      refine ⟨658033674427313296456421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1754756465139502123883789 658033674427313296456421)
                      ·
                        rfl

theorem cell23_1281516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 3].length) (baseStart_1281516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1281516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1281516 prefixEnd_1281516 := by exact prefixLift 1281516
  have htrace : WordTrace (prefixWord ++ tailWord_1281516) baseStart_1281516 baseEnd_1281516 := by
    simpa [prefixWord, tailWord_1281516, baseEnd_1281516] using wordTrace_append hprefix tailTrace_1281516
  have hstable : (prefixWord ++ tailWord_1281516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281516).length < 2 ^ (prefixWord ++ tailWord_1281516).sum := by decide
  have hdescent : baseEnd_1281516 < baseStart_1281516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281520 : List Nat := [2, 1, 1, 1, 3, 4, 4, 1, 1, 2, 3]
def baseStart_1281520 : Nat := 118140960795 + 1281520 * 2 ^ 59
def prefixEnd_1281520 : Nat := 4983230072969 + 3 ^ 40 * 1281520 * 2
def baseEnd_1281520 : Nat := 658035728349931280806403

theorem tailTrace_1281520 : CollatzResearch.WordTrace tailWord_1281520 prefixEnd_1281520 658035728349931280806403 := by
  unfold tailWord_1281520
  simp only [CollatzResearch.WordTrace]
  refine ⟨23370437158639690518141007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31160582878186254024188009 23370437158639690518141007)
  ·
    refine ⟨35055655737959535777211511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23370437158639690518141007 35055655737959535777211511)
    ·
      refine ⟨52583483606939303665817267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35055655737959535777211511 52583483606939303665817267)
      ·
        refine ⟨78875225410408955498725901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52583483606939303665817267 78875225410408955498725901)
        ·
          refine ⟨29578209528903358312022213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78875225410408955498725901 29578209528903358312022213)
          ·
            refine ⟨5545914286669379683504165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29578209528903358312022213 5545914286669379683504165)
            ·
              refine ⟨1039858928750508690657031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5545914286669379683504165 1039858928750508690657031)
              ·
                refine ⟨1559788393125763035985547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1039858928750508690657031 1559788393125763035985547)
                ·
                  refine ⟨2339682589688644553978321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1559788393125763035985547 2339682589688644553978321)
                  ·
                    refine ⟨1754761942266483415483741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2339682589688644553978321 1754761942266483415483741)
                    ·
                      refine ⟨658035728349931280806403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1754761942266483415483741 658035728349931280806403)
                      ·
                        rfl

theorem cell23_1281520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 4, 1, 1, 2, 3].length) (baseStart_1281520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1281520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1281520 prefixEnd_1281520 := by exact prefixLift 1281520
  have htrace : WordTrace (prefixWord ++ tailWord_1281520) baseStart_1281520 baseEnd_1281520 := by
    simpa [prefixWord, tailWord_1281520, baseEnd_1281520] using wordTrace_append hprefix tailTrace_1281520
  have hstable : (prefixWord ++ tailWord_1281520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281520).length < 2 ^ (prefixWord ++ tailWord_1281520).sum := by decide
  have hdescent : baseEnd_1281520 < baseStart_1281520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281573 : List Nat := [1, 3, 1, 2, 2, 1, 1, 3, 3, 4, 2]
def baseStart_1281573 : Nat := 118140960795 + 1281573 * 2 ^ 59
def prefixEnd_1281573 : Nat := 4983230072969 + 3 ^ 40 * 1281573 * 2
def baseEnd_1281573 : Nat := 658062942824619573443659

theorem tailTrace_1281573 : CollatzResearch.WordTrace tailWord_1281573 prefixEnd_1281573 658062942824619573443659 := by
  unfold tailWord_1281573
  simp only [CollatzResearch.WordTrace]
  refine ⟨46742807386087371087961373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31161871590724914058640915 46742807386087371087961373)
  ·
    refine ⟨17528552769782764157985515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46742807386087371087961373 17528552769782764157985515)
    ·
      refine ⟨26292829154674146236978273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17528552769782764157985515 26292829154674146236978273)
      ·
        refine ⟨19719621866005609677733705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26292829154674146236978273 19719621866005609677733705)
        ·
          refine ⟨14789716399504207258300279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19719621866005609677733705 14789716399504207258300279)
          ·
            refine ⟨22184574599256310887450419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14789716399504207258300279 22184574599256310887450419)
            ·
              refine ⟨33276861898884466331175629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22184574599256310887450419 33276861898884466331175629)
              ·
                refine ⟨12478823212081674874190861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33276861898884466331175629 12478823212081674874190861)
                ·
                  refine ⟨4679558704530628077821573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12478823212081674874190861 4679558704530628077821573)
                  ·
                    refine ⟨877417257099492764591545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4679558704530628077821573 877417257099492764591545)
                    ·
                      refine ⟨658062942824619573443659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 877417257099492764591545 658062942824619573443659)
                      ·
                        rfl

theorem cell23_1281573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 3, 4, 2].length) (baseStart_1281573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1281573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1281573 prefixEnd_1281573 := by exact prefixLift 1281573
  have htrace : WordTrace (prefixWord ++ tailWord_1281573) baseStart_1281573 baseEnd_1281573 := by
    simpa [prefixWord, tailWord_1281573, baseEnd_1281573] using wordTrace_append hprefix tailTrace_1281573
  have hstable : (prefixWord ++ tailWord_1281573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281573).length < 2 ^ (prefixWord ++ tailWord_1281573).sum := by decide
  have hdescent : baseEnd_1281573 < baseStart_1281573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281626 : List Nat := [3, 1, 1, 2, 1, 1, 1, 5, 1, 7]
def baseStart_1281626 : Nat := 118140960795 + 1281626 * 2 ^ 59
def prefixEnd_1281626 : Nat := 4983230072969 + 3 ^ 40 * 1281626 * 2
def baseEnd_1281626 : Nat := 219363385766435955360305

theorem tailTrace_1281626 : CollatzResearch.WordTrace tailWord_1281626 prefixEnd_1281626 219363385766435955360305 := by
  unfold tailWord_1281626
  simp only [CollatzResearch.WordTrace]
  refine ⟨11686185113723840284910183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31163160303263574093093821 11686185113723840284910183)
  ·
    refine ⟨17529277670585760427365275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11686185113723840284910183 17529277670585760427365275)
    ·
      refine ⟨26293916505878640641047913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17529277670585760427365275 26293916505878640641047913)
      ·
        refine ⟨19720437379408980480785935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26293916505878640641047913 19720437379408980480785935)
        ·
          refine ⟨29580656069113470721178903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19720437379408980480785935 29580656069113470721178903)
          ·
            refine ⟨44370984103670206081768355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29580656069113470721178903 44370984103670206081768355)
            ·
              refine ⟨66556476155505309122652533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44370984103670206081768355 66556476155505309122652533)
              ·
                refine ⟨6239669639578622730248675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 66556476155505309122652533 6239669639578622730248675)
                ·
                  refine ⟨9359504459367934095373013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6239669639578622730248675 9359504459367934095373013)
                  ·
                    refine ⟨219363385766435955360305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9359504459367934095373013 219363385766435955360305)
                    ·
                      rfl

theorem cell23_1281626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 5, 1, 7].length) (baseStart_1281626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1281626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1281626 prefixEnd_1281626 := by exact prefixLift 1281626
  have htrace : WordTrace (prefixWord ++ tailWord_1281626) baseStart_1281626 baseEnd_1281626 := by
    simpa [prefixWord, tailWord_1281626, baseEnd_1281626] using wordTrace_append hprefix tailTrace_1281626
  have hstable : (prefixWord ++ tailWord_1281626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281626).length < 2 ^ (prefixWord ++ tailWord_1281626).sum := by decide
  have hdescent : baseEnd_1281626 < baseStart_1281626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281650 : List Nat := [3, 2, 1, 2, 3, 1, 1, 1, 2, 5, 2]
def baseStart_1281650 : Nat := 118140960795 + 1281650 * 2 ^ 59
def prefixEnd_1281650 : Nat := 4983230072969 + 3 ^ 40 * 1281650 * 2
def baseEnd_1281650 : Nat := 658102480835015772180805

theorem tailTrace_1281650 : CollatzResearch.WordTrace tailWord_1281650 prefixEnd_1281650 658102480835015772180805 := by
  unfold tailWord_1281650
  simp only [CollatzResearch.WordTrace]
  refine ⟨11686403951702103309628601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31163743871205608825676269 11686403951702103309628601)
  ·
    refine ⟨8764802963776577482221451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11686403951702103309628601 8764802963776577482221451)
    ·
      refine ⟨13147204445664866223332177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8764802963776577482221451 13147204445664866223332177)
      ·
        refine ⟨9860403334248649667499133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13147204445664866223332177 9860403334248649667499133)
        ·
          refine ⟨3697651250343243625312175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9860403334248649667499133 3697651250343243625312175)
          ·
            refine ⟨5546476875514865437968263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3697651250343243625312175 5546476875514865437968263)
            ·
              refine ⟨8319715313272298156952395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5546476875514865437968263 8319715313272298156952395)
              ·
                refine ⟨12479572969908447235428593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8319715313272298156952395 12479572969908447235428593)
                ·
                  refine ⟨9359679727431335426571445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12479572969908447235428593 9359679727431335426571445)
                  ·
                    refine ⟨877469974446687696241073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9359679727431335426571445 877469974446687696241073)
                    ·
                      refine ⟨658102480835015772180805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 877469974446687696241073 658102480835015772180805)
                      ·
                        rfl

theorem cell23_1281650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 2, 5, 2].length) (baseStart_1281650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1281650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1281650 prefixEnd_1281650 := by exact prefixLift 1281650
  have htrace : WordTrace (prefixWord ++ tailWord_1281650) baseStart_1281650 baseEnd_1281650 := by
    simpa [prefixWord, tailWord_1281650, baseEnd_1281650] using wordTrace_append hprefix tailTrace_1281650
  have hstable : (prefixWord ++ tailWord_1281650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281650).length < 2 ^ (prefixWord ++ tailWord_1281650).sum := by decide
  have hdescent : baseEnd_1281650 < baseStart_1281650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281673 : List Nat := [1, 2, 1, 1, 4, 1, 3, 1, 5, 4]
def baseStart_1281673 : Nat := 118140960795 + 1281673 * 2 ^ 59
def prefixEnd_1281673 : Nat := 4983230072969 + 3 ^ 40 * 1281673 * 2
def baseEnd_1281673 : Nat := 219371430296689727397733

theorem tailTrace_1281673 : CollatzResearch.WordTrace tailWord_1281673 prefixEnd_1281673 219371430296689727397733 := by
  unfold tailWord_1281673
  simp only [CollatzResearch.WordTrace]
  refine ⟨46746454685725088166601673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31164303123816725444401115 46746454685725088166601673)
  ·
    refine ⟨35059841014293816124951255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46746454685725088166601673 35059841014293816124951255)
    ·
      refine ⟨52589761521440724187426883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35059841014293816124951255 52589761521440724187426883)
      ·
        refine ⟨78884642282161086281140325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52589761521440724187426883 78884642282161086281140325)
        ·
          refine ⟨14790870427905203677713811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78884642282161086281140325 14790870427905203677713811)
          ·
            refine ⟨22186305641857805516570717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14790870427905203677713811 22186305641857805516570717)
            ·
              refine ⟨8319864615696677068714019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22186305641857805516570717 8319864615696677068714019)
              ·
                refine ⟨12479796923545015603071029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8319864615696677068714019 12479796923545015603071029)
                ·
                  refine ⟨1169980961582345212787909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12479796923545015603071029 1169980961582345212787909)
                  ·
                    refine ⟨219371430296689727397733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1169980961582345212787909 219371430296689727397733)
                    ·
                      rfl

theorem cell23_1281673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 5, 4].length) (baseStart_1281673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1281673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1281673 prefixEnd_1281673 := by exact prefixLift 1281673
  have htrace : WordTrace (prefixWord ++ tailWord_1281673) baseStart_1281673 baseEnd_1281673 := by
    simpa [prefixWord, tailWord_1281673, baseEnd_1281673] using wordTrace_append hprefix tailTrace_1281673
  have hstable : (prefixWord ++ tailWord_1281673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281673).length < 2 ^ (prefixWord ++ tailWord_1281673).sum := by decide
  have hdescent : baseEnd_1281673 < baseStart_1281673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281734 : List Nat := [6, 1, 2, 1, 1, 1, 2, 1, 1, 4, 3]
def baseStart_1281734 : Nat := 118140960795 + 1281734 * 2 ^ 59
def prefixEnd_1281734 : Nat := 4983230072969 + 3 ^ 40 * 1281734 * 2
def baseEnd_1281734 : Nat := 658145613209993443530419

theorem tailTrace_1281734 : CollatzResearch.WordTrace tailWord_1281734 prefixEnd_1281734 658145613209993443530419 := by
  unfold tailWord_1281734
  simp only [CollatzResearch.WordTrace]
  refine ⟨1460896235578252987017883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 31165786359002730389714837 1460896235578252987017883)
  ·
    refine ⟨2191344353367379480526825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1460896235578252987017883 2191344353367379480526825)
    ·
      refine ⟨1643508265025534610395119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2191344353367379480526825 1643508265025534610395119)
      ·
        refine ⟨2465262397538301915592679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1643508265025534610395119 2465262397538301915592679)
        ·
          refine ⟨3697893596307452873389019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2465262397538301915592679 3697893596307452873389019)
          ·
            refine ⟨5546840394461179310083529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3697893596307452873389019 5546840394461179310083529)
            ·
              refine ⟨4160130295845884482562647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5546840394461179310083529 4160130295845884482562647)
              ·
                refine ⟨6240195443768826723843971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4160130295845884482562647 6240195443768826723843971)
                ·
                  refine ⟨9360293165653240085765957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6240195443768826723843971 9360293165653240085765957)
                  ·
                    refine ⟨1755054968559982516081117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9360293165653240085765957 1755054968559982516081117)
                    ·
                      refine ⟨658145613209993443530419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1755054968559982516081117 658145613209993443530419)
                      ·
                        rfl

theorem cell23_1281734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_1281734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1281734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1281734 prefixEnd_1281734 := by exact prefixLift 1281734
  have htrace : WordTrace (prefixWord ++ tailWord_1281734) baseStart_1281734 baseEnd_1281734 := by
    simpa [prefixWord, tailWord_1281734, baseEnd_1281734] using wordTrace_append hprefix tailTrace_1281734
  have hstable : (prefixWord ++ tailWord_1281734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281734).length < 2 ^ (prefixWord ++ tailWord_1281734).sum := by decide
  have hdescent : baseEnd_1281734 < baseStart_1281734 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281741 : List Nat := [1, 6, 2, 1, 1, 1, 3, 3, 1, 4]
def baseStart_1281741 : Nat := 118140960795 + 1281741 * 2 ^ 59
def prefixEnd_1281741 : Nat := 4983230072969 + 3 ^ 40 * 1281741 * 2
def baseEnd_1281741 : Nat := 219383069191524972047629

theorem tailTrace_1281741 : CollatzResearch.WordTrace tailWord_1281741 prefixEnd_1281741 219383069191524972047629 := by
  unfold tailWord_1281741
  simp only [CollatzResearch.WordTrace]
  refine ⟨46748934849478735780077077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31165956566319157186718051 46748934849478735780077077)
  ·
    refine ⟨2191356321069315739691113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 46748934849478735780077077 2191356321069315739691113)
    ·
      refine ⟨1643517240801986804768335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2191356321069315739691113 1643517240801986804768335)
      ·
        refine ⟨2465275861202980207152503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1643517240801986804768335 2465275861202980207152503)
        ·
          refine ⟨3697913791804470310728755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2465275861202980207152503 3697913791804470310728755)
          ·
            refine ⟨5546870687706705466093133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3697913791804470310728755 5546870687706705466093133)
            ·
              refine ⟨2080076507890014549784925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5546870687706705466093133 2080076507890014549784925)
              ·
                refine ⟨780028690458755456169347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2080076507890014549784925 780028690458755456169347)
                ·
                  refine ⟨1170043035688133184254021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 780028690458755456169347 1170043035688133184254021)
                  ·
                    refine ⟨219383069191524972047629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1170043035688133184254021 219383069191524972047629)
                    ·
                      rfl

theorem cell23_1281741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_1281741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1281741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1281741 prefixEnd_1281741 := by exact prefixLift 1281741
  have htrace : WordTrace (prefixWord ++ tailWord_1281741) baseStart_1281741 baseEnd_1281741 := by
    simpa [prefixWord, tailWord_1281741, baseEnd_1281741] using wordTrace_append hprefix tailTrace_1281741
  have hstable : (prefixWord ++ tailWord_1281741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281741).length < 2 ^ (prefixWord ++ tailWord_1281741).sum := by decide
  have hdescent : baseEnd_1281741 < baseStart_1281741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281783 : List Nat := [1, 1, 3, 1, 1, 1, 6, 1, 1, 1, 6]
def baseStart_1281783 : Nat := 118140960795 + 1281783 * 2 ^ 59
def prefixEnd_1281783 : Nat := 4983230072969 + 3 ^ 40 * 1281783 * 2
def baseEnd_1281783 : Nat := 658170773762063751817693

theorem tailTrace_1281783 : CollatzResearch.WordTrace tailWord_1281783 prefixEnd_1281783 658170773762063751817693 := by
  unfold tailWord_1281783
  simp only [CollatzResearch.WordTrace]
  refine ⟨46750466715326576953106003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31166977810217717968737335 46750466715326576953106003)
  ·
    refine ⟨70125700072989865429659005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46750466715326576953106003 70125700072989865429659005)
    ·
      refine ⟨26297137527371199536122127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70125700072989865429659005 26297137527371199536122127)
      ·
        refine ⟨39445706291056799304183191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26297137527371199536122127 39445706291056799304183191)
        ·
          refine ⟨59168559436585198956274787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39445706291056799304183191 59168559436585198956274787)
          ·
            refine ⟨88752839154877798434412181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59168559436585198956274787 88752839154877798434412181)
            ·
              refine ⟨4160289335384896801613071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 88752839154877798434412181 4160289335384896801613071)
              ·
                refine ⟨6240434003077345202419607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4160289335384896801613071 6240434003077345202419607)
                ·
                  refine ⟨9360651004616017803629411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6240434003077345202419607 9360651004616017803629411)
                  ·
                    refine ⟨14040976506924026705444117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9360651004616017803629411 14040976506924026705444117)
                    ·
                      refine ⟨658170773762063751817693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14040976506924026705444117 658170773762063751817693)
                      ·
                        rfl

theorem cell23_1281783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 1, 1, 1, 6].length) (baseStart_1281783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1281783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1281783 prefixEnd_1281783 := by exact prefixLift 1281783
  have htrace : WordTrace (prefixWord ++ tailWord_1281783) baseStart_1281783 baseEnd_1281783 := by
    simpa [prefixWord, tailWord_1281783, baseEnd_1281783] using wordTrace_append hprefix tailTrace_1281783
  have hstable : (prefixWord ++ tailWord_1281783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281783).length < 2 ^ (prefixWord ++ tailWord_1281783).sum := by decide
  have hdescent : baseEnd_1281783 < baseStart_1281783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281793 : List Nat := [1, 2, 4, 1, 1, 1, 4, 9]
def baseStart_1281793 : Nat := 118140960795 + 1281793 * 2 ^ 59
def prefixEnd_1281793 : Nat := 4983230072969 + 3 ^ 40 * 1281793 * 2
def baseEnd_1281793 : Nat := 24376885502541063433061

theorem tailTrace_1281793 : CollatzResearch.WordTrace tailWord_1281793 prefixEnd_1281793 24376885502541063433061 := by
  unfold tailWord_1281793
  simp only [CollatzResearch.WordTrace]
  refine ⟨46750831445290348660970033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31167220963526899107313355 46750831445290348660970033)
  ·
    refine ⟨35063123583967761495727525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46750831445290348660970033 35063123583967761495727525)
    ·
      refine ⟨6574335671993955280448911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35063123583967761495727525 6574335671993955280448911)
      ·
        refine ⟨9861503507990932920673367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6574335671993955280448911 9861503507990932920673367)
        ·
          refine ⟨14792255261986399381010051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9861503507990932920673367 14792255261986399381010051)
          ·
            refine ⟨22188382892979599071515077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14792255261986399381010051 22188382892979599071515077)
            ·
              refine ⟨4160321792433674825909077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22188382892979599071515077 4160321792433674825909077)
              ·
                refine ⟨24376885502541063433061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4160321792433674825909077 24376885502541063433061)
                ·
                  rfl

theorem cell23_1281793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 9].length) (baseStart_1281793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1281793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1281793 prefixEnd_1281793 := by exact prefixLift 1281793
  have htrace : WordTrace (prefixWord ++ tailWord_1281793) baseStart_1281793 baseEnd_1281793 := by
    simpa [prefixWord, tailWord_1281793, baseEnd_1281793] using wordTrace_append hprefix tailTrace_1281793
  have hstable : (prefixWord ++ tailWord_1281793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281793).length < 2 ^ (prefixWord ++ tailWord_1281793).sum := by decide
  have hdescent : baseEnd_1281793 < baseStart_1281793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281800 : List Nat := [2, 1, 3, 2, 2, 1, 3, 2, 1, 2, 4]
def baseStart_1281800 : Nat := 118140960795 + 1281800 * 2 ^ 59
def prefixEnd_1281800 : Nat := 4983230072969 + 3 ^ 40 * 1281800 * 2
def baseEnd_1281800 : Nat := 658179502933190185305115

theorem tailTrace_1281800 : CollatzResearch.WordTrace tailWord_1281800 prefixEnd_1281800 658179502933190185305115 := by
  unfold tailWord_1281800
  simp only [CollatzResearch.WordTrace]
  refine ⟨23375543378132494428237427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31167391170843325904316569 23375543378132494428237427)
  ·
    refine ⟨35063315067198741642356141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23375543378132494428237427 35063315067198741642356141)
    ·
      refine ⟨13148743150199528115883553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35063315067198741642356141 13148743150199528115883553)
      ·
        refine ⟨9861557362649646086912665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13148743150199528115883553 9861557362649646086912665)
        ·
          refine ⟨7396168021987234565184499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9861557362649646086912665 7396168021987234565184499)
          ·
            refine ⟨11094252032980851847776749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7396168021987234565184499 11094252032980851847776749)
            ·
              refine ⟨4160344512367819442916281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11094252032980851847776749 4160344512367819442916281)
              ·
                refine ⟨3120258384275864582187211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4160344512367819442916281 3120258384275864582187211)
                ·
                  refine ⟨4680387576413796873280817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3120258384275864582187211 4680387576413796873280817)
                  ·
                    refine ⟨3510290682310347654960613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4680387576413796873280817 3510290682310347654960613)
                    ·
                      refine ⟨658179502933190185305115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3510290682310347654960613 658179502933190185305115)
                      ·
                        rfl

theorem cell23_1281800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 2, 1, 2, 4].length) (baseStart_1281800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1281800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1281800 prefixEnd_1281800 := by exact prefixLift 1281800
  have htrace : WordTrace (prefixWord ++ tailWord_1281800) baseStart_1281800 baseEnd_1281800 := by
    simpa [prefixWord, tailWord_1281800, baseEnd_1281800] using wordTrace_append hprefix tailTrace_1281800
  have hstable : (prefixWord ++ tailWord_1281800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281800).length < 2 ^ (prefixWord ++ tailWord_1281800).sum := by decide
  have hdescent : baseEnd_1281800 < baseStart_1281800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281810 : List Nat := [3, 2, 4, 1, 1, 12]
def baseStart_1281810 : Nat := 118140960795 + 1281810 * 2 ^ 59
def prefixEnd_1281810 : Nat := 4983230072969 + 3 ^ 40 * 1281810 * 2
def baseEnd_1281810 : Nat := 2708578756130597309383

theorem tailTrace_1281810 : CollatzResearch.WordTrace tailWord_1281810 prefixEnd_1281810 2708578756130597309383 := by
  unfold tailWord_1281810
  simp only [CollatzResearch.WordTrace]
  refine ⟨11687862871557190141084721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31167634324152507042892589 11687862871557190141084721)
  ·
    refine ⟨8765897153667892605813541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11687862871557190141084721 8765897153667892605813541)
    ·
      refine ⟨1643605716312729863590039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8765897153667892605813541 1643605716312729863590039)
      ·
        refine ⟨2465408574469094795385059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1643605716312729863590039 2465408574469094795385059)
        ·
          refine ⟨3698112861703642193077589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2465408574469094795385059 3698112861703642193077589)
          ·
            refine ⟨2708578756130597309383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 3698112861703642193077589 2708578756130597309383)
            ·
              rfl

theorem cell23_1281810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 12].length) (baseStart_1281810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1281810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1281810 prefixEnd_1281810 := by exact prefixLift 1281810
  have htrace : WordTrace (prefixWord ++ tailWord_1281810) baseStart_1281810 baseEnd_1281810 := by
    simpa [prefixWord, tailWord_1281810, baseEnd_1281810] using wordTrace_append hprefix tailTrace_1281810
  have hstable : (prefixWord ++ tailWord_1281810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281810).length < 2 ^ (prefixWord ++ tailWord_1281810).sum := by decide
  have hdescent : baseEnd_1281810 < baseStart_1281810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281820 : List Nat := [2, 2, 3, 1, 1, 2, 1, 2, 3, 3, 3]
def baseStart_1281820 : Nat := 118140960795 + 1281820 * 2 ^ 59
def prefixEnd_1281820 : Nat := 4983230072969 + 3 ^ 40 * 1281820 * 2
def baseEnd_1281820 : Nat := 658189772546280107055023

theorem tailTrace_1281820 : CollatzResearch.WordTrace tailWord_1281820 prefixEnd_1281820 658189772546280107055023 := by
  unfold tailWord_1281820
  simp only [CollatzResearch.WordTrace]
  refine ⟨23375908108096266136101457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31167877477461688181468609 23375908108096266136101457)
  ·
    refine ⟨17531931081072199602076093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23375908108096266136101457 17531931081072199602076093)
    ·
      refine ⟨6574474155402074850778535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17531931081072199602076093 6574474155402074850778535)
      ·
        refine ⟨9861711233103112276167803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6574474155402074850778535 9861711233103112276167803)
        ·
          refine ⟨14792566849654668414251705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9861711233103112276167803 14792566849654668414251705)
          ·
            refine ⟨11094425137241001310688779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14792566849654668414251705 11094425137241001310688779)
            ·
              refine ⟨16641637705861501966033169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11094425137241001310688779 16641637705861501966033169)
              ·
                refine ⟨12481228279396126474524877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16641637705861501966033169 12481228279396126474524877)
                ·
                  refine ⟨4680460604773547427946829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12481228279396126474524877 4680460604773547427946829)
                  ·
                    refine ⟨1755172726790080285480061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4680460604773547427946829 1755172726790080285480061)
                    ·
                      refine ⟨658189772546280107055023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1755172726790080285480061 658189772546280107055023)
                      ·
                        rfl

theorem cell23_1281820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 3, 3, 3].length) (baseStart_1281820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1281820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1281820 prefixEnd_1281820 := by exact prefixLift 1281820
  have htrace : WordTrace (prefixWord ++ tailWord_1281820) baseStart_1281820 baseEnd_1281820 := by
    simpa [prefixWord, tailWord_1281820, baseEnd_1281820] using wordTrace_append hprefix tailTrace_1281820
  have hstable : (prefixWord ++ tailWord_1281820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281820).length < 2 ^ (prefixWord ++ tailWord_1281820).sum := by decide
  have hdescent : baseEnd_1281820 < baseStart_1281820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281823 : List Nat := [1, 1, 2, 4, 2, 1, 1, 1, 1, 9]
def baseStart_1281823 : Nat := 118140960795 + 1281823 * 2 ^ 59
def prefixEnd_1281823 : Nat := 4983230072969 + 3 ^ 40 * 1281823 * 2
def baseEnd_1281823 : Nat := 219397104329414531772503

theorem tailTrace_1281823 : CollatzResearch.WordTrace tailWord_1281823 prefixEnd_1281823 219397104329414531772503 := by
  unfold tailWord_1281823
  simp only [CollatzResearch.WordTrace]
  refine ⟨46751925635181663784562123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31167950423454442523041415 46751925635181663784562123)
  ·
    refine ⟨70127888452772495676843185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46751925635181663784562123 70127888452772495676843185)
    ·
      refine ⟨52595916339579371757632389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70127888452772495676843185 52595916339579371757632389)
      ·
        refine ⟨9861734313671132204556073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52595916339579371757632389 9861734313671132204556073)
        ·
          refine ⟨7396300735253349153417055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9861734313671132204556073 7396300735253349153417055)
          ·
            refine ⟨11094451102880023730125583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7396300735253349153417055 11094451102880023730125583)
            ·
              refine ⟨16641676654320035595188375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11094451102880023730125583 16641676654320035595188375)
              ·
                refine ⟨24962514981480053392782563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16641676654320035595188375 24962514981480053392782563)
                ·
                  refine ⟨37443772472220080089173845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24962514981480053392782563 37443772472220080089173845)
                  ·
                    refine ⟨219397104329414531772503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 37443772472220080089173845 219397104329414531772503)
                    ·
                      rfl

theorem cell23_1281823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 9].length) (baseStart_1281823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1281823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1281823 prefixEnd_1281823 := by exact prefixLift 1281823
  have htrace : WordTrace (prefixWord ++ tailWord_1281823) baseStart_1281823 baseEnd_1281823 := by
    simpa [prefixWord, tailWord_1281823, baseEnd_1281823] using wordTrace_append hprefix tailTrace_1281823
  have hstable : (prefixWord ++ tailWord_1281823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281823).length < 2 ^ (prefixWord ++ tailWord_1281823).sum := by decide
  have hdescent : baseEnd_1281823 < baseStart_1281823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281864 : List Nat := [2, 1, 3, 1, 1, 5, 1, 3, 1, 3, 2]
def baseStart_1281864 : Nat := 118140960795 + 1281864 * 2 ^ 59
def prefixEnd_1281864 : Nat := 4983230072969 + 3 ^ 40 * 1281864 * 2
def baseEnd_1281864 : Nat := 658212365695077934904821

theorem tailTrace_1281864 : CollatzResearch.WordTrace tailWord_1281864 prefixEnd_1281864 658212365695077934904821 := by
  unfold tailWord_1281864
  simp only [CollatzResearch.WordTrace]
  refine ⟨23376710514016563893402323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31168947352022085191203097 23376710514016563893402323)
  ·
    refine ⟨35065065771024845840103485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23376710514016563893402323 35065065771024845840103485)
    ·
      refine ⟨13149399664134317190038807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35065065771024845840103485 13149399664134317190038807)
      ·
        refine ⟨19724099496201475785058211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13149399664134317190038807 19724099496201475785058211)
        ·
          refine ⟨29586149244302213677587317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19724099496201475785058211 29586149244302213677587317)
          ·
            refine ⟨2773701491653332532273811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29586149244302213677587317 2773701491653332532273811)
            ·
              refine ⟨4160552237479998798410717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2773701491653332532273811 4160552237479998798410717)
              ·
                refine ⟨1560207089054999549404019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4160552237479998798410717 1560207089054999549404019)
                ·
                  refine ⟨2340310633582499324106029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1560207089054999549404019 2340310633582499324106029)
                  ·
                    refine ⟨877616487593437246539761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2340310633582499324106029 877616487593437246539761)
                    ·
                      refine ⟨658212365695077934904821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 877616487593437246539761 658212365695077934904821)
                      ·
                        rfl

theorem cell23_1281864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 3, 1, 3, 2].length) (baseStart_1281864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1281864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1281864 prefixEnd_1281864 := by exact prefixLift 1281864
  have htrace : WordTrace (prefixWord ++ tailWord_1281864) baseStart_1281864 baseEnd_1281864 := by
    simpa [prefixWord, tailWord_1281864, baseEnd_1281864] using wordTrace_append hprefix tailTrace_1281864
  have hstable : (prefixWord ++ tailWord_1281864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281864).length < 2 ^ (prefixWord ++ tailWord_1281864).sum := by decide
  have hdescent : baseEnd_1281864 < baseStart_1281864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281898 : List Nat := [3, 1, 3, 4, 1, 1, 2, 2, 1, 3, 2]
def baseStart_1281898 : Nat := 118140960795 + 1281898 * 2 ^ 59
def prefixEnd_1281898 : Nat := 4983230072969 + 3 ^ 40 * 1281898 * 2
def baseEnd_1281898 : Nat := 658229824037330801879665

theorem tailTrace_1281898 : CollatzResearch.WordTrace tailWord_1281898 prefixEnd_1281898 658229824037330801879665 := by
  unfold tailWord_1281898
  simp only [CollatzResearch.WordTrace]
  refine ⟨11688665277477487898385587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31169774073273301062361565 11688665277477487898385587)
  ·
    refine ⟨17532997916216231847578381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11688665277477487898385587 17532997916216231847578381)
    ·
      refine ⟨6574874218581086942841893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17532997916216231847578381 6574874218581086942841893)
      ·
        refine ⟨1232788915983953801782855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6574874218581086942841893 1232788915983953801782855)
        ·
          refine ⟨1849183373975930702674283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1232788915983953801782855 1849183373975930702674283)
          ·
            refine ⟨2773775060963896054011425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1849183373975930702674283 2773775060963896054011425)
            ·
              refine ⟨2080331295722922040508569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2773775060963896054011425 2080331295722922040508569)
              ·
                refine ⟨1560248471792191530381427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2080331295722922040508569 1560248471792191530381427)
                ·
                  refine ⟨2340372707688287295572141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1560248471792191530381427 2340372707688287295572141)
                  ·
                    refine ⟨877639765383107735839553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2340372707688287295572141 877639765383107735839553)
                    ·
                      refine ⟨658229824037330801879665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 877639765383107735839553 658229824037330801879665)
                      ·
                        rfl

theorem cell23_1281898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_1281898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1281898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1281898 prefixEnd_1281898 := by exact prefixLift 1281898
  have htrace : WordTrace (prefixWord ++ tailWord_1281898) baseStart_1281898 baseEnd_1281898 := by
    simpa [prefixWord, tailWord_1281898, baseEnd_1281898] using wordTrace_append hprefix tailTrace_1281898
  have hstable : (prefixWord ++ tailWord_1281898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281898).length < 2 ^ (prefixWord ++ tailWord_1281898).sum := by decide
  have hdescent : baseEnd_1281898 < baseStart_1281898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281900 : List Nat := [2, 2, 1, 1, 4, 2, 2, 2, 7]
def baseStart_1281900 : Nat := 118140960795 + 1281900 * 2 ^ 59
def prefixEnd_1281900 : Nat := 4983230072969 + 3 ^ 40 * 1281900 * 2
def baseEnd_1281900 : Nat := 73136761222071088228295

theorem tailTrace_1281900 : CollatzResearch.WordTrace tailWord_1281900 prefixEnd_1281900 73136761222071088228295 := by
  unfold tailWord_1281900
  simp only [CollatzResearch.WordTrace]
  refine ⟨23377367027951352967557577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31169822703935137290076769 23377367027951352967557577)
  ·
    refine ⟨17533025270963514725668183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23377367027951352967557577 17533025270963514725668183)
    ·
      refine ⟨26299537906445272088502275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17533025270963514725668183 26299537906445272088502275)
      ·
        refine ⟨39449306859667908132753413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26299537906445272088502275 39449306859667908132753413)
        ·
          refine ⟨7396745036187732774891265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39449306859667908132753413 7396745036187732774891265)
          ·
            refine ⟨5547558777140799581168449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7396745036187732774891265 5547558777140799581168449)
            ·
              refine ⟨4160669082855599685876337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5547558777140799581168449 4160669082855599685876337)
              ·
                refine ⟨3120501812141699764407253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4160669082855599685876337 3120501812141699764407253)
                ·
                  refine ⟨73136761222071088228295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3120501812141699764407253 73136761222071088228295)
                  ·
                    rfl

theorem cell23_1281900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 7].length) (baseStart_1281900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1281900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1281900 prefixEnd_1281900 := by exact prefixLift 1281900
  have htrace : WordTrace (prefixWord ++ tailWord_1281900) baseStart_1281900 baseEnd_1281900 := by
    simpa [prefixWord, tailWord_1281900, baseEnd_1281900] using wordTrace_append hprefix tailTrace_1281900
  have hstable : (prefixWord ++ tailWord_1281900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281900).length < 2 ^ (prefixWord ++ tailWord_1281900).sum := by decide
  have hdescent : baseEnd_1281900 < baseStart_1281900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281967 : List Nat := [1, 1, 2, 1, 2, 2, 6, 1, 2, 1, 4]
def baseStart_1281967 : Nat := 118140960795 + 1281967 * 2 ^ 59
def prefixEnd_1281967 : Nat := 4983230072969 + 3 ^ 40 * 1281967 * 2
def baseEnd_1281967 : Nat := 658265254202491031916847

theorem tailTrace_1281967 : CollatzResearch.WordTrace tailWord_1281967 prefixEnd_1281967 658265254202491031916847 := by
  unfold tailWord_1281967
  simp only [CollatzResearch.WordTrace]
  refine ⟨46757177746659976377804155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31171451831106650918536103 46757177746659976377804155)
  ·
    refine ⟨70135766619989964566706233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46757177746659976377804155 70135766619989964566706233)
    ·
      refine ⟨52601824964992473425029675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70135766619989964566706233 52601824964992473425029675)
      ·
        refine ⟨78902737447488710137544513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52601824964992473425029675 78902737447488710137544513)
        ·
          refine ⟨59177053085616532603158385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78902737447488710137544513 59177053085616532603158385)
          ·
            refine ⟨44382789814212399452368789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59177053085616532603158385 44382789814212399452368789)
            ·
              refine ⟨2080443272541206224329787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 44382789814212399452368789 2080443272541206224329787)
              ·
                refine ⟨3120664908811809336494681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2080443272541206224329787 3120664908811809336494681)
                ·
                  refine ⟨2340498681608857002371011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3120664908811809336494681 2340498681608857002371011)
                  ·
                    refine ⟨3510748022413285503556517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2340498681608857002371011 3510748022413285503556517)
                    ·
                      refine ⟨658265254202491031916847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3510748022413285503556517 658265254202491031916847)
                      ·
                        rfl

theorem cell23_1281967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 1, 2, 1, 4].length) (baseStart_1281967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1281967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1281967 prefixEnd_1281967 := by exact prefixLift 1281967
  have htrace : WordTrace (prefixWord ++ tailWord_1281967) baseStart_1281967 baseEnd_1281967 := by
    simpa [prefixWord, tailWord_1281967, baseEnd_1281967] using wordTrace_append hprefix tailTrace_1281967
  have hstable : (prefixWord ++ tailWord_1281967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281967).length < 2 ^ (prefixWord ++ tailWord_1281967).sum := by decide
  have hdescent : baseEnd_1281967 < baseStart_1281967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282018 : List Nat := [3, 3, 3, 1, 2, 2, 1, 1, 2, 1, 4]
def baseStart_1282018 : Nat := 118140960795 + 1282018 * 2 ^ 59
def prefixEnd_1282018 : Nat := 4983230072969 + 3 ^ 40 * 1282018 * 2
def baseEnd_1282018 : Nat := 658291441715870332379113

theorem tailTrace_1282018 : CollatzResearch.WordTrace tailWord_1282018 prefixEnd_1282018 658291441715870332379113 := by
  unfold tailWord_1282018
  simp only [CollatzResearch.WordTrace]
  refine ⟨11689759467368803021977677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31172691912983474725273805 11689759467368803021977677)
  ·
    refine ⟨4383659800263301133241629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11689759467368803021977677 4383659800263301133241629)
    ·
      refine ⟨1643872425098737924965611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4383659800263301133241629 1643872425098737924965611)
      ·
        refine ⟨2465808637648106887448417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1643872425098737924965611 2465808637648106887448417)
        ·
          refine ⟨1849356478236080165586313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2465808637648106887448417 1849356478236080165586313)
          ·
            refine ⟨1387017358677060124189735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1849356478236080165586313 1387017358677060124189735)
            ·
              refine ⟨2080526038015590186284603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1387017358677060124189735 2080526038015590186284603)
              ·
                refine ⟨3120789057023385279426905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2080526038015590186284603 3120789057023385279426905)
                ·
                  refine ⟨2340591792767538959570179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3120789057023385279426905 2340591792767538959570179)
                  ·
                    refine ⟨3510887689151308439355269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2340591792767538959570179 3510887689151308439355269)
                    ·
                      refine ⟨658291441715870332379113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3510887689151308439355269 658291441715870332379113)
                      ·
                        rfl

theorem cell23_1282018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_1282018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1282018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1282018 prefixEnd_1282018 := by exact prefixLift 1282018
  have htrace : WordTrace (prefixWord ++ tailWord_1282018) baseStart_1282018 baseEnd_1282018 := by
    simpa [prefixWord, tailWord_1282018, baseEnd_1282018] using wordTrace_append hprefix tailTrace_1282018
  have hstable : (prefixWord ++ tailWord_1282018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282018).length < 2 ^ (prefixWord ++ tailWord_1282018).sum := by decide
  have hdescent : baseEnd_1282018 < baseStart_1282018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282044 : List Nat := [2, 2, 2, 1, 2, 2, 2, 1, 4, 3, 2]
def baseStart_1282044 : Nat := 118140960795 + 1282044 * 2 ^ 59
def prefixEnd_1282044 : Nat := 4983230072969 + 3 ^ 40 * 1282044 * 2
def baseEnd_1282044 : Nat := 658304792212887230653993

theorem tailTrace_1282044 : CollatzResearch.WordTrace tailWord_1282044 prefixEnd_1282044 658304792212887230653993 := by
  unfold tailWord_1282044
  simp only [CollatzResearch.WordTrace]
  refine ⟨23379993083690509264178593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31173324111587345685571457 23379993083690509264178593)
  ·
    refine ⟨17534994812767881948133945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23379993083690509264178593 17534994812767881948133945)
    ·
      refine ⟨13151246109575911461100459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17534994812767881948133945 13151246109575911461100459)
      ·
        refine ⟨19726869164363867191650689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13151246109575911461100459 19726869164363867191650689)
        ·
          refine ⟨14795151873272900393738017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19726869164363867191650689 14795151873272900393738017)
          ·
            refine ⟨11096363904954675295303513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14795151873272900393738017 11096363904954675295303513)
            ·
              refine ⟨8322272928716006471477635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11096363904954675295303513 8322272928716006471477635)
              ·
                refine ⟨12483409393074009707216453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8322272928716006471477635 12483409393074009707216453)
                ·
                  refine ⟨2340639261201376820103085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12483409393074009707216453 2340639261201376820103085)
                  ·
                    refine ⟨877739722950516307538657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2340639261201376820103085 877739722950516307538657)
                    ·
                      refine ⟨658304792212887230653993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 877739722950516307538657 658304792212887230653993)
                      ·
                        rfl

theorem cell23_1282044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 4, 3, 2].length) (baseStart_1282044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1282044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1282044 prefixEnd_1282044 := by exact prefixLift 1282044
  have htrace : WordTrace (prefixWord ++ tailWord_1282044) baseStart_1282044 baseEnd_1282044 := by
    simpa [prefixWord, tailWord_1282044, baseEnd_1282044] using wordTrace_append hprefix tailTrace_1282044
  have hstable : (prefixWord ++ tailWord_1282044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282044).length < 2 ^ (prefixWord ++ tailWord_1282044).sum := by decide
  have hdescent : baseEnd_1282044 < baseStart_1282044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282067 : List Nat := [1, 1, 1, 2, 1, 4, 5, 1, 1, 6]
def baseStart_1282067 : Nat := 118140960795 + 1282067 * 2 ^ 59
def prefixEnd_1282067 : Nat := 4983230072969 + 3 ^ 40 * 1282067 * 2
def baseEnd_1282067 : Nat := 219438867422646880222129

theorem tailTrace_1282067 : CollatzResearch.WordTrace tailWord_1282067 prefixEnd_1282067 219438867422646880222129 := by
  unfold tailWord_1282067
  simp only [CollatzResearch.WordTrace]
  refine ⟨46760825046297693456444455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31173883364198462304296303 46760825046297693456444455)
  ·
    refine ⟨70141237569446540184666683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46760825046297693456444455 70141237569446540184666683)
    ·
      refine ⟨105211856354169810277000025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70141237569446540184666683 105211856354169810277000025)
      ·
        refine ⟨78908892265627357707750019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105211856354169810277000025 78908892265627357707750019)
        ·
          refine ⟨118363338398441036561625029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78908892265627357707750019 118363338398441036561625029)
          ·
            refine ⟨22193125949707694355304693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 118363338398441036561625029 22193125949707694355304693)
            ·
              refine ⟨2080605557785096345809815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22193125949707694355304693 2080605557785096345809815)
              ·
                refine ⟨3120908336677644518714723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2080605557785096345809815 3120908336677644518714723)
                ·
                  refine ⟨4681362505016466778072085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3120908336677644518714723 4681362505016466778072085)
                  ·
                    refine ⟨219438867422646880222129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4681362505016466778072085 219438867422646880222129)
                    ·
                      rfl

theorem cell23_1282067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 1, 1, 6].length) (baseStart_1282067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1282067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1282067 prefixEnd_1282067 := by exact prefixLift 1282067
  have htrace : WordTrace (prefixWord ++ tailWord_1282067) baseStart_1282067 baseEnd_1282067 := by
    simpa [prefixWord, tailWord_1282067, baseEnd_1282067] using wordTrace_append hprefix tailTrace_1282067
  have hstable : (prefixWord ++ tailWord_1282067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282067).length < 2 ^ (prefixWord ++ tailWord_1282067).sum := by decide
  have hdescent : baseEnd_1282067 < baseStart_1282067 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282071 : List Nat := [1, 1, 3, 5, 2, 1, 2, 2, 1, 5]
def baseStart_1282071 : Nat := 118140960795 + 1282071 * 2 ^ 59
def prefixEnd_1282071 : Nat := 4983230072969 + 3 ^ 40 * 1282071 * 2
def baseEnd_1282071 : Nat := 219439552063519541672123

theorem tailTrace_1282071 : CollatzResearch.WordTrace tailWord_1282071 prefixEnd_1282071 219439552063519541672123 := by
  unfold tailWord_1282071
  simp only [CollatzResearch.WordTrace]
  refine ⟨46760970938283202139590067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31173980625522134759726711 46760970938283202139590067)
  ·
    refine ⟨70141456407424803209385101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46760970938283202139590067 70141456407424803209385101)
    ·
      refine ⟨26303046152784301203519413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70141456407424803209385101 26303046152784301203519413)
      ·
        refine ⟨2465910576823528237829945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26303046152784301203519413 2465910576823528237829945)
        ·
          refine ⟨1849432932617646178372459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2465910576823528237829945 1849432932617646178372459)
          ·
            refine ⟨2774149398926469267558689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1849432932617646178372459 2774149398926469267558689)
            ·
              refine ⟨2080612049194851950669017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2774149398926469267558689 2080612049194851950669017)
              ·
                refine ⟨1560459036896138963001763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2080612049194851950669017 1560459036896138963001763)
                ·
                  refine ⟨2340688555344208444502645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1560459036896138963001763 2340688555344208444502645)
                  ·
                    refine ⟨219439552063519541672123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2340688555344208444502645 219439552063519541672123)
                    ·
                      rfl

theorem cell23_1282071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 2, 1, 5].length) (baseStart_1282071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1282071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1282071 prefixEnd_1282071 := by exact prefixLift 1282071
  have htrace : WordTrace (prefixWord ++ tailWord_1282071) baseStart_1282071 baseEnd_1282071 := by
    simpa [prefixWord, tailWord_1282071, baseEnd_1282071] using wordTrace_append hprefix tailTrace_1282071
  have hstable : (prefixWord ++ tailWord_1282071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282071).length < 2 ^ (prefixWord ++ tailWord_1282071).sum := by decide
  have hdescent : baseEnd_1282071 < baseStart_1282071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282074 : List Nat := [3, 1, 1, 3, 1, 3, 1, 4, 1, 1, 4]
def baseStart_1282074 : Nat := 118140960795 + 1282074 * 2 ^ 59
def prefixEnd_1282074 : Nat := 4983230072969 + 3 ^ 40 * 1282074 * 2
def baseEnd_1282074 : Nat := 658320196632522113278855

theorem tailTrace_1282074 : CollatzResearch.WordTrace tailWord_1282074 prefixEnd_1282074 658320196632522113278855 := by
  unfold tailWord_1282074
  simp only [CollatzResearch.WordTrace]
  refine ⟨11690270089318083412987319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31174053571514889101299517 11690270089318083412987319)
  ·
    refine ⟨17535405133977125119480979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11690270089318083412987319 17535405133977125119480979)
    ·
      refine ⟨26303107700965687679221469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17535405133977125119480979 26303107700965687679221469)
      ·
        refine ⟨9863665387862132879708051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26303107700965687679221469 9863665387862132879708051)
        ·
          refine ⟨14795498081793199319562077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9863665387862132879708051 14795498081793199319562077)
          ·
            refine ⟨5548311780672449744835779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14795498081793199319562077 5548311780672449744835779)
            ·
              refine ⟨8322467671008674617253669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5548311780672449744835779 8322467671008674617253669)
              ·
                refine ⟨1560462688314126490735063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8322467671008674617253669 1560462688314126490735063)
                ·
                  refine ⟨2340694032471189736102595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1560462688314126490735063 2340694032471189736102595)
                  ·
                    refine ⟨3511041048706784604153893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2340694032471189736102595 3511041048706784604153893)
                    ·
                      refine ⟨658320196632522113278855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3511041048706784604153893 658320196632522113278855)
                      ·
                        rfl

theorem cell23_1282074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 4, 1, 1, 4].length) (baseStart_1282074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1282074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1282074 prefixEnd_1282074 := by exact prefixLift 1282074
  have htrace : WordTrace (prefixWord ++ tailWord_1282074) baseStart_1282074 baseEnd_1282074 := by
    simpa [prefixWord, tailWord_1282074, baseEnd_1282074] using wordTrace_append hprefix tailTrace_1282074
  have hstable : (prefixWord ++ tailWord_1282074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282074).length < 2 ^ (prefixWord ++ tailWord_1282074).sum := by decide
  have hdescent : baseEnd_1282074 < baseStart_1282074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282094 : List Nat := [4, 1, 3, 1, 1, 2, 1, 3, 1, 1, 5]
def baseStart_1282094 : Nat := 118140960795 + 1282094 * 2 ^ 59
def prefixEnd_1282094 : Nat := 4983230072969 + 3 ^ 40 * 1282094 * 2
def baseEnd_1282094 : Nat := 658330466245612035028763

theorem tailTrace_1282094 : CollatzResearch.WordTrace tailWord_1282094 prefixEnd_1282094 658330466245612035028763 := by
  unfold tailWord_1282094
  simp only [CollatzResearch.WordTrace]
  refine ⟨5845226227149984633459667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31174539878133251378451557 5845226227149984633459667)
  ·
    refine ⟨8767839340724976950189501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5845226227149984633459667 8767839340724976950189501)
    ·
      refine ⟨3287939752771866356321063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8767839340724976950189501 3287939752771866356321063)
      ·
        refine ⟨4931909629157799534481595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3287939752771866356321063 4931909629157799534481595)
        ·
          refine ⟨7397864443736699301722393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4931909629157799534481595 7397864443736699301722393)
          ·
            refine ⟨5548398332802524476291795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7397864443736699301722393 5548398332802524476291795)
            ·
              refine ⟨8322597499203786714437693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5548398332802524476291795 8322597499203786714437693)
              ·
                refine ⟨3120974062201420017914135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8322597499203786714437693 3120974062201420017914135)
                ·
                  refine ⟨4681461093302130026871203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3120974062201420017914135 4681461093302130026871203)
                  ·
                    refine ⟨7022191639953195040306805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4681461093302130026871203 7022191639953195040306805)
                    ·
                      refine ⟨658330466245612035028763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7022191639953195040306805 658330466245612035028763)
                      ·
                        rfl

theorem cell23_1282094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_1282094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1282094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1282094 prefixEnd_1282094 := by exact prefixLift 1282094
  have htrace : WordTrace (prefixWord ++ tailWord_1282094) baseStart_1282094 baseEnd_1282094 := by
    simpa [prefixWord, tailWord_1282094, baseEnd_1282094] using wordTrace_append hprefix tailTrace_1282094
  have hstable : (prefixWord ++ tailWord_1282094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282094).length < 2 ^ (prefixWord ++ tailWord_1282094).sum := by decide
  have hdescent : baseEnd_1282094 < baseStart_1282094 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282097 : List Nat := [1, 2, 2, 3, 1, 5, 9]
def baseStart_1282097 : Nat := 118140960795 + 1282097 * 2 ^ 59
def prefixEnd_1282097 : Nat := 4983230072969 + 3 ^ 40 * 1282097 * 2
def baseEnd_1282097 : Nat := 8127555638118216336929

theorem tailTrace_1282097 : CollatzResearch.WordTrace tailWord_1282097 prefixEnd_1282097 8127555638118216336929 := by
  unfold tailWord_1282097
  simp only [CollatzResearch.WordTrace]
  refine ⟨46761919236189008580036545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31174612824126005720024363 46761919236189008580036545)
  ·
    refine ⟨35071439427141756435027409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46761919236189008580036545 35071439427141756435027409)
    ·
      refine ⟨26303579570356317326270557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35071439427141756435027409 26303579570356317326270557)
      ·
        refine ⟨9863842338883618997351459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26303579570356317326270557 9863842338883618997351459)
        ·
          refine ⟨14795763508325428496027189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9863842338883618997351459 14795763508325428496027189)
          ·
            refine ⟨1387102828905508921502549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14795763508325428496027189 1387102828905508921502549)
            ·
              refine ⟨8127555638118216336929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1387102828905508921502549 8127555638118216336929)
              ·
                rfl

theorem cell23_1282097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 9].length) (baseStart_1282097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1282097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1282097 prefixEnd_1282097 := by exact prefixLift 1282097
  have htrace : WordTrace (prefixWord ++ tailWord_1282097) baseStart_1282097 baseEnd_1282097 := by
    simpa [prefixWord, tailWord_1282097, baseEnd_1282097] using wordTrace_append hprefix tailTrace_1282097
  have hstable : (prefixWord ++ tailWord_1282097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282097).length < 2 ^ (prefixWord ++ tailWord_1282097).sum := by decide
  have hdescent : baseEnd_1282097 < baseStart_1282097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282107 : List Nat := [1, 1, 1, 1, 1, 2, 1, 6, 3, 3, 3]
def baseStart_1282107 : Nat := 118140960795 + 1282107 * 2 ^ 59
def prefixEnd_1282107 : Nat := 4983230072969 + 3 ^ 40 * 1282107 * 2
def baseEnd_1282107 : Nat := 658337141494120484166203

theorem tailTrace_1282107 : CollatzResearch.WordTrace tailWord_1282107 prefixEnd_1282107 658337141494120484166203 := by
  unfold tailWord_1282107
  simp only [CollatzResearch.WordTrace]
  refine ⟨46762283966152780287900575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31174855977435186858600383 46762283966152780287900575)
  ·
    refine ⟨70143425949229170431850863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46762283966152780287900575 70143425949229170431850863)
    ·
      refine ⟨105215138923843755647776295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70143425949229170431850863 105215138923843755647776295)
      ·
        refine ⟨157822708385765633471664443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105215138923843755647776295 157822708385765633471664443)
        ·
          refine ⟨236734062578648450207496665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157822708385765633471664443 236734062578648450207496665)
          ·
            refine ⟨177550546933986337655622499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 236734062578648450207496665 177550546933986337655622499)
            ·
              refine ⟨266325820400979506483433749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 177550546933986337655622499 266325820400979506483433749)
              ·
                refine ⟨12484022831295914366410957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 266325820400979506483433749 12484022831295914366410957)
                ·
                  refine ⟨4681508561735967887404109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12484022831295914366410957 4681508561735967887404109)
                  ·
                    refine ⟨1755565710650987957776541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4681508561735967887404109 1755565710650987957776541)
                    ·
                      refine ⟨658337141494120484166203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1755565710650987957776541 658337141494120484166203)
                      ·
                        rfl

theorem cell23_1282107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 3, 3, 3].length) (baseStart_1282107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1282107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1282107 prefixEnd_1282107 := by exact prefixLift 1282107
  have htrace : WordTrace (prefixWord ++ tailWord_1282107) baseStart_1282107 baseEnd_1282107 := by
    simpa [prefixWord, tailWord_1282107, baseEnd_1282107] using wordTrace_append hprefix tailTrace_1282107
  have hstable : (prefixWord ++ tailWord_1282107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282107).length < 2 ^ (prefixWord ++ tailWord_1282107).sum := by decide
  have hdescent : baseEnd_1282107 < baseStart_1282107 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282118 : List Nat := [6, 1, 1, 1, 1, 1, 3, 3, 2, 4]
def baseStart_1282118 : Nat := 118140960795 + 1282118 * 2 ^ 59
def prefixEnd_1282118 : Nat := 4983230072969 + 3 ^ 40 * 1282118 * 2
def baseEnd_1282118 : Nat := 219447596593773313709551

theorem tailTrace_1282118 : CollatzResearch.WordTrace tailWord_1282118 prefixEnd_1282118 219447596593773313709551 := by
  unfold tailWord_1282118
  simp only [CollatzResearch.WordTrace]
  refine ⟨1461333911534779036454719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 31175123446075286111034005 1461333911534779036454719)
  ·
    refine ⟨2192000867302168554682079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1461333911534779036454719 2192000867302168554682079)
    ·
      refine ⟨3288001300953252832023119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2192000867302168554682079 3288001300953252832023119)
      ·
        refine ⟨4932001951429879248034679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3288001300953252832023119 4932001951429879248034679)
        ·
          refine ⟨7398002927144818872052019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4932001951429879248034679 7398002927144818872052019)
          ·
            refine ⟨11097004390717228308078029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7398002927144818872052019 11097004390717228308078029)
            ·
              refine ⟨4161376646518960615529261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11097004390717228308078029 4161376646518960615529261)
              ·
                refine ⟨1560516242444610230823473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4161376646518960615529261 1560516242444610230823473)
                ·
                  refine ⟨1170387181833457673117605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1560516242444610230823473 1170387181833457673117605)
                  ·
                    refine ⟨219447596593773313709551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1170387181833457673117605 219447596593773313709551)
                    ·
                      rfl

theorem cell23_1282118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_1282118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1282118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1282118 prefixEnd_1282118 := by exact prefixLift 1282118
  have htrace : WordTrace (prefixWord ++ tailWord_1282118) baseStart_1282118 baseEnd_1282118 := by
    simpa [prefixWord, tailWord_1282118, baseEnd_1282118] using wordTrace_append hprefix tailTrace_1282118
  have hstable : (prefixWord ++ tailWord_1282118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282118).length < 2 ^ (prefixWord ++ tailWord_1282118).sum := by decide
  have hdescent : baseEnd_1282118 < baseStart_1282118 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282141 : List Nat := [1, 4, 4, 1, 1, 1, 1, 1, 3, 3, 3]
def baseStart_1282141 : Nat := 118140960795 + 1282141 * 2 ^ 59
def prefixEnd_1282141 : Nat := 4983230072969 + 3 ^ 40 * 1282141 * 2
def baseEnd_1282141 : Nat := 658354599836373351141047

theorem tailTrace_1282141 : CollatzResearch.WordTrace tailWord_1282141 prefixEnd_1282141 658354599836373351141047 := by
  unfold tailWord_1282141
  simp only [CollatzResearch.WordTrace]
  refine ⟨46763524048029604094638277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31175682698686402729758851 46763524048029604094638277)
  ·
    refine ⟨8768160759005550767744677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46763524048029604094638277 8768160759005550767744677)
    ·
      refine ⟨1644030142313540768952127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8768160759005550767744677 1644030142313540768952127)
      ·
        refine ⟨2466045213470311153428191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1644030142313540768952127 2466045213470311153428191)
        ·
          refine ⟨3699067820205466730142287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2466045213470311153428191 3699067820205466730142287)
          ·
            refine ⟨5548601730308200095213431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3699067820205466730142287 5548601730308200095213431)
            ·
              refine ⟨8322902595462300142820147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5548601730308200095213431 8322902595462300142820147)
              ·
                refine ⟨12484353893193450214230221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8322902595462300142820147 12484353893193450214230221)
                ·
                  refine ⟨4681632709947543830336333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12484353893193450214230221 4681632709947543830336333)
                  ·
                    refine ⟨1755612266230328936376125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4681632709947543830336333 1755612266230328936376125)
                    ·
                      refine ⟨658354599836373351141047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1755612266230328936376125 658354599836373351141047)
                      ·
                        rfl

theorem cell23_1282141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_1282141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1282141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1282141 prefixEnd_1282141 := by exact prefixLift 1282141
  have htrace : WordTrace (prefixWord ++ tailWord_1282141) baseStart_1282141 baseEnd_1282141 := by
    simpa [prefixWord, tailWord_1282141, baseEnd_1282141] using wordTrace_append hprefix tailTrace_1282141
  have hstable : (prefixWord ++ tailWord_1282141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282141).length < 2 ^ (prefixWord ++ tailWord_1282141).sum := by decide
  have hdescent : baseEnd_1282141 < baseStart_1282141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282142 : List Nat := [4, 4, 1, 1, 2, 1, 3, 1, 1, 1, 4]
def baseStart_1282142 : Nat := 118140960795 + 1282142 * 2 ^ 59
def prefixEnd_1282142 : Nat := 4983230072969 + 3 ^ 40 * 1282142 * 2
def baseEnd_1282142 : Nat := 658355113317027847228543

theorem tailTrace_1282142 : CollatzResearch.WordTrace tailWord_1282142 prefixEnd_1282142 658355113317027847228543 := by
  unfold tailWord_1282142
  simp only [CollatzResearch.WordTrace]
  refine ⟨5845445065128247658178085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31175707014017320843616453 5845445065128247658178085)
  ·
    refine ⟨1096020949711546435908391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5845445065128247658178085 1096020949711546435908391)
    ·
      refine ⟨1644031424567319653862587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1096020949711546435908391 1644031424567319653862587)
      ·
        refine ⟨2466047136850979480793881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1644031424567319653862587 2466047136850979480793881)
        ·
          refine ⟨1849535352638234610595411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2466047136850979480793881 1849535352638234610595411)
          ·
            refine ⟨2774303028957351915893117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1849535352638234610595411 2774303028957351915893117)
            ·
              refine ⟨1040363635859006968459919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2774303028957351915893117 1040363635859006968459919)
              ·
                refine ⟨1560545453788510452689879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1040363635859006968459919 1560545453788510452689879)
                ·
                  refine ⟨2340818180682765679034819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1560545453788510452689879 2340818180682765679034819)
                  ·
                    refine ⟨3511227271024148518552229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2340818180682765679034819 3511227271024148518552229)
                    ·
                      refine ⟨658355113317027847228543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3511227271024148518552229 658355113317027847228543)
                      ·
                        rfl

theorem cell23_1282142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_1282142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1282142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1282142 prefixEnd_1282142 := by exact prefixLift 1282142
  have htrace : WordTrace (prefixWord ++ tailWord_1282142) baseStart_1282142 baseEnd_1282142 := by
    simpa [prefixWord, tailWord_1282142, baseEnd_1282142] using wordTrace_append hprefix tailTrace_1282142
  have hstable : (prefixWord ++ tailWord_1282142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282142).length < 2 ^ (prefixWord ++ tailWord_1282142).sum := by decide
  have hdescent : baseEnd_1282142 < baseStart_1282142 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282158 : List Nat := [4, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3]
def baseStart_1282158 : Nat := 118140960795 + 1282158 * 2 ^ 59
def prefixEnd_1282158 : Nat := 4983230072969 + 3 ^ 40 * 1282158 * 2
def baseEnd_1282158 : Nat := 658363329007499784628469

theorem tailTrace_1282158 : CollatzResearch.WordTrace tailWord_1282158 prefixEnd_1282158 658363329007499784628469 := by
  unfold tailWord_1282158
  simp only [CollatzResearch.WordTrace]
  refine ⟨5845518011121001999750891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31176096059312010665338085 5845518011121001999750891)
  ·
    refine ⟨8768277016681502999626337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5845518011121001999750891 8768277016681502999626337)
    ·
      refine ⟨6576207762511127249719753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8768277016681502999626337 6576207762511127249719753)
      ·
        refine ⟨4932155821883345437289815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6576207762511127249719753 4932155821883345437289815)
        ·
          refine ⟨7398233732825018155934723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4932155821883345437289815 7398233732825018155934723)
          ·
            refine ⟨11097350599237527233902085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7398233732825018155934723 11097350599237527233902085)
            ·
              refine ⟨2080753237357036356356641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11097350599237527233902085 2080753237357036356356641)
              ·
                refine ⟨1560564928017777267267481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2080753237357036356356641 1560564928017777267267481)
                ·
                  refine ⟨1170423696013332950450611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1560564928017777267267481 1170423696013332950450611)
                  ·
                    refine ⟨1755635544019999425675917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1170423696013332950450611 1755635544019999425675917)
                    ·
                      refine ⟨658363329007499784628469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1755635544019999425675917 658363329007499784628469)
                      ·
                        rfl

theorem cell23_1282158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3].length) (baseStart_1282158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1282158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1282158 prefixEnd_1282158 := by exact prefixLift 1282158
  have htrace : WordTrace (prefixWord ++ tailWord_1282158) baseStart_1282158 baseEnd_1282158 := by
    simpa [prefixWord, tailWord_1282158, baseEnd_1282158] using wordTrace_append hprefix tailTrace_1282158
  have hstable : (prefixWord ++ tailWord_1282158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282158).length < 2 ^ (prefixWord ++ tailWord_1282158).sum := by decide
  have hdescent : baseEnd_1282158 < baseStart_1282158 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282181 : List Nat := [1, 3, 1, 1, 5, 1, 1, 3, 1, 4, 2]
def baseStart_1282181 : Nat := 118140960795 + 1282181 * 2 ^ 59
def prefixEnd_1282181 : Nat := 4983230072969 + 3 ^ 40 * 1282181 * 2
def baseEnd_1282181 : Nat := 658375139062553194640863

theorem tailTrace_1282181 : CollatzResearch.WordTrace tailWord_1282181 prefixEnd_1282181 658375139062553194640863 := by
  unfold tailWord_1282181
  simp only [CollatzResearch.WordTrace]
  refine ⟨46764982967884690926094397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31176655311923127284062931 46764982967884690926094397)
  ·
    refine ⟨17536868612956759097285399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46764982967884690926094397 17536868612956759097285399)
    ·
      refine ⟨26305302919435138645928099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17536868612956759097285399 26305302919435138645928099)
      ·
        refine ⟨39457954379152707968892149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26305302919435138645928099 39457954379152707968892149)
        ·
          refine ⟨3699183223045566372083639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39457954379152707968892149 3699183223045566372083639)
          ·
            refine ⟨5548774834568349558125459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3699183223045566372083639 5548774834568349558125459)
            ·
              refine ⟨8323162251852524337188189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5548774834568349558125459 8323162251852524337188189)
              ·
                refine ⟨3121185844444696626445571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8323162251852524337188189 3121185844444696626445571)
                ·
                  refine ⟨4681778766667044939668357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3121185844444696626445571 4681778766667044939668357)
                  ·
                    refine ⟨877833518750070926187817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4681778766667044939668357 877833518750070926187817)
                    ·
                      refine ⟨658375139062553194640863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 877833518750070926187817 658375139062553194640863)
                      ·
                        rfl

theorem cell23_1282181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 3, 1, 4, 2].length) (baseStart_1282181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1282181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1282181 prefixEnd_1282181 := by exact prefixLift 1282181
  have htrace : WordTrace (prefixWord ++ tailWord_1282181) baseStart_1282181 baseEnd_1282181 := by
    simpa [prefixWord, tailWord_1282181, baseEnd_1282181] using wordTrace_append hprefix tailTrace_1282181
  have hstable : (prefixWord ++ tailWord_1282181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282181).length < 2 ^ (prefixWord ++ tailWord_1282181).sum := by decide
  have hdescent : baseEnd_1282181 < baseStart_1282181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282194 : List Nat := [3, 2, 3, 1, 1, 1, 1, 2, 1, 4, 4]
def baseStart_1282194 : Nat := 118140960795 + 1282194 * 2 ^ 59
def prefixEnd_1282194 : Nat := 4983230072969 + 3 ^ 40 * 1282194 * 2
def baseEnd_1282194 : Nat := 658381814311061643778303

theorem tailTrace_1282194 : CollatzResearch.WordTrace tailWord_1282194 prefixEnd_1282194 658381814311061643778303 := by
  unfold tailWord_1282194
  simp only [CollatzResearch.WordTrace]
  refine ⟨11691364279209398536579409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31176971411225062764211757 11691364279209398536579409)
  ·
    refine ⟨8768523209407048902434557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11691364279209398536579409 8768523209407048902434557)
    ·
      refine ⟨3288196203527643338412959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8768523209407048902434557 3288196203527643338412959)
      ·
        refine ⟨4932294305291465007619439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3288196203527643338412959 4932294305291465007619439)
        ·
          refine ⟨7398441457937197511429159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4932294305291465007619439 7398441457937197511429159)
          ·
            refine ⟨11097662186905796267143739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7398441457937197511429159 11097662186905796267143739)
            ·
              refine ⟨16646493280358694400715609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11097662186905796267143739 16646493280358694400715609)
              ·
                refine ⟨12484869960269020800536707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16646493280358694400715609 12484869960269020800536707)
                ·
                  refine ⟨18727304940403531200805061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12484869960269020800536707 18727304940403531200805061)
                  ·
                    refine ⟨3511369676325662100150949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18727304940403531200805061 3511369676325662100150949)
                    ·
                      refine ⟨658381814311061643778303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3511369676325662100150949 658381814311061643778303)
                      ·
                        rfl

theorem cell23_1282194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_1282194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1282194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1282194 prefixEnd_1282194 := by exact prefixLift 1282194
  have htrace : WordTrace (prefixWord ++ tailWord_1282194) baseStart_1282194 baseEnd_1282194 := by
    simpa [prefixWord, tailWord_1282194, baseEnd_1282194] using wordTrace_append hprefix tailTrace_1282194
  have hstable : (prefixWord ++ tailWord_1282194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282194).length < 2 ^ (prefixWord ++ tailWord_1282194).sum := by decide
  have hdescent : baseEnd_1282194 < baseStart_1282194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282202 : List Nat := [3, 1, 1, 5, 2, 2, 2, 1, 1, 3, 2]
def baseStart_1282202 : Nat := 118140960795 + 1282202 * 2 ^ 59
def prefixEnd_1282202 : Nat := 4983230072969 + 3 ^ 40 * 1282202 * 2
def baseEnd_1282202 : Nat := 658385922156297612478267

theorem tailTrace_1282202 : CollatzResearch.WordTrace tailWord_1282202 prefixEnd_1282202 658385922156297612478267 := by
  unfold tailWord_1282202
  simp only [CollatzResearch.WordTrace]
  refine ⟨11691437225202152878152215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31177165933872407675072573 11691437225202152878152215)
  ·
    refine ⟨17537155837803229317228323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11691437225202152878152215 17537155837803229317228323)
    ·
      refine ⟨26305733756704843975842485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17537155837803229317228323 26305733756704843975842485)
      ·
        refine ⟨2466162539691079122735233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26305733756704843975842485 2466162539691079122735233)
        ·
          refine ⟨1849621904768309342051425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2466162539691079122735233 1849621904768309342051425)
          ·
            refine ⟨1387216428576232006538569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1849621904768309342051425 1387216428576232006538569)
            ·
              refine ⟨1040412321432174004903927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1387216428576232006538569 1040412321432174004903927)
              ·
                refine ⟨1560618482148261007355891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1040412321432174004903927 1560618482148261007355891)
                ·
                  refine ⟨2340927723222391511033837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1560618482148261007355891 2340927723222391511033837)
                  ·
                    refine ⟨877847896208396816637689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2340927723222391511033837 877847896208396816637689)
                    ·
                      refine ⟨658385922156297612478267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 877847896208396816637689 658385922156297612478267)
                      ·
                        rfl

theorem cell23_1282202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_1282202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1282202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1282202 prefixEnd_1282202 := by exact prefixLift 1282202
  have htrace : WordTrace (prefixWord ++ tailWord_1282202) baseStart_1282202 baseEnd_1282202 := by
    simpa [prefixWord, tailWord_1282202, baseEnd_1282202] using wordTrace_append hprefix tailTrace_1282202
  have hstable : (prefixWord ++ tailWord_1282202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282202).length < 2 ^ (prefixWord ++ tailWord_1282202).sum := by decide
  have hdescent : baseEnd_1282202 < baseStart_1282202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282215 : List Nat := [1, 1, 6, 2, 2, 1, 1, 1, 4, 2, 2]
def baseStart_1282215 : Nat := 118140960795 + 1282215 * 2 ^ 59
def prefixEnd_1282215 : Nat := 4983230072969 + 3 ^ 40 * 1282215 * 2
def baseEnd_1282215 : Nat := 658392597404806061615707

theorem tailTrace_1282215 : CollatzResearch.WordTrace tailWord_1282215 prefixEnd_1282215 658392597404806061615707 := by
  unfold tailWord_1282215
  simp only [CollatzResearch.WordTrace]
  refine ⟨46766223049761514732832099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31177482033174343155221399 46766223049761514732832099)
  ·
    refine ⟨70149334574642272099248149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46766223049761514732832099 70149334574642272099248149)
    ·
      refine ⟨3288250058186356504652257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 70149334574642272099248149 3288250058186356504652257)
      ·
        refine ⟨2466187543639767378489193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3288250058186356504652257 2466187543639767378489193)
        ·
          refine ⟨1849640657729825533866895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2466187543639767378489193 1849640657729825533866895)
          ·
            refine ⟨2774460986594738300800343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1849640657729825533866895 2774460986594738300800343)
            ·
              refine ⟨4161691479892107451200515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2774460986594738300800343 4161691479892107451200515)
              ·
                refine ⟨6242537219838161176800773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4161691479892107451200515 6242537219838161176800773)
                ·
                  refine ⟨1170475728719655220650145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6242537219838161176800773 1170475728719655220650145)
                  ·
                    refine ⟨877856796539741415487609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1170475728719655220650145 877856796539741415487609)
                    ·
                      refine ⟨658392597404806061615707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 877856796539741415487609 658392597404806061615707)
                      ·
                        rfl

theorem cell23_1282215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_1282215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1282215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1282215 prefixEnd_1282215 := by exact prefixLift 1282215
  have htrace : WordTrace (prefixWord ++ tailWord_1282215) baseStart_1282215 baseEnd_1282215 := by
    simpa [prefixWord, tailWord_1282215, baseEnd_1282215] using wordTrace_append hprefix tailTrace_1282215
  have hstable : (prefixWord ++ tailWord_1282215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282215).length < 2 ^ (prefixWord ++ tailWord_1282215).sum := by decide
  have hdescent : baseEnd_1282215 < baseStart_1282215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282221 : List Nat := [1, 5, 2, 1, 2, 2, 2, 1, 7]
def baseStart_1282221 : Nat := 118140960795 + 1282221 * 2 ^ 59
def prefixEnd_1282221 : Nat := 4983230072969 + 3 ^ 40 * 1282221 * 2
def baseEnd_1282221 : Nat := 73155075365414782015631

theorem tailTrace_1282221 : CollatzResearch.WordTrace tailWord_1282221 prefixEnd_1282221 73155075365414782015631 := by
  unfold tailWord_1282221
  simp only [CollatzResearch.WordTrace]
  refine ⟨46766441887739777757550517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31177627925159851838367011 46766441887739777757550517)
  ·
    refine ⟨4384353926975604164770361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46766441887739777757550517 4384353926975604164770361)
    ·
      refine ⟨3288265445231703123577771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4384353926975604164770361 3288265445231703123577771)
      ·
        refine ⟨4932398167847554685366657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3288265445231703123577771 4932398167847554685366657)
        ·
          refine ⟨3699298625885666014024993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4932398167847554685366657 3699298625885666014024993)
          ·
            refine ⟨2774473969414249510518745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3699298625885666014024993 2774473969414249510518745)
            ·
              refine ⟨2080855477060687132889059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2774473969414249510518745 2080855477060687132889059)
              ·
                refine ⟨3121283215591030699333589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2080855477060687132889059 3121283215591030699333589)
                ·
                  refine ⟨73155075365414782015631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3121283215591030699333589 73155075365414782015631)
                  ·
                    rfl

theorem cell23_1282221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 1, 7].length) (baseStart_1282221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1282221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1282221 prefixEnd_1282221 := by exact prefixLift 1282221
  have htrace : WordTrace (prefixWord ++ tailWord_1282221) baseStart_1282221 baseEnd_1282221 := by
    simpa [prefixWord, tailWord_1282221, baseEnd_1282221] using wordTrace_append hprefix tailTrace_1282221
  have hstable : (prefixWord ++ tailWord_1282221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282221).length < 2 ^ (prefixWord ++ tailWord_1282221).sum := by decide
  have hdescent : baseEnd_1282221 < baseStart_1282221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282227 : List Nat := [1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 7]
def baseStart_1282227 : Nat := 118140960795 + 1282227 * 2 ^ 59
def prefixEnd_1282227 : Nat := 4983230072969 + 3 ^ 40 * 1282227 * 2
def baseEnd_1282227 : Nat := 658398759172660014665651

theorem tailTrace_1282227 : CollatzResearch.WordTrace tailWord_1282227 prefixEnd_1282227 658398759172660014665651 := by
  unfold tailWord_1282227
  simp only [CollatzResearch.WordTrace]
  refine ⟨46766660725718040782268935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31177773817145360521512623 46766660725718040782268935)
  ·
    refine ⟨70149991088577061173403403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46766660725718040782268935 70149991088577061173403403)
    ·
      refine ⟨105224986632865591760105105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70149991088577061173403403 105224986632865591760105105)
      ·
        refine ⟨78918739974649193820078829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105224986632865591760105105 78918739974649193820078829)
        ·
          refine ⟨29594527490493447682529561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78918739974649193820078829 29594527490493447682529561)
          ·
            refine ⟨22195895617870085761897171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29594527490493447682529561 22195895617870085761897171)
            ·
              refine ⟨33293843426805128642845757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22195895617870085761897171 33293843426805128642845757)
              ·
                refine ⟨12485191285051923241067159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33293843426805128642845757 12485191285051923241067159)
                ·
                  refine ⟨18727786927577884861600739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12485191285051923241067159 18727786927577884861600739)
                  ·
                    refine ⟨28091680391366827292401109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18727786927577884861600739 28091680391366827292401109)
                    ·
                      refine ⟨658398759172660014665651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 28091680391366827292401109 658398759172660014665651)
                      ·
                        rfl

theorem cell23_1282227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 7].length) (baseStart_1282227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1282227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1282227 prefixEnd_1282227 := by exact prefixLift 1282227
  have htrace : WordTrace (prefixWord ++ tailWord_1282227) baseStart_1282227 baseEnd_1282227 := by
    simpa [prefixWord, tailWord_1282227, baseEnd_1282227] using wordTrace_append hprefix tailTrace_1282227
  have hstable : (prefixWord ++ tailWord_1282227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282227).length < 2 ^ (prefixWord ++ tailWord_1282227).sum := by decide
  have hdescent : baseEnd_1282227 < baseStart_1282227 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282304 : List Nat := [2, 1, 1, 2, 1, 1, 4, 1, 2, 5, 3]
def baseStart_1282304 : Nat := 118140960795 + 1282304 * 2 ^ 59
def prefixEnd_1282304 : Nat := 4983230072969 + 3 ^ 40 * 1282304 * 2
def baseEnd_1282304 : Nat := 658438297183056213402797

theorem tailTrace_1282304 : CollatzResearch.WordTrace tailWord_1282304 prefixEnd_1282304 658438297183056213402797 := by
  unfold tailWord_1282304
  simp only [CollatzResearch.WordTrace]
  refine ⟨23384734573219541466410983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31179646097626055288547977 23384734573219541466410983)
  ·
    refine ⟨35077101859829312199616475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23384734573219541466410983 35077101859829312199616475)
    ·
      refine ⟨52615652789743968299424713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35077101859829312199616475 52615652789743968299424713)
      ·
        refine ⟨39461739592307976224568535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52615652789743968299424713 39461739592307976224568535)
        ·
          refine ⟨59192609388461964336852803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39461739592307976224568535 59192609388461964336852803)
          ·
            refine ⟨88788914082692946505279205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59192609388461964336852803 88788914082692946505279205)
            ·
              refine ⟨16647921390504927469739851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 88788914082692946505279205 16647921390504927469739851)
              ·
                refine ⟨24971882085757391204609777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16647921390504927469739851 24971882085757391204609777)
                ·
                  refine ⟨18728911564318043403457333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24971882085757391204609777 18728911564318043403457333)
                  ·
                    refine ⟨1755835459154816569074125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18728911564318043403457333 1755835459154816569074125)
                    ·
                      refine ⟨658438297183056213402797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1755835459154816569074125 658438297183056213402797)
                      ·
                        rfl

theorem cell23_1282304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 2, 5, 3].length) (baseStart_1282304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1282304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1282304 prefixEnd_1282304 := by exact prefixLift 1282304
  have htrace : WordTrace (prefixWord ++ tailWord_1282304) baseStart_1282304 baseEnd_1282304 := by
    simpa [prefixWord, tailWord_1282304, baseEnd_1282304] using wordTrace_append hprefix tailTrace_1282304
  have hstable : (prefixWord ++ tailWord_1282304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282304).length < 2 ^ (prefixWord ++ tailWord_1282304).sum := by decide
  have hdescent : baseEnd_1282304 < baseStart_1282304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282384 : List Nat := [2, 1, 1, 1, 1, 7, 10]
def baseStart_1282384 : Nat := 118140960795 + 1282384 * 2 ^ 59
def prefixEnd_1282384 : Nat := 4983230072969 + 3 ^ 40 * 1282384 * 2
def baseEnd_1282384 : Nat := 8129375007844640745709

theorem tailTrace_1282384 : CollatzResearch.WordTrace tailWord_1282384 prefixEnd_1282384 8129375007844640745709 := by
  unfold tailWord_1282384
  simp only [CollatzResearch.WordTrace]
  refine ⟨23386193493074628297867103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31181591324099504397156137 23386193493074628297867103)
  ·
    refine ⟨35079290239611942446800655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23386193493074628297867103 35079290239611942446800655)
    ·
      refine ⟨52618935359417913670200983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35079290239611942446800655 52618935359417913670200983)
      ·
        refine ⟨78928403039126870505301475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52618935359417913670200983 78928403039126870505301475)
        ·
          refine ⟨118392604558690305757952213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78928403039126870505301475 118392604558690305757952213)
          ·
            refine ⟨2774826669344304041202005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 118392604558690305757952213 2774826669344304041202005)
            ·
              refine ⟨8129375007844640745709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2774826669344304041202005 8129375007844640745709)
              ·
                rfl

theorem cell23_1282384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 10].length) (baseStart_1282384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1282384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1282384 prefixEnd_1282384 := by exact prefixLift 1282384
  have htrace : WordTrace (prefixWord ++ tailWord_1282384) baseStart_1282384 baseEnd_1282384 := by
    simpa [prefixWord, tailWord_1282384, baseEnd_1282384] using wordTrace_append hprefix tailTrace_1282384
  have hstable : (prefixWord ++ tailWord_1282384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282384).length < 2 ^ (prefixWord ++ tailWord_1282384).sum := by decide
  have hdescent : baseEnd_1282384 < baseStart_1282384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282388 : List Nat := [2, 4, 1, 1, 2, 3, 1, 1, 4, 4]
def baseStart_1282388 : Nat := 118140960795 + 1282388 * 2 ^ 59
def prefixEnd_1282388 : Nat := 4983230072969 + 3 ^ 40 * 1282388 * 2
def baseEnd_1282388 : Nat := 219493809852677961584137

theorem tailTrace_1282388 : CollatzResearch.WordTrace tailWord_1282388 prefixEnd_1282388 219493809852677961584137 := by
  unfold tailWord_1282388
  simp only [CollatzResearch.WordTrace]
  refine ⟨23386266439067382639439909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31181688585423176852586545 23386266439067382639439909)
  ·
    refine ⟨4384924957325134244894983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23386266439067382639439909 4384924957325134244894983)
    ·
      refine ⟨6577387435987701367342475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4384924957325134244894983 6577387435987701367342475)
      ·
        refine ⟨9866081153981552051013713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6577387435987701367342475 9866081153981552051013713)
        ·
          refine ⟨7399560865486164038260285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9866081153981552051013713 7399560865486164038260285)
          ·
            refine ⟨2774835324557311514347607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7399560865486164038260285 2774835324557311514347607)
            ·
              refine ⟨4162252986835967271521411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2774835324557311514347607 4162252986835967271521411)
              ·
                refine ⟨6243379480253950907282117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4162252986835967271521411 6243379480253950907282117)
                ·
                  refine ⟨1170633652547615795115397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6243379480253950907282117 1170633652547615795115397)
                  ·
                    refine ⟨219493809852677961584137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1170633652547615795115397 219493809852677961584137)
                    ·
                      rfl

theorem cell23_1282388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 1, 4, 4].length) (baseStart_1282388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1282388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1282388 prefixEnd_1282388 := by exact prefixLift 1282388
  have htrace : WordTrace (prefixWord ++ tailWord_1282388) baseStart_1282388 baseEnd_1282388 := by
    simpa [prefixWord, tailWord_1282388, baseEnd_1282388] using wordTrace_append hprefix tailTrace_1282388
  have hstable : (prefixWord ++ tailWord_1282388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282388).length < 2 ^ (prefixWord ++ tailWord_1282388).sum := by decide
  have hdescent : baseEnd_1282388 < baseStart_1282388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282394 : List Nat := [3, 1, 1, 2, 1, 2, 1, 1, 2, 2, 7]
def baseStart_1282394 : Nat := 118140960795 + 1282394 * 2 ^ 59
def prefixEnd_1282394 : Nat := 4983230072969 + 3 ^ 40 * 1282394 * 2
def baseEnd_1282394 : Nat := 658484510441960861277383

theorem tailTrace_1282394 : CollatzResearch.WordTrace tailWord_1282394 prefixEnd_1282394 658484510441960861277383 := by
  unfold tailWord_1282394
  simp only [CollatzResearch.WordTrace]
  refine ⟨11693187929028257075899559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31181834477408685535732157 11693187929028257075899559)
  ·
    refine ⟨17539781893542385613849339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11693187929028257075899559 17539781893542385613849339)
    ·
      refine ⟨26309672840313578420774009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17539781893542385613849339 26309672840313578420774009)
      ·
        refine ⟨19732254630235183815580507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26309672840313578420774009 19732254630235183815580507)
        ·
          refine ⟨29598381945352775723370761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19732254630235183815580507 29598381945352775723370761)
          ·
            refine ⟨22198786459014581792528071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29598381945352775723370761 22198786459014581792528071)
            ·
              refine ⟨33298179688521872688792107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22198786459014581792528071 33298179688521872688792107)
              ·
                refine ⟨49947269532782809033188161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33298179688521872688792107 49947269532782809033188161)
                ·
                  refine ⟨37460452149587106774891121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49947269532782809033188161 37460452149587106774891121)
                  ·
                    refine ⟨28095339112190330081168341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37460452149587106774891121 28095339112190330081168341)
                    ·
                      refine ⟨658484510441960861277383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 28095339112190330081168341 658484510441960861277383)
                      ·
                        rfl

theorem cell23_1282394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 2, 2, 7].length) (baseStart_1282394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1282394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1282394 prefixEnd_1282394 := by exact prefixLift 1282394
  have htrace : WordTrace (prefixWord ++ tailWord_1282394) baseStart_1282394 baseEnd_1282394 := by
    simpa [prefixWord, tailWord_1282394, baseEnd_1282394] using wordTrace_append hprefix tailTrace_1282394
  have hstable : (prefixWord ++ tailWord_1282394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282394).length < 2 ^ (prefixWord ++ tailWord_1282394).sum := by decide
  have hdescent : baseEnd_1282394 < baseStart_1282394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282405 : List Nat := [1, 3, 1, 3, 1, 4, 3, 1, 2, 4]
def baseStart_1282405 : Nat := 118140960795 + 1282405 * 2 ^ 59
def prefixEnd_1282405 : Nat := 4983230072969 + 3 ^ 40 * 1282405 * 2
def baseEnd_1282405 : Nat := 219496719576386772746611

theorem tailTrace_1282405 : CollatzResearch.WordTrace tailWord_1282405 prefixEnd_1282405 219496719576386772746611 := by
  unfold tailWord_1282405
  simp only [CollatzResearch.WordTrace]
  refine ⟨46773152919073177182248669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31182101946048784788165779 46773152919073177182248669)
  ·
    refine ⟨17539932344652441443343251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46773152919073177182248669 17539932344652441443343251)
    ·
      refine ⟨26309898516978662165014877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17539932344652441443343251 26309898516978662165014877)
      ·
        refine ⟨9866211943866998311880579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26309898516978662165014877 9866211943866998311880579)
        ·
          refine ⟨14799317915800497467820869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9866211943866998311880579 14799317915800497467820869)
          ·
            refine ⟨2774872109212593275216413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14799317915800497467820869 2774872109212593275216413)
            ·
              refine ⟨1040577040954722478206155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2774872109212593275216413 1040577040954722478206155)
              ·
                refine ⟨1560865561432083717309233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1040577040954722478206155 1560865561432083717309233)
                ·
                  refine ⟨1170649171074062787981925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1560865561432083717309233 1170649171074062787981925)
                  ·
                    refine ⟨219496719576386772746611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1170649171074062787981925 219496719576386772746611)
                    ·
                      rfl

theorem cell23_1282405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 3, 1, 2, 4].length) (baseStart_1282405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1282405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1282405 prefixEnd_1282405 := by exact prefixLift 1282405
  have htrace : WordTrace (prefixWord ++ tailWord_1282405) baseStart_1282405 baseEnd_1282405 := by
    simpa [prefixWord, tailWord_1282405, baseEnd_1282405] using wordTrace_append hprefix tailTrace_1282405
  have hstable : (prefixWord ++ tailWord_1282405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282405).length < 2 ^ (prefixWord ++ tailWord_1282405).sum := by decide
  have hdescent : baseEnd_1282405 < baseStart_1282405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282408 : List Nat := [2, 1, 4, 2, 2, 1, 3, 1, 1, 2, 4]
def baseStart_1282408 : Nat := 118140960795 + 1282408 * 2 ^ 59
def prefixEnd_1282408 : Nat := 4983230072969 + 3 ^ 40 * 1282408 * 2
def baseEnd_1282408 : Nat := 658491699171123806502319

theorem tailTrace_1282408 : CollatzResearch.WordTrace tailWord_1282408 prefixEnd_1282408 658491699171123806502319 := by
  unfold tailWord_1282408
  simp only [CollatzResearch.WordTrace]
  refine ⟨23386631169031154347303939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31182174892041539129738585 23386631169031154347303939)
  ·
    refine ⟨35079946753546731520955909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23386631169031154347303939 35079946753546731520955909)
    ·
      refine ⟨6577490016290012160179233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35079946753546731520955909 6577490016290012160179233)
      ·
        refine ⟨4933117512217509120134425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6577490016290012160179233 4933117512217509120134425)
        ·
          refine ⟨3699838134163131840100819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4933117512217509120134425 3699838134163131840100819)
          ·
            refine ⟨5549757201244697760151229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3699838134163131840100819 5549757201244697760151229)
            ·
              refine ⟨2081158950466761660056711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5549757201244697760151229 2081158950466761660056711)
              ·
                refine ⟨3121738425700142490085067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2081158950466761660056711 3121738425700142490085067)
                ·
                  refine ⟨4682607638550213735127601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3121738425700142490085067 4682607638550213735127601)
                  ·
                    refine ⟨3511955728912660301345701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4682607638550213735127601 3511955728912660301345701)
                    ·
                      refine ⟨658491699171123806502319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3511955728912660301345701 658491699171123806502319)
                      ·
                        rfl

theorem cell23_1282408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_1282408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1282408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1282408 prefixEnd_1282408 := by exact prefixLift 1282408
  have htrace : WordTrace (prefixWord ++ tailWord_1282408) baseStart_1282408 baseEnd_1282408 := by
    simpa [prefixWord, tailWord_1282408, baseEnd_1282408] using wordTrace_append hprefix tailTrace_1282408
  have hstable : (prefixWord ++ tailWord_1282408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282408).length < 2 ^ (prefixWord ++ tailWord_1282408).sum := by decide
  have hdescent : baseEnd_1282408 < baseStart_1282408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282418 : List Nat := [3, 2, 1, 2, 1, 5, 2, 7]
def baseStart_1282418 : Nat := 118140960795 + 1282418 * 2 ^ 59
def prefixEnd_1282418 : Nat := 4983230072969 + 3 ^ 40 * 1282418 * 2
def baseEnd_1282418 : Nat := 24388771628802546939899

theorem tailTrace_1282418 : CollatzResearch.WordTrace tailWord_1282418 prefixEnd_1282418 24388771628802546939899 := by
  unfold tailWord_1282418
  simp only [CollatzResearch.WordTrace]
  refine ⟨11693406767006520100617977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31182418045350720268314605 11693406767006520100617977)
  ·
    refine ⟨8770055075254890075463483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11693406767006520100617977 8770055075254890075463483)
    ·
      refine ⟨13155082612882335113195225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8770055075254890075463483 13155082612882335113195225)
      ·
        refine ⟨9866311959661751334896419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13155082612882335113195225 9866311959661751334896419)
        ·
          refine ⟨14799467939492627002344629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9866311959661751334896419 14799467939492627002344629)
          ·
            refine ⟨1387450119327433781469809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14799467939492627002344629 1387450119327433781469809)
            ·
              refine ⟨1040587589495575336102357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1387450119327433781469809 1040587589495575336102357)
              ·
                refine ⟨24388771628802546939899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1040587589495575336102357 24388771628802546939899)
                ·
                  rfl

theorem cell23_1282418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 2, 7].length) (baseStart_1282418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1282418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1282418 prefixEnd_1282418 := by exact prefixLift 1282418
  have htrace : WordTrace (prefixWord ++ tailWord_1282418) baseStart_1282418 baseEnd_1282418 := by
    simpa [prefixWord, tailWord_1282418, baseEnd_1282418] using wordTrace_append hprefix tailTrace_1282418
  have hstable : (prefixWord ++ tailWord_1282418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282418).length < 2 ^ (prefixWord ++ tailWord_1282418).sum := by decide
  have hdescent : baseEnd_1282418 < baseStart_1282418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282429 : List Nat := [1, 4, 1, 1, 2, 5, 1, 3, 1, 2, 2]
def baseStart_1282429 : Nat := 118140960795 + 1282429 * 2 ^ 59
def prefixEnd_1282429 : Nat := 4983230072969 + 3 ^ 40 * 1282429 * 2
def baseEnd_1282429 : Nat := 658502482264868224339723

theorem tailTrace_1282429 : CollatzResearch.WordTrace tailWord_1282429 prefixEnd_1282429 658502482264868224339723 := by
  unfold tailWord_1282429
  simp only [CollatzResearch.WordTrace]
  refine ⟨46774028270986229281122341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31182685513990819520748227 46774028270986229281122341)
  ·
    refine ⟨8770130300809917990210439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46774028270986229281122341 8770130300809917990210439)
    ·
      refine ⟨13155195451214876985315659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8770130300809917990210439 13155195451214876985315659)
      ·
        refine ⟨19732793176822315477973489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13155195451214876985315659 19732793176822315477973489)
        ·
          refine ⟨14799594882616736608480117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19732793176822315477973489 14799594882616736608480117)
          ·
            refine ⟨1387462020245319057045011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14799594882616736608480117 1387462020245319057045011)
            ·
              refine ⟨2081193030367978585567517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1387462020245319057045011 2081193030367978585567517)
              ·
                refine ⟨780447386387991969587819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2081193030367978585567517 780447386387991969587819)
                ·
                  refine ⟨1170671079581987954381729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 780447386387991969587819 1170671079581987954381729)
                  ·
                    refine ⟨878003309686490965786297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1170671079581987954381729 878003309686490965786297)
                    ·
                      refine ⟨658502482264868224339723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 878003309686490965786297 658502482264868224339723)
                      ·
                        rfl

theorem cell23_1282429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 3, 1, 2, 2].length) (baseStart_1282429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1282429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1282429 prefixEnd_1282429 := by exact prefixLift 1282429
  have htrace : WordTrace (prefixWord ++ tailWord_1282429) baseStart_1282429 baseEnd_1282429 := by
    simpa [prefixWord, tailWord_1282429, baseEnd_1282429] using wordTrace_append hprefix tailTrace_1282429
  have hstable : (prefixWord ++ tailWord_1282429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282429).length < 2 ^ (prefixWord ++ tailWord_1282429).sum := by decide
  have hdescent : baseEnd_1282429 < baseStart_1282429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282446 : List Nat := [4, 1, 1, 4, 1, 2, 3, 2, 1, 2, 2]
def baseStart_1282446 : Nat := 118140960795 + 1282446 * 2 ^ 59
def prefixEnd_1282446 : Nat := 4983230072969 + 3 ^ 40 * 1282446 * 2
def baseEnd_1282446 : Nat := 658511211435994657827145

theorem tailTrace_1282446 : CollatzResearch.WordTrace tailWord_1282446 prefixEnd_1282446 658511211435994657827145 := by
  unfold tailWord_1282446
  simp only [CollatzResearch.WordTrace]
  refine ⟨5846831038990580148061399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31183098874616427456327461 5846831038990580148061399)
  ·
    refine ⟨8770246558485870222092099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5846831038990580148061399 8770246558485870222092099)
    ·
      refine ⟨13155369837728805333138149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8770246558485870222092099 13155369837728805333138149)
      ·
        refine ⟨2466631844574150999963403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13155369837728805333138149 2466631844574150999963403)
        ·
          refine ⟨3699947766861226499945105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2466631844574150999963403 3699947766861226499945105)
          ·
            refine ⟨2774960825145919874958829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3699947766861226499945105 2774960825145919874958829)
            ·
              refine ⟨1040610309429719953109561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2774960825145919874958829 1040610309429719953109561)
              ·
                refine ⟨780457732072289964832171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1040610309429719953109561 780457732072289964832171)
                ·
                  refine ⟨1170686598108434947248257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 780457732072289964832171 1170686598108434947248257)
                  ·
                    refine ⟨878014948581326210436193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1170686598108434947248257 878014948581326210436193)
                    ·
                      refine ⟨658511211435994657827145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 878014948581326210436193 658511211435994657827145)
                      ·
                        rfl

theorem cell23_1282446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 3, 2, 1, 2, 2].length) (baseStart_1282446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1282446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1282446 prefixEnd_1282446 := by exact prefixLift 1282446
  have htrace : WordTrace (prefixWord ++ tailWord_1282446) baseStart_1282446 baseEnd_1282446 := by
    simpa [prefixWord, tailWord_1282446, baseEnd_1282446] using wordTrace_append hprefix tailTrace_1282446
  have hstable : (prefixWord ++ tailWord_1282446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282446).length < 2 ^ (prefixWord ++ tailWord_1282446).sum := by decide
  have hdescent : baseEnd_1282446 < baseStart_1282446 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282472 : List Nat := [2, 1, 6, 1, 1, 2, 1, 1, 3, 3, 2]
def baseStart_1282472 : Nat := 118140960795 + 1282472 * 2 ^ 59
def prefixEnd_1282472 : Nat := 4983230072969 + 3 ^ 40 * 1282472 * 2
def baseEnd_1282472 : Nat := 658524561933011556102025

theorem tailTrace_1282472 : CollatzResearch.WordTrace tailWord_1282472 prefixEnd_1282472 658524561933011556102025 := by
  unfold tailWord_1282472
  simp only [CollatzResearch.WordTrace]
  refine ⟨23387798304915223812468835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31183731073220298416625113 23387798304915223812468835)
  ·
    refine ⟨35081697457372835718703253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23387798304915223812468835 35081697457372835718703253)
    ·
      refine ⟨1644454568314351674314215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 35081697457372835718703253 1644454568314351674314215)
      ·
        refine ⟨2466681852471527511471323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1644454568314351674314215 2466681852471527511471323)
        ·
          refine ⟨3700022778707291267206985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2466681852471527511471323 3700022778707291267206985)
          ·
            refine ⟨2775017084030468450405239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3700022778707291267206985 2775017084030468450405239)
            ·
              refine ⟨4162525626045702675607859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2775017084030468450405239 4162525626045702675607859)
              ·
                refine ⟨6243788439068554013411789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4162525626045702675607859 6243788439068554013411789)
                ·
                  refine ⟨2341420664650707755029421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6243788439068554013411789 2341420664650707755029421)
                  ·
                    refine ⟨878032749244015408136033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2341420664650707755029421 878032749244015408136033)
                    ·
                      refine ⟨658524561933011556102025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 878032749244015408136033 658524561933011556102025)
                      ·
                        rfl

theorem cell23_1282472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_1282472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1282472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1282472 prefixEnd_1282472 := by exact prefixLift 1282472
  have htrace : WordTrace (prefixWord ++ tailWord_1282472) baseStart_1282472 baseEnd_1282472 := by
    simpa [prefixWord, tailWord_1282472, baseEnd_1282472] using wordTrace_append hprefix tailTrace_1282472
  have hstable : (prefixWord ++ tailWord_1282472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282472).length < 2 ^ (prefixWord ++ tailWord_1282472).sum := by decide
  have hdescent : baseEnd_1282472 < baseStart_1282472 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282497 : List Nat := [1, 2, 7, 1, 2, 1, 2, 2, 1, 2, 2]
def baseStart_1282497 : Nat := 118140960795 + 1282497 * 2 ^ 59
def prefixEnd_1282497 : Nat := 4983230072969 + 3 ^ 40 * 1282497 * 2
def baseEnd_1282497 : Nat := 658537398949373958289411

theorem tailTrace_1282497 : CollatzResearch.WordTrace tailWord_1282497 prefixEnd_1282497 658537398949373958289411 := by
  unfold tailWord_1282497
  simp only [CollatzResearch.WordTrace]
  refine ⟨46776508434739876894597745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31184338956493251263065163 46776508434739876894597745)
  ·
    refine ⟨35082381326054907670948309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46776508434739876894597745 35082381326054907670948309)
    ·
      refine ⟨822243312329411898537851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 35082381326054907670948309 822243312329411898537851)
      ·
        refine ⟨1233364968494117847806777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 822243312329411898537851 1233364968494117847806777)
        ·
          refine ⟨925023726370588385855083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1233364968494117847806777 925023726370588385855083)
          ·
            refine ⟨1387535589555882578782625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 925023726370588385855083 1387535589555882578782625)
            ·
              refine ⟨1040651692166911934086969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1387535589555882578782625 1040651692166911934086969)
              ·
                refine ⟨780488769125183950565227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1040651692166911934086969 780488769125183950565227)
                ·
                  refine ⟨1170733153687775925847841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 780488769125183950565227 1170733153687775925847841)
                  ·
                    refine ⟨878049865265831944385881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1170733153687775925847841 878049865265831944385881)
                    ·
                      refine ⟨658537398949373958289411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 878049865265831944385881 658537398949373958289411)
                      ·
                        rfl

theorem cell23_1282497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_1282497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1282497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1282497 prefixEnd_1282497 := by exact prefixLift 1282497
  have htrace : WordTrace (prefixWord ++ tailWord_1282497) baseStart_1282497 baseEnd_1282497 := by
    simpa [prefixWord, tailWord_1282497, baseEnd_1282497] using wordTrace_append hprefix tailTrace_1282497
  have hstable : (prefixWord ++ tailWord_1282497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282497).length < 2 ^ (prefixWord ++ tailWord_1282497).sum := by decide
  have hdescent : baseEnd_1282497 < baseStart_1282497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282501 : List Nat := [1, 3, 1, 1, 1, 1, 1, 1, 5, 5, 3]
def baseStart_1282501 : Nat := 118140960795 + 1282501 * 2 ^ 59
def prefixEnd_1282501 : Nat := 4983230072969 + 3 ^ 40 * 1282501 * 2
def baseEnd_1282501 : Nat := 658539452871991942639391

theorem tailTrace_1282501 : CollatzResearch.WordTrace tailWord_1282501 prefixEnd_1282501 658539452871991942639391 := by
  unfold tailWord_1282501
  simp only [CollatzResearch.WordTrace]
  refine ⟨46776654326725385577743357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31184436217816923718495571 46776654326725385577743357)
  ·
    refine ⟨17541245372522019591653759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46776654326725385577743357 17541245372522019591653759)
    ·
      refine ⟨26311868058783029387480639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17541245372522019591653759 26311868058783029387480639)
      ·
        refine ⟨39467802088174544081220959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26311868058783029387480639 39467802088174544081220959)
        ·
          refine ⟨59201703132261816121831439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39467802088174544081220959 59201703132261816121831439)
          ·
            refine ⟨88802554698392724182747159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59201703132261816121831439 88802554698392724182747159)
            ·
              refine ⟨133203832047589086274120739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88802554698392724182747159 133203832047589086274120739)
              ·
                refine ⟨199805748071383629411181109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 133203832047589086274120739 199805748071383629411181109)
                ·
                  refine ⟨18731788881692215257298229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 199805748071383629411181109 18731788881692215257298229)
                  ·
                    refine ⟨1756105207658645180371709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18731788881692215257298229 1756105207658645180371709)
                    ·
                      refine ⟨658539452871991942639391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1756105207658645180371709 658539452871991942639391)
                      ·
                        rfl

theorem cell23_1282501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 5, 3].length) (baseStart_1282501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1282501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1282501 prefixEnd_1282501 := by exact prefixLift 1282501
  have htrace : WordTrace (prefixWord ++ tailWord_1282501) baseStart_1282501 baseEnd_1282501 := by
    simpa [prefixWord, tailWord_1282501, baseEnd_1282501] using wordTrace_append hprefix tailTrace_1282501
  have hstable : (prefixWord ++ tailWord_1282501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282501).length < 2 ^ (prefixWord ++ tailWord_1282501).sum := by decide
  have hdescent : baseEnd_1282501 < baseStart_1282501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282521 : List Nat := [1, 2, 1, 2, 4, 1, 2, 2, 1, 7]
def baseStart_1282521 : Nat := 118140960795 + 1282521 * 2 ^ 59
def prefixEnd_1282521 : Nat := 4983230072969 + 3 ^ 40 * 1282521 * 2
def baseEnd_1282521 : Nat := 219516574161693954796433

theorem tailTrace_1282521 : CollatzResearch.WordTrace tailWord_1282521 prefixEnd_1282521 219516574161693954796433 := by
  unfold tailWord_1282521
  simp only [CollatzResearch.WordTrace]
  refine ⟨46777383786652928993471417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31184922524435285995647611 46777383786652928993471417)
  ·
    refine ⟨35083037839989696745103563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46777383786652928993471417 35083037839989696745103563)
    ·
      refine ⟨52624556759984545117655345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35083037839989696745103563 52624556759984545117655345)
      ·
        refine ⟨39468417569988408838241509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52624556759984545117655345 39468417569988408838241509)
        ·
          refine ⟨7400328294372826657170283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39468417569988408838241509 7400328294372826657170283)
          ·
            refine ⟨11100492441559239985755425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7400328294372826657170283 11100492441559239985755425)
            ·
              refine ⟨8325369331169429989316569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11100492441559239985755425 8325369331169429989316569)
              ·
                refine ⟨6244026998377072491987427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8325369331169429989316569 6244026998377072491987427)
                ·
                  refine ⟨9366040497565608737981141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6244026998377072491987427 9366040497565608737981141)
                  ·
                    refine ⟨219516574161693954796433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9366040497565608737981141 219516574161693954796433)
                    ·
                      rfl

theorem cell23_1282521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 2, 1, 7].length) (baseStart_1282521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1282521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1282521 prefixEnd_1282521 := by exact prefixLift 1282521
  have htrace : WordTrace (prefixWord ++ tailWord_1282521) baseStart_1282521 baseEnd_1282521 := by
    simpa [prefixWord, tailWord_1282521, baseEnd_1282521] using wordTrace_append hprefix tailTrace_1282521
  have hstable : (prefixWord ++ tailWord_1282521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282521).length < 2 ^ (prefixWord ++ tailWord_1282521).sum := by decide
  have hdescent : baseEnd_1282521 < baseStart_1282521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282528 : List Nat := [2, 1, 1, 3, 1, 1, 3, 2, 2, 5, 2]
def baseStart_1282528 : Nat := 118140960795 + 1282528 * 2 ^ 59
def prefixEnd_1282528 : Nat := 4983230072969 + 3 ^ 40 * 1282528 * 2
def baseEnd_1282528 : Nat := 658553316849663337001767

theorem tailTrace_1282528 : CollatzResearch.WordTrace tailWord_1282528 prefixEnd_1282528 658553316849663337001767 := by
  unfold tailWord_1282528
  simp only [CollatzResearch.WordTrace]
  refine ⟨23388819548813784594488119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31185092731751712792650825 23388819548813784594488119)
  ·
    refine ⟨35083229323220676891732179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23388819548813784594488119 35083229323220676891732179)
    ·
      refine ⟨52624843984831015337598269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35083229323220676891732179 52624843984831015337598269)
      ·
        refine ⟨19734316494311630751599351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52624843984831015337598269 19734316494311630751599351)
        ·
          refine ⟨29601474741467446127399027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19734316494311630751599351 29601474741467446127399027)
          ·
            refine ⟨44402212112201169191098541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29601474741467446127399027 44402212112201169191098541)
            ·
              refine ⟨16650829542075438446661953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44402212112201169191098541 16650829542075438446661953)
              ·
                refine ⟨12488122156556578834996465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16650829542075438446661953 12488122156556578834996465)
                ·
                  refine ⟨9366091617417434126247349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12488122156556578834996465 9366091617417434126247349)
                  ·
                    refine ⟨878071089132884449335689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9366091617417434126247349 878071089132884449335689)
                    ·
                      refine ⟨658553316849663337001767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 878071089132884449335689 658553316849663337001767)
                      ·
                        rfl

theorem cell23_1282528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 2, 5, 2].length) (baseStart_1282528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1282528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1282528 prefixEnd_1282528 := by exact prefixLift 1282528
  have htrace : WordTrace (prefixWord ++ tailWord_1282528) baseStart_1282528 baseEnd_1282528 := by
    simpa [prefixWord, tailWord_1282528, baseEnd_1282528] using wordTrace_append hprefix tailTrace_1282528
  have hstable : (prefixWord ++ tailWord_1282528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282528).length < 2 ^ (prefixWord ++ tailWord_1282528).sum := by decide
  have hdescent : baseEnd_1282528 < baseStart_1282528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282538 : List Nat := [3, 1, 3, 1, 3, 2, 1, 1, 1, 7]
def baseStart_1282538 : Nat := 118140960795 + 1282538 * 2 ^ 59
def prefixEnd_1282538 : Nat := 4983230072969 + 3 ^ 40 * 1282538 * 2
def baseEnd_1282538 : Nat := 219519483885402765958907

theorem tailTrace_1282538 : CollatzResearch.WordTrace tailWord_1282538 prefixEnd_1282538 219519483885402765958907 := by
  unfold tailWord_1282538
  simp only [CollatzResearch.WordTrace]
  refine ⟨11694500956897835224210067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31185335885060893931226845 11694500956897835224210067)
  ·
    refine ⟨17541751435346752836315101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11694500956897835224210067 17541751435346752836315101)
    ·
      refine ⟨6578156788255032313618163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17541751435346752836315101 6578156788255032313618163)
      ·
        refine ⟨9867235182382548470427245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6578156788255032313618163 9867235182382548470427245)
        ·
          refine ⟨3700213193393455676410217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9867235182382548470427245 3700213193393455676410217)
          ·
            refine ⟨2775159895045091757307663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3700213193393455676410217 2775159895045091757307663)
            ·
              refine ⟨4162739842567637635961495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2775159895045091757307663 4162739842567637635961495)
              ·
                refine ⟨6244109763851456453942243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4162739842567637635961495 6244109763851456453942243)
                ·
                  refine ⟨9366164645777184680913365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6244109763851456453942243 9366164645777184680913365)
                  ·
                    refine ⟨219519483885402765958907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9366164645777184680913365 219519483885402765958907)
                    ·
                      rfl

theorem cell23_1282538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 1, 1, 7].length) (baseStart_1282538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1282538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1282538 prefixEnd_1282538 := by exact prefixLift 1282538
  have htrace : WordTrace (prefixWord ++ tailWord_1282538) baseStart_1282538 baseEnd_1282538 := by
    simpa [prefixWord, tailWord_1282538, baseEnd_1282538] using wordTrace_append hprefix tailTrace_1282538
  have hstable : (prefixWord ++ tailWord_1282538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282538).length < 2 ^ (prefixWord ++ tailWord_1282538).sum := by decide
  have hdescent : baseEnd_1282538 < baseStart_1282538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282645 : List Nat := [1, 3, 2, 2, 1, 1, 5, 2, 1, 5]
def baseStart_1282645 : Nat := 118140960795 + 1282645 * 2 ^ 59
def prefixEnd_1282645 : Nat := 4983230072969 + 3 ^ 40 * 1282645 * 2
def baseEnd_1282645 : Nat := 219537798028746459746243

theorem tailTrace_1282645 : CollatzResearch.WordTrace tailWord_1282645 prefixEnd_1282645 219537798028746459746243 := by
  unfold tailWord_1282645
  simp only [CollatzResearch.WordTrace]
  refine ⟨46781906438203698170985389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31187937625469132113990259 46781906438203698170985389)
  ·
    refine ⟨17543214914326386814119521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46781906438203698170985389 17543214914326386814119521)
    ·
      refine ⟨13157411185744790110589641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17543214914326386814119521 13157411185744790110589641)
      ·
        refine ⟨9868058389308592582942231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13157411185744790110589641 9868058389308592582942231)
        ·
          refine ⟨14802087583962888874413347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9868058389308592582942231 14802087583962888874413347)
          ·
            refine ⟨22203131375944333311620021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14802087583962888874413347 22203131375944333311620021)
            ·
              refine ⟨2081543566494781247964377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22203131375944333311620021 2081543566494781247964377)
              ·
                refine ⟨1561157674871085935973283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2081543566494781247964377 1561157674871085935973283)
                ·
                  refine ⟨2341736512306628903959925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1561157674871085935973283 2341736512306628903959925)
                  ·
                    refine ⟨219537798028746459746243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2341736512306628903959925 219537798028746459746243)
                    ·
                      rfl

theorem cell23_1282645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 2, 1, 5].length) (baseStart_1282645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1282645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1282645 prefixEnd_1282645 := by exact prefixLift 1282645
  have htrace : WordTrace (prefixWord ++ tailWord_1282645) baseStart_1282645 baseEnd_1282645 := by
    simpa [prefixWord, tailWord_1282645, baseEnd_1282645] using wordTrace_append hprefix tailTrace_1282645
  have hstable : (prefixWord ++ tailWord_1282645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282645).length < 2 ^ (prefixWord ++ tailWord_1282645).sum := by decide
  have hdescent : baseEnd_1282645 < baseStart_1282645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282651 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 11]
def baseStart_1282651 : Nat := 118140960795 + 1282651 * 2 ^ 59
def prefixEnd_1282651 : Nat := 4983230072969 + 3 ^ 40 * 1282651 * 2
def baseEnd_1282651 : Nat := 658616474970166355763701

theorem tailTrace_1282651 : CollatzResearch.WordTrace tailWord_1282651 prefixEnd_1282651 658616474970166355763701 := by
  unfold tailWord_1282651
  simp only [CollatzResearch.WordTrace]
  refine ⟨46782125276181961195703807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31188083517454640797135871 46782125276181961195703807)
  ·
    refine ⟨70173187914272941793555711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46782125276181961195703807 70173187914272941793555711)
    ·
      refine ⟨105259781871409412690333567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70173187914272941793555711 105259781871409412690333567)
      ·
        refine ⟨157889672807114119035500351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105259781871409412690333567 157889672807114119035500351)
        ·
          refine ⟨236834509210671178553250527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157889672807114119035500351 236834509210671178553250527)
          ·
            refine ⟨355251763816006767829875791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 236834509210671178553250527 355251763816006767829875791)
            ·
              refine ⟨532877645724010151744813687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 355251763816006767829875791 532877645724010151744813687)
              ·
                refine ⟨799316468586015227617220531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 532877645724010151744813687 799316468586015227617220531)
                ·
                  refine ⟨1198974702879022841425830797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 799316468586015227617220531 1198974702879022841425830797)
                  ·
                    refine ⟨449615513579633565534686549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1198974702879022841425830797 449615513579633565534686549)
                    ·
                      refine ⟨658616474970166355763701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 11 449615513579633565534686549 658616474970166355763701)
                      ·
                        rfl

theorem cell23_1282651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 11].length) (baseStart_1282651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1282651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1282651 prefixEnd_1282651 := by exact prefixLift 1282651
  have htrace : WordTrace (prefixWord ++ tailWord_1282651) baseStart_1282651 baseEnd_1282651 := by
    simpa [prefixWord, tailWord_1282651, baseEnd_1282651] using wordTrace_append hprefix tailTrace_1282651
  have hstable : (prefixWord ++ tailWord_1282651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282651).length < 2 ^ (prefixWord ++ tailWord_1282651).sum := by decide
  have hdescent : baseEnd_1282651 < baseStart_1282651 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282688 : List Nat := [2, 1, 1, 2, 1, 5, 3, 8]
def baseStart_1282688 : Nat := 118140960795 + 1282688 * 2 ^ 59
def prefixEnd_1282688 : Nat := 4983230072969 + 3 ^ 40 * 1282688 * 2
def baseEnd_1282688 : Nat := 24393906435347507814853

theorem tailTrace_1282688 : CollatzResearch.WordTrace tailWord_1282688 prefixEnd_1282688 24393906435347507814853 := by
  unfold tailWord_1282688
  simp only [CollatzResearch.WordTrace]
  refine ⟨23391737388523958257400359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31188983184698611009867145 23391737388523958257400359)
  ·
    refine ⟨35087606082785937386100539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23391737388523958257400359 35087606082785937386100539)
    ·
      refine ⟨52631409124178906079150809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35087606082785937386100539 52631409124178906079150809)
      ·
        refine ⟨39473556843134179559363107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52631409124178906079150809 39473556843134179559363107)
        ·
          refine ⟨59210335264701269339044661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39473556843134179559363107 59210335264701269339044661)
          ·
            refine ⟨5550968931065744000535437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 59210335264701269339044661 5550968931065744000535437)
            ·
              refine ⟨2081613349149654000200789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5550968931065744000535437 2081613349149654000200789)
              ·
                refine ⟨24393906435347507814853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2081613349149654000200789 24393906435347507814853)
                ·
                  rfl

theorem cell23_1282688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 8].length) (baseStart_1282688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1282688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1282688 prefixEnd_1282688 := by exact prefixLift 1282688
  have htrace : WordTrace (prefixWord ++ tailWord_1282688) baseStart_1282688 baseEnd_1282688 := by
    simpa [prefixWord, tailWord_1282688, baseEnd_1282688] using wordTrace_append hprefix tailTrace_1282688
  have hstable : (prefixWord ++ tailWord_1282688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282688).length < 2 ^ (prefixWord ++ tailWord_1282688).sum := by decide
  have hdescent : baseEnd_1282688 < baseStart_1282688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282692 : List Nat := [2, 3, 2, 1, 3, 1, 2, 3, 2, 4]
def baseStart_1282692 : Nat := 118140960795 + 1282692 * 2 ^ 59
def prefixEnd_1282692 : Nat := 4983230072969 + 3 ^ 40 * 1282692 * 2
def baseEnd_1282692 : Nat := 219545842559000231783671

theorem tailTrace_1282692 : CollatzResearch.WordTrace tailWord_1282692 prefixEnd_1282692 219545842559000231783671 := by
  unfold tailWord_1282692
  simp only [CollatzResearch.WordTrace]
  refine ⟨23391810334516712598973165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31189080446022283465297553 23391810334516712598973165)
  ·
    refine ⟨8771928875443767224614937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23391810334516712598973165 8771928875443767224614937)
    ·
      refine ⟨6578946656582825418461203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8771928875443767224614937 6578946656582825418461203)
      ·
        refine ⟨9868419984874238127691805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6578946656582825418461203 9868419984874238127691805)
        ·
          refine ⟨3700657494327839297884427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9868419984874238127691805 3700657494327839297884427)
          ·
            refine ⟨5550986241491758946826641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3700657494327839297884427 5550986241491758946826641)
            ·
              refine ⟨4163239681118819210119981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5550986241491758946826641 4163239681118819210119981)
              ·
                refine ⟨1561214880419557203794993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4163239681118819210119981 1561214880419557203794993)
                ·
                  refine ⟨1170911160314667902846245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1561214880419557203794993 1170911160314667902846245)
                  ·
                    refine ⟨219545842559000231783671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1170911160314667902846245 219545842559000231783671)
                    ·
                      rfl

theorem cell23_1282692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 3, 2, 4].length) (baseStart_1282692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1282692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1282692 prefixEnd_1282692 := by exact prefixLift 1282692
  have htrace : WordTrace (prefixWord ++ tailWord_1282692) baseStart_1282692 baseEnd_1282692 := by
    simpa [prefixWord, tailWord_1282692, baseEnd_1282692] using wordTrace_append hprefix tailTrace_1282692
  have hstable : (prefixWord ++ tailWord_1282692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282692).length < 2 ^ (prefixWord ++ tailWord_1282692).sum := by decide
  have hdescent : baseEnd_1282692 < baseStart_1282692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282695 : List Nat := [1, 1, 4, 2, 1, 2, 4, 1, 1, 2, 4]
def baseStart_1282695 : Nat := 118140960795 + 1282695 * 2 ^ 59
def prefixEnd_1282695 : Nat := 4983230072969 + 3 ^ 40 * 1282695 * 2
def baseEnd_1282695 : Nat := 658639068118964183613499

theorem tailTrace_1282695 : CollatzResearch.WordTrace tailWord_1282695 prefixEnd_1282695 658639068118964183613499 := by
  unfold tailWord_1282695
  simp only [CollatzResearch.WordTrace]
  refine ⟨46783730088022556710305539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31189153392015037806870359 46783730088022556710305539)
  ·
    refine ⟨70175595132033835065458309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46783730088022556710305539 70175595132033835065458309)
    ·
      refine ⟨13157924087256344074773433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70175595132033835065458309 13157924087256344074773433)
      ·
        refine ⟨9868443065442258056080075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13157924087256344074773433 9868443065442258056080075)
        ·
          refine ⟨14802664598163387084120113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9868443065442258056080075 14802664598163387084120113)
          ·
            refine ⟨11101998448622540313090085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14802664598163387084120113 11101998448622540313090085)
            ·
              refine ⟨2081624709116726308704391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11101998448622540313090085 2081624709116726308704391)
              ·
                refine ⟨3122437063675089463056587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2081624709116726308704391 3122437063675089463056587)
                ·
                  refine ⟨4683655595512634194584881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3122437063675089463056587 4683655595512634194584881)
                  ·
                    refine ⟨3512741696634475645938661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4683655595512634194584881 3512741696634475645938661)
                    ·
                      refine ⟨658639068118964183613499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3512741696634475645938661 658639068118964183613499)
                      ·
                        rfl

theorem cell23_1282695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 1, 1, 2, 4].length) (baseStart_1282695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1282695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1282695 prefixEnd_1282695 := by exact prefixLift 1282695
  have htrace : WordTrace (prefixWord ++ tailWord_1282695) baseStart_1282695 baseEnd_1282695 := by
    simpa [prefixWord, tailWord_1282695, baseEnd_1282695] using wordTrace_append hprefix tailTrace_1282695
  have hstable : (prefixWord ++ tailWord_1282695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282695).length < 2 ^ (prefixWord ++ tailWord_1282695).sum := by decide
  have hdescent : baseEnd_1282695 < baseStart_1282695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282702 : List Nat := [4, 1, 1, 3, 1, 1, 2, 4, 1, 2, 3]
def baseStart_1282702 : Nat := 118140960795 + 1282702 * 2 ^ 59
def prefixEnd_1282702 : Nat := 4983230072969 + 3 ^ 40 * 1282702 * 2
def baseEnd_1282702 : Nat := 658642662483545656225967

theorem tailTrace_1282702 : CollatzResearch.WordTrace tailWord_1282702 prefixEnd_1282702 658642662483545656225967 := by
  unfold tailWord_1282702
  simp only [CollatzResearch.WordTrace]
  refine ⟨5847998174874649613226295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31189323599331464603873573 5847998174874649613226295)
  ·
    refine ⟨8771997262311974419839443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5847998174874649613226295 8771997262311974419839443)
    ·
      refine ⟨13157995893467961629759165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8771997262311974419839443 13157995893467961629759165)
      ·
        refine ⟨4934248460050485611159687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13157995893467961629759165 4934248460050485611159687)
        ·
          refine ⟨7401372690075728416739531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4934248460050485611159687 7401372690075728416739531)
          ·
            refine ⟨11102059035113592625109297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7401372690075728416739531 11102059035113592625109297)
            ·
              refine ⟨8326544276335194468831973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11102059035113592625109297 8326544276335194468831973)
              ·
                refine ⟨1561227051812848962905995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8326544276335194468831973 1561227051812848962905995)
                ·
                  refine ⟨2341840577719273444358993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1561227051812848962905995 2341840577719273444358993)
                  ·
                    refine ⟨1756380433289455083269245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2341840577719273444358993 1756380433289455083269245)
                    ·
                      refine ⟨658642662483545656225967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1756380433289455083269245 658642662483545656225967)
                      ·
                        rfl

theorem cell23_1282702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 4, 1, 2, 3].length) (baseStart_1282702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1282702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1282702 prefixEnd_1282702 := by exact prefixLift 1282702
  have htrace : WordTrace (prefixWord ++ tailWord_1282702) baseStart_1282702 baseEnd_1282702 := by
    simpa [prefixWord, tailWord_1282702, baseEnd_1282702] using wordTrace_append hprefix tailTrace_1282702
  have hstable : (prefixWord ++ tailWord_1282702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282702).length < 2 ^ (prefixWord ++ tailWord_1282702).sum := by decide
  have hdescent : baseEnd_1282702 < baseStart_1282702 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282716 : List Nat := [2, 2, 3, 2, 2, 1, 1, 5, 1, 2, 2]
def baseStart_1282716 : Nat := 118140960795 + 1282716 * 2 ^ 59
def prefixEnd_1282716 : Nat := 4983230072969 + 3 ^ 40 * 1282716 * 2
def baseEnd_1282716 : Nat := 658649851212708601450903

theorem tailTrace_1282716 : CollatzResearch.WordTrace tailWord_1282716 prefixEnd_1282716 658649851212708601450903 := by
  unfold tailWord_1282716
  simp only [CollatzResearch.WordTrace]
  refine ⟨23392248010473238648410001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31189664013964318197880001 23392248010473238648410001)
  ·
    refine ⟨17544186007854928986307501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23392248010473238648410001 17544186007854928986307501)
    ·
      refine ⟨6579069752945598369865313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17544186007854928986307501 6579069752945598369865313)
      ·
        refine ⟨4934302314709198777398985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6579069752945598369865313 4934302314709198777398985)
        ·
          refine ⟨3700726736031899083049239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4934302314709198777398985 3700726736031899083049239)
          ·
            refine ⟨5551090104047848624573859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3700726736031899083049239 5551090104047848624573859)
            ·
              refine ⟨8326635156071772936860789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5551090104047848624573859 8326635156071772936860789)
              ·
                refine ⟨780622045881728712830699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8326635156071772936860789 780622045881728712830699)
                ·
                  refine ⟨1170933068822593069246049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 780622045881728712830699 1170933068822593069246049)
                  ·
                    refine ⟨878199801616944801934537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1170933068822593069246049 878199801616944801934537)
                    ·
                      refine ⟨658649851212708601450903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 878199801616944801934537 658649851212708601450903)
                      ·
                        rfl

theorem cell23_1282716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 5, 1, 2, 2].length) (baseStart_1282716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1282716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1282716 prefixEnd_1282716 := by exact prefixLift 1282716
  have htrace : WordTrace (prefixWord ++ tailWord_1282716) baseStart_1282716 baseEnd_1282716 := by
    simpa [prefixWord, tailWord_1282716, baseEnd_1282716] using wordTrace_append hprefix tailTrace_1282716
  have hstable : (prefixWord ++ tailWord_1282716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282716).length < 2 ^ (prefixWord ++ tailWord_1282716).sum := by decide
  have hdescent : baseEnd_1282716 < baseStart_1282716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282775 : List Nat := [1, 1, 3, 2, 1, 5, 1, 1, 2, 1, 5]
def baseStart_1282775 : Nat := 118140960795 + 1282775 * 2 ^ 59
def prefixEnd_1282775 : Nat := 4983230072969 + 3 ^ 40 * 1282775 * 2
def baseEnd_1282775 : Nat := 658680146571323870613131

theorem tailTrace_1282775 : CollatzResearch.WordTrace tailWord_1282775 prefixEnd_1282775 658680146571323870613131 := by
  unfold tailWord_1282775
  simp only [CollatzResearch.WordTrace]
  refine ⟨46786647927732730373217779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31191098618488486915478519 46786647927732730373217779)
  ·
    refine ⟨70179971891599095559826669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46786647927732730373217779 70179971891599095559826669)
    ·
      refine ⟨26317489459349660834935001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70179971891599095559826669 26317489459349660834935001)
      ·
        refine ⟨19738117094512245626201251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26317489459349660834935001 19738117094512245626201251)
        ·
          refine ⟨29607175641768368439301877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19738117094512245626201251 29607175641768368439301877)
          ·
            refine ⟨2775672716415784541184551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29607175641768368439301877 2775672716415784541184551)
            ·
              refine ⟨4163509074623676811776827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2775672716415784541184551 4163509074623676811776827)
              ·
                refine ⟨6245263611935515217665241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4163509074623676811776827 6245263611935515217665241)
                ·
                  refine ⟨4683947708951636413248931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6245263611935515217665241 4683947708951636413248931)
                  ·
                    refine ⟨7025921563427454619873397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4683947708951636413248931 7025921563427454619873397)
                    ·
                      refine ⟨658680146571323870613131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7025921563427454619873397 658680146571323870613131)
                      ·
                        rfl

theorem cell23_1282775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 1, 2, 1, 5].length) (baseStart_1282775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1282775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1282775 prefixEnd_1282775 := by exact prefixLift 1282775
  have htrace : WordTrace (prefixWord ++ tailWord_1282775) baseStart_1282775 baseEnd_1282775 := by
    simpa [prefixWord, tailWord_1282775, baseEnd_1282775] using wordTrace_append hprefix tailTrace_1282775
  have hstable : (prefixWord ++ tailWord_1282775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282775).length < 2 ^ (prefixWord ++ tailWord_1282775).sum := by decide
  have hdescent : baseEnd_1282775 < baseStart_1282775 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282789 : List Nat := [1, 3, 1, 4, 1, 2, 2, 1, 4, 2, 2]
def baseStart_1282789 : Nat := 118140960795 + 1282789 * 2 ^ 59
def prefixEnd_1282789 : Nat := 4983230072969 + 3 ^ 40 * 1282789 * 2
def baseEnd_1282789 : Nat := 658687335300486815838067

theorem tailTrace_1282789 : CollatzResearch.WordTrace tailWord_1282789 prefixEnd_1282789 658687335300486815838067 := by
  unfold tailWord_1282789
  simp only [CollatzResearch.WordTrace]
  refine ⟨46787158549682010764227421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31191439033121340509484947 46787158549682010764227421)
  ·
    refine ⟨17545184456130754036585283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46787158549682010764227421 17545184456130754036585283)
    ·
      refine ⟨26317776684196131054877925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17545184456130754036585283 26317776684196131054877925)
      ·
        refine ⟨4934583128286774572789611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26317776684196131054877925 4934583128286774572789611)
        ·
          refine ⟨7401874692430161859184417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4934583128286774572789611 7401874692430161859184417)
          ·
            refine ⟨5551406019322621394388313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7401874692430161859184417 5551406019322621394388313)
            ·
              refine ⟨4163554514491966045791235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5551406019322621394388313 4163554514491966045791235)
              ·
                refine ⟨6245331771737949068686853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4163554514491966045791235 6245331771737949068686853)
                ·
                  refine ⟨1170999707200865450378785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6245331771737949068686853 1170999707200865450378785)
                  ·
                    refine ⟨878249780400649087784089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1170999707200865450378785 878249780400649087784089)
                    ·
                      refine ⟨658687335300486815838067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 878249780400649087784089 658687335300486815838067)
                      ·
                        rfl

theorem cell23_1282789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 1, 4, 2, 2].length) (baseStart_1282789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1282789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1282789 prefixEnd_1282789 := by exact prefixLift 1282789
  have htrace : WordTrace (prefixWord ++ tailWord_1282789) baseStart_1282789 baseEnd_1282789 := by
    simpa [prefixWord, tailWord_1282789, baseEnd_1282789] using wordTrace_append hprefix tailTrace_1282789
  have hstable : (prefixWord ++ tailWord_1282789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282789).length < 2 ^ (prefixWord ++ tailWord_1282789).sum := by decide
  have hdescent : baseEnd_1282789 < baseStart_1282789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282806 : List Nat := [5, 1, 1, 1, 1, 2, 3, 3, 2, 2, 2]
def baseStart_1282806 : Nat := 118140960795 + 1282806 * 2 ^ 59
def prefixEnd_1282806 : Nat := 4983230072969 + 3 ^ 40 * 1282806 * 2
def baseEnd_1282806 : Nat := 658696064471613249325489

theorem tailTrace_1282806 : CollatzResearch.WordTrace tailWord_1282806 prefixEnd_1282806 658696064471613249325489 := by
  unfold tailWord_1282806
  simp only [CollatzResearch.WordTrace]
  refine ⟨2924236161913776416724767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31191852393746948445064181 2924236161913776416724767)
  ·
    refine ⟨4386354242870664625087151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2924236161913776416724767 4386354242870664625087151)
    ·
      refine ⟨6579531364305996937630727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4386354242870664625087151 6579531364305996937630727)
      ·
        refine ⟨9869297046458995406446091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6579531364305996937630727 9869297046458995406446091)
        ·
          refine ⟨14803945569688493109669137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9869297046458995406446091 14803945569688493109669137)
          ·
            refine ⟨11102959177266369832251853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14803945569688493109669137 11102959177266369832251853)
            ·
              refine ⟨4163609691474888687094445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11102959177266369832251853 4163609691474888687094445)
              ·
                refine ⟨1561353634303083257660417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4163609691474888687094445 1561353634303083257660417)
                ·
                  refine ⟨1171015225727312443245313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1561353634303083257660417 1171015225727312443245313)
                  ·
                    refine ⟨878261419295484332433985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1171015225727312443245313 878261419295484332433985)
                    ·
                      refine ⟨658696064471613249325489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 878261419295484332433985 658696064471613249325489)
                      ·
                        rfl

theorem cell23_1282806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 3, 2, 2, 2].length) (baseStart_1282806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1282806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1282806 prefixEnd_1282806 := by exact prefixLift 1282806
  have htrace : WordTrace (prefixWord ++ tailWord_1282806) baseStart_1282806 baseEnd_1282806 := by
    simpa [prefixWord, tailWord_1282806, baseEnd_1282806] using wordTrace_append hprefix tailTrace_1282806
  have hstable : (prefixWord ++ tailWord_1282806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282806).length < 2 ^ (prefixWord ++ tailWord_1282806).sum := by decide
  have hdescent : baseEnd_1282806 < baseStart_1282806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282825 : List Nat := [1, 2, 1, 1, 3, 2, 3, 3, 2, 5]
def baseStart_1282825 : Nat := 118140960795 + 1282825 * 2 ^ 59
def prefixEnd_1282825 : Nat := 4983230072969 + 3 ^ 40 * 1282825 * 2
def baseEnd_1282825 : Nat := 219568606868016224995967

theorem tailTrace_1282825 : CollatzResearch.WordTrace tailWord_1282825 prefixEnd_1282825 219568606868016224995967 := by
  unfold tailWord_1282825
  simp only [CollatzResearch.WordTrace]
  refine ⟨46788471577551588912537929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31192314385034392608358619 46788471577551588912537929)
  ·
    refine ⟨35091353683163691684403447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46788471577551588912537929 35091353683163691684403447)
    ·
      refine ⟨52637030524745537526605171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35091353683163691684403447 52637030524745537526605171)
      ·
        refine ⟨78955545787118306289907757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52637030524745537526605171 78955545787118306289907757)
        ·
          refine ⟨29608329670169364858715409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78955545787118306289907757 29608329670169364858715409)
          ·
            refine ⟨22206247252627023644036557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29608329670169364858715409 22206247252627023644036557)
            ·
              refine ⟨8327342719735133866513709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22206247252627023644036557 8327342719735133866513709)
              ·
                refine ⟨3122753519900675199942641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8327342719735133866513709 3122753519900675199942641)
                ·
                  refine ⟨2342065139925506399956981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3122753519900675199942641 2342065139925506399956981)
                  ·
                    refine ⟨219568606868016224995967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2342065139925506399956981 219568606868016224995967)
                    ·
                      rfl

theorem cell23_1282825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 3, 2, 5].length) (baseStart_1282825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1282825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1282825 prefixEnd_1282825 := by exact prefixLift 1282825
  have htrace : WordTrace (prefixWord ++ tailWord_1282825) baseStart_1282825 baseEnd_1282825 := by
    simpa [prefixWord, tailWord_1282825, baseEnd_1282825] using wordTrace_append hprefix tailTrace_1282825
  have hstable : (prefixWord ++ tailWord_1282825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282825).length < 2 ^ (prefixWord ++ tailWord_1282825).sum := by decide
  have hdescent : baseEnd_1282825 < baseStart_1282825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282872 : List Nat := [2, 1, 2, 1, 3, 2, 3, 2, 3, 4]
def baseStart_1282872 : Nat := 118140960795 + 1282872 * 2 ^ 59
def prefixEnd_1282872 : Nat := 4983230072969 + 3 ^ 40 * 1282872 * 2
def baseEnd_1282872 : Nat := 219576651398269997033395

theorem tailTrace_1282872 : CollatzResearch.WordTrace tailWord_1282872 prefixEnd_1282872 219576651398269997033395 := by
  unfold tailWord_1282872
  simp only [CollatzResearch.WordTrace]
  refine ⟨23395092904190657969749435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31193457205587543959665913 23395092904190657969749435)
  ·
    refine ⟨35092639356285986954624153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23395092904190657969749435 35092639356285986954624153)
    ·
      refine ⟨26319479517214490215968115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35092639356285986954624153 26319479517214490215968115)
      ·
        refine ⟨39479219275821735323952173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26319479517214490215968115 39479219275821735323952173)
        ·
          refine ⟨14804707228433150746482065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39479219275821735323952173 14804707228433150746482065)
          ·
            refine ⟨11103530421324863059861549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14804707228433150746482065 11103530421324863059861549)
            ·
              refine ⟨4163823907996823647448081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11103530421324863059861549 4163823907996823647448081)
              ·
                refine ⟨3122867930997617735586061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4163823907996823647448081 3122867930997617735586061)
                ·
                  refine ⟨1171075474124106650844773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3122867930997617735586061 1171075474124106650844773)
                  ·
                    refine ⟨219576651398269997033395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1171075474124106650844773 219576651398269997033395)
                    ·
                      rfl

theorem cell23_1282872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 2, 3, 4].length) (baseStart_1282872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1282872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1282872 prefixEnd_1282872 := by exact prefixLift 1282872
  have htrace : WordTrace (prefixWord ++ tailWord_1282872) baseStart_1282872 baseEnd_1282872 := by
    simpa [prefixWord, tailWord_1282872, baseEnd_1282872] using wordTrace_append hprefix tailTrace_1282872
  have hstable : (prefixWord ++ tailWord_1282872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282872).length < 2 ^ (prefixWord ++ tailWord_1282872).sum := by decide
  have hdescent : baseEnd_1282872 < baseStart_1282872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282879 : List Nat := [1, 1, 2, 2, 5, 3, 1, 1, 2, 1, 4]
def baseStart_1282879 : Nat := 118140960795 + 1282879 * 2 ^ 59
def prefixEnd_1282879 : Nat := 4983230072969 + 3 ^ 40 * 1282879 * 2
def baseEnd_1282879 : Nat := 658733548559391463712653

theorem tailTrace_1282879 : CollatzResearch.WordTrace tailWord_1282879 prefixEnd_1282879 658733548559391463712653 := by
  unfold tailWord_1282879
  simp only [CollatzResearch.WordTrace]
  refine ⟨46790441119355956135003691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31193627412903970756669127 46790441119355956135003691)
  ·
    refine ⟨70185661679033934202505537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46790441119355956135003691 70185661679033934202505537)
    ·
      refine ⟨52639246259275450651879153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70185661679033934202505537 52639246259275450651879153)
      ·
        refine ⟨39479434694456587988909365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52639246259275450651879153 39479434694456587988909365)
        ·
          refine ⟨3701197002605305123960253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39479434694456587988909365 3701197002605305123960253)
          ·
            refine ⟨1387948875976989421485095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3701197002605305123960253 1387948875976989421485095)
            ·
              refine ⟨2081923313965484132227643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1387948875976989421485095 2081923313965484132227643)
              ·
                refine ⟨3122884970948226198341465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2081923313965484132227643 3122884970948226198341465)
                ·
                  refine ⟨2342163728211169648756099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3122884970948226198341465 2342163728211169648756099)
                  ·
                    refine ⟨3513245592316754473134149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2342163728211169648756099 3513245592316754473134149)
                    ·
                      refine ⟨658733548559391463712653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3513245592316754473134149 658733548559391463712653)
                      ·
                        rfl

theorem cell23_1282879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 1, 2, 1, 4].length) (baseStart_1282879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1282879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1282879 prefixEnd_1282879 := by exact prefixLift 1282879
  have htrace : WordTrace (prefixWord ++ tailWord_1282879) baseStart_1282879 baseEnd_1282879 := by
    simpa [prefixWord, tailWord_1282879, baseEnd_1282879] using wordTrace_append hprefix tailTrace_1282879
  have hstable : (prefixWord ++ tailWord_1282879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282879).length < 2 ^ (prefixWord ++ tailWord_1282879).sum := by decide
  have hdescent : baseEnd_1282879 < baseStart_1282879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282889 : List Nat := [1, 2, 1, 1, 2, 5, 1, 5, 1, 4]
def baseStart_1282889 : Nat := 118140960795 + 1282889 * 2 ^ 59
def prefixEnd_1282889 : Nat := 4983230072969 + 3 ^ 40 * 1282889 * 2
def baseEnd_1282889 : Nat := 219579561121978808195869

theorem tailTrace_1282889 : CollatzResearch.WordTrace tailWord_1282889 prefixEnd_1282889 219579561121978808195869 := by
  unfold tailWord_1282889
  simp only [CollatzResearch.WordTrace]
  refine ⟨46790805849319727842867721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31193870566213151895245147 46790805849319727842867721)
  ·
    refine ⟨35093104386989795882150791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46790805849319727842867721 35093104386989795882150791)
    ·
      refine ⟨52639656580484693823226187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35093104386989795882150791 52639656580484693823226187)
      ·
        refine ⟨78959484870727040734839281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52639656580484693823226187 78959484870727040734839281)
        ·
          refine ⟨59219613653045280551129461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78959484870727040734839281 59219613653045280551129461)
          ·
            refine ⟨5551838779972995051668387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 59219613653045280551129461 5551838779972995051668387)
            ·
              refine ⟨8327758169959492577502581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5551838779972995051668387 8327758169959492577502581)
              ·
                refine ⟨780727328433702429140867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8327758169959492577502581 780727328433702429140867)
                ·
                  refine ⟨1171090992650553643711301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 780727328433702429140867 1171090992650553643711301)
                  ·
                    refine ⟨219579561121978808195869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1171090992650553643711301 219579561121978808195869)
                    ·
                      rfl

theorem cell23_1282889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 5, 1, 4].length) (baseStart_1282889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1282889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1282889 prefixEnd_1282889 := by exact prefixLift 1282889
  have htrace : WordTrace (prefixWord ++ tailWord_1282889) baseStart_1282889 baseEnd_1282889 := by
    simpa [prefixWord, tailWord_1282889, baseEnd_1282889] using wordTrace_append hprefix tailTrace_1282889
  have hstable : (prefixWord ++ tailWord_1282889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282889).length < 2 ^ (prefixWord ++ tailWord_1282889).sum := by decide
  have hdescent : baseEnd_1282889 < baseStart_1282889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282895 : List Nat := [1, 1, 2, 1, 1, 2, 1, 1, 3, 7, 3]
def baseStart_1282895 : Nat := 118140960795 + 1282895 * 2 ^ 59
def prefixEnd_1282895 : Nat := 4983230072969 + 3 ^ 40 * 1282895 * 2
def baseEnd_1282895 : Nat := 658741764249863401112579

theorem tailTrace_1282895 : CollatzResearch.WordTrace tailWord_1282895 prefixEnd_1282895 658741764249863401112579 := by
  unfold tailWord_1282895
  simp only [CollatzResearch.WordTrace]
  refine ⟨46791024687297990867586139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31194016458198660578390759 46791024687297990867586139)
  ·
    refine ⟨70186537030946986301379209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46791024687297990867586139 70186537030946986301379209)
    ·
      refine ⟨52639902773210239726034407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70186537030946986301379209 52639902773210239726034407)
      ·
        refine ⟨78959854159815359589051611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52639902773210239726034407 78959854159815359589051611)
        ·
          refine ⟨118439781239723039383577417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78959854159815359589051611 118439781239723039383577417)
          ·
            refine ⟨88829835929792279537683063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118439781239723039383577417 88829835929792279537683063)
            ·
              refine ⟨133244753894688419306524595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88829835929792279537683063 133244753894688419306524595)
              ·
                refine ⟨199867130842032628959786893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 133244753894688419306524595 199867130842032628959786893)
                ·
                  refine ⟨74950174065762235859920085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 199867130842032628959786893 74950174065762235859920085)
                  ·
                    refine ⟨1756644704666302402966877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 74950174065762235859920085 1756644704666302402966877)
                    ·
                      refine ⟨658741764249863401112579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1756644704666302402966877 658741764249863401112579)
                      ·
                        rfl

theorem cell23_1282895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 7, 3].length) (baseStart_1282895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1282895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1282895 prefixEnd_1282895 := by exact prefixLift 1282895
  have htrace : WordTrace (prefixWord ++ tailWord_1282895) baseStart_1282895 baseEnd_1282895 := by
    simpa [prefixWord, tailWord_1282895, baseEnd_1282895] using wordTrace_append hprefix tailTrace_1282895
  have hstable : (prefixWord ++ tailWord_1282895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282895).length < 2 ^ (prefixWord ++ tailWord_1282895).sum := by decide
  have hdescent : baseEnd_1282895 < baseStart_1282895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282905 : List Nat := [1, 2, 1, 2, 2, 4, 1, 1, 1, 2, 6]
def baseStart_1282905 : Nat := 118140960795 + 1282905 * 2 ^ 59
def prefixEnd_1282905 : Nat := 4983230072969 + 3 ^ 40 * 1282905 * 2
def baseEnd_1282905 : Nat := 658746899056408361987533

theorem tailTrace_1282905 : CollatzResearch.WordTrace tailWord_1282905 prefixEnd_1282905 658746899056408361987533 := by
  unfold tailWord_1282905
  simp only [CollatzResearch.WordTrace]
  refine ⟨46791389417261762575450169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31194259611507841716966779 46791389417261762575450169)
  ·
    refine ⟨35093542062946321931587627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46791389417261762575450169 35093542062946321931587627)
    ·
      refine ⟨52640313094419482897381441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35093542062946321931587627 52640313094419482897381441)
      ·
        refine ⟨39480234820814612173036081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52640313094419482897381441 39480234820814612173036081)
        ·
          refine ⟨29610176115610959129777061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39480234820814612173036081 29610176115610959129777061)
          ·
            refine ⟨5551908021677054836833199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29610176115610959129777061 5551908021677054836833199)
            ·
              refine ⟨8327862032515582255249799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5551908021677054836833199 8327862032515582255249799)
              ·
                refine ⟨12491793048773373382874699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8327862032515582255249799 12491793048773373382874699)
                ·
                  refine ⟨18737689573160060074312049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12491793048773373382874699 18737689573160060074312049)
                  ·
                    refine ⟨14053267179870045055734037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18737689573160060074312049 14053267179870045055734037)
                    ·
                      refine ⟨658746899056408361987533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14053267179870045055734037 658746899056408361987533)
                      ·
                        rfl

theorem cell23_1282905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 2, 6].length) (baseStart_1282905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1282905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1282905 prefixEnd_1282905 := by exact prefixLift 1282905
  have htrace : WordTrace (prefixWord ++ tailWord_1282905) baseStart_1282905 baseEnd_1282905 := by
    simpa [prefixWord, tailWord_1282905, baseEnd_1282905] using wordTrace_append hprefix tailTrace_1282905
  have hstable : (prefixWord ++ tailWord_1282905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282905).length < 2 ^ (prefixWord ++ tailWord_1282905).sum := by decide
  have hdescent : baseEnd_1282905 < baseStart_1282905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282919 : List Nat := [1, 1, 5, 1, 2, 3, 3, 1, 6]
def baseStart_1282919 : Nat := 118140960795 + 1282919 * 2 ^ 59
def prefixEnd_1282919 : Nat := 4983230072969 + 3 ^ 40 * 1282919 * 2
def baseEnd_1282919 : Nat := 73194898642841256356941

theorem tailTrace_1282919 : CollatzResearch.WordTrace tailWord_1282919 prefixEnd_1282919 73194898642841256356941 := by
  unfold tailWord_1282919
  simp only [CollatzResearch.WordTrace]
  refine ⟨46791900039211042966459811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31194600026140695310973207 46791900039211042966459811)
  ·
    refine ⟨70187850058816564449689717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46791900039211042966459811 70187850058816564449689717)
    ·
      refine ⟨6580110943014052917158411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 70187850058816564449689717 6580110943014052917158411)
      ·
        refine ⟨9870166414521079375737617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6580110943014052917158411 9870166414521079375737617)
        ·
          refine ⟨7402624810890809531803213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9870166414521079375737617 7402624810890809531803213)
          ·
            refine ⟨2775984304084053574426205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7402624810890809531803213 2775984304084053574426205)
            ·
              refine ⟨1040994114031520090409827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2775984304084053574426205 1040994114031520090409827)
              ·
                refine ⟨1561491171047280135614741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1040994114031520090409827 1561491171047280135614741)
                ·
                  refine ⟨73194898642841256356941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1561491171047280135614741 73194898642841256356941)
                  ·
                    rfl

theorem cell23_1282919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 3, 1, 6].length) (baseStart_1282919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1282919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1282919 prefixEnd_1282919 := by exact prefixLift 1282919
  have htrace : WordTrace (prefixWord ++ tailWord_1282919) baseStart_1282919 baseEnd_1282919 := by
    simpa [prefixWord, tailWord_1282919, baseEnd_1282919] using wordTrace_append hprefix tailTrace_1282919
  have hstable : (prefixWord ++ tailWord_1282919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282919).length < 2 ^ (prefixWord ++ tailWord_1282919).sum := by decide
  have hdescent : baseEnd_1282919 < baseStart_1282919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282929 : List Nat := [1, 2, 2, 2, 1, 4, 2, 2, 3, 1, 3]
def baseStart_1282929 : Nat := 118140960795 + 1282929 * 2 ^ 59
def prefixEnd_1282929 : Nat := 4983230072969 + 3 ^ 40 * 1282929 * 2
def baseEnd_1282929 : Nat := 658759222592116268087423

theorem tailTrace_1282929 : CollatzResearch.WordTrace tailWord_1282929 prefixEnd_1282929 658759222592116268087423 := by
  unfold tailWord_1282929
  simp only [CollatzResearch.WordTrace]
  refine ⟨46792264769174814674323841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31194843179449876449549227 46792264769174814674323841)
  ·
    refine ⟨35094198576881111005742881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46792264769174814674323841 35094198576881111005742881)
    ·
      refine ⟨26320648932660833254307161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35094198576881111005742881 26320648932660833254307161)
      ·
        refine ⟨19740486699495624940730371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26320648932660833254307161 19740486699495624940730371)
        ·
          refine ⟨29610730049243437411095557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19740486699495624940730371 29610730049243437411095557)
          ·
            refine ⟨5552011884233144514580417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29610730049243437411095557 5552011884233144514580417)
            ·
              refine ⟨4164008913174858385935313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5552011884233144514580417 4164008913174858385935313)
              ·
                refine ⟨3123006684881143789451485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4164008913174858385935313 3123006684881143789451485)
                ·
                  refine ⟨1171127506830428921044307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3123006684881143789451485 1171127506830428921044307)
                  ·
                    refine ⟨1756691260245643381566461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1171127506830428921044307 1756691260245643381566461)
                    ·
                      refine ⟨658759222592116268087423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1756691260245643381566461 658759222592116268087423)
                      ·
                        rfl

theorem cell23_1282929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 2, 3, 1, 3].length) (baseStart_1282929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1282929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1282929 prefixEnd_1282929 := by exact prefixLift 1282929
  have htrace : WordTrace (prefixWord ++ tailWord_1282929) baseStart_1282929 baseEnd_1282929 := by
    simpa [prefixWord, tailWord_1282929, baseEnd_1282929] using wordTrace_append hprefix tailTrace_1282929
  have hstable : (prefixWord ++ tailWord_1282929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282929).length < 2 ^ (prefixWord ++ tailWord_1282929).sum := by decide
  have hdescent : baseEnd_1282929 < baseStart_1282929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282935 : List Nat := [1, 1, 3, 1, 1, 2, 1, 2, 2, 5, 4]
def baseStart_1282935 : Nat := 118140960795 + 1282935 * 2 ^ 59
def prefixEnd_1282935 : Nat := 4983230072969 + 3 ^ 40 * 1282935 * 2
def baseEnd_1282935 : Nat := 658762303476043244612395

theorem tailTrace_1282935 : CollatzResearch.WordTrace tailWord_1282935 prefixEnd_1282935 658762303476043244612395 := by
  unfold tailWord_1282935
  simp only [CollatzResearch.WordTrace]
  refine ⟨46792483607153077699042259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31194989071435385132694839 46792483607153077699042259)
  ·
    refine ⟨70188725410729616548563389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46792483607153077699042259 70188725410729616548563389)
    ·
      refine ⟨26320772029023606205711271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70188725410729616548563389 26320772029023606205711271)
      ·
        refine ⟨39481158043535409308566907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26320772029023606205711271 39481158043535409308566907)
        ·
          refine ⟨59221737065303113962850361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39481158043535409308566907 59221737065303113962850361)
          ·
            refine ⟨44416302798977335472137771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59221737065303113962850361 44416302798977335472137771)
            ·
              refine ⟨66624454198466003208206657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44416302798977335472137771 66624454198466003208206657)
              ·
                refine ⟨49968340648849502406154993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66624454198466003208206657 49968340648849502406154993)
                ·
                  refine ⟨37476255486637126804616245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49968340648849502406154993 37476255486637126804616245)
                  ·
                    refine ⟨3513398951872230637932773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37476255486637126804616245 3513398951872230637932773)
                    ·
                      refine ⟨658762303476043244612395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3513398951872230637932773 658762303476043244612395)
                      ·
                        rfl

theorem cell23_1282935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 5, 4].length) (baseStart_1282935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1282935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1282935 prefixEnd_1282935 := by exact prefixLift 1282935
  have htrace : WordTrace (prefixWord ++ tailWord_1282935) baseStart_1282935 baseEnd_1282935 := by
    simpa [prefixWord, tailWord_1282935, baseEnd_1282935] using wordTrace_append hprefix tailTrace_1282935
  have hstable : (prefixWord ++ tailWord_1282935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282935).length < 2 ^ (prefixWord ++ tailWord_1282935).sum := by decide
  have hdescent : baseEnd_1282935 < baseStart_1282935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282983 : List Nat := [1, 1, 6, 1, 4, 1, 1, 2, 1, 5]
def baseStart_1282983 : Nat := 118140960795 + 1282983 * 2 ^ 59
def prefixEnd_1282983 : Nat := 4983230072969 + 3 ^ 40 * 1282983 * 2
def baseEnd_1282983 : Nat := 219595650182486352270725

theorem tailTrace_1282983 : CollatzResearch.WordTrace tailWord_1282983 prefixEnd_1282983 219595650182486352270725 := by
  unfold tailWord_1282983
  simp only [CollatzResearch.WordTrace]
  refine ⟨46794234310979181896789603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31196156207319454597859735 46794234310979181896789603)
  ·
    refine ⟨70191351466468772845184405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46794234310979181896789603 70191351466468772845184405)
    ·
      refine ⟨3290219599990723727118019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 70191351466468772845184405 3290219599990723727118019)
      ·
        refine ⟨4935329399986085590677029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3290219599990723727118019 4935329399986085590677029)
        ·
          refine ⟨925374262497391048251943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4935329399986085590677029 925374262497391048251943)
          ·
            refine ⟨1388061393746086572377915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 925374262497391048251943 1388061393746086572377915)
            ·
              refine ⟨2082092090619129858566873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1388061393746086572377915 2082092090619129858566873)
              ·
                refine ⟨1561569067964347393925155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2082092090619129858566873 1561569067964347393925155)
                ·
                  refine ⟨2342353601946521090887733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1561569067964347393925155 2342353601946521090887733)
                  ·
                    refine ⟨219595650182486352270725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2342353601946521090887733 219595650182486352270725)
                    ·
                      rfl

theorem cell23_1282983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 2, 1, 5].length) (baseStart_1282983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1282983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1282983 prefixEnd_1282983 := by exact prefixLift 1282983
  have htrace : WordTrace (prefixWord ++ tailWord_1282983) baseStart_1282983 baseEnd_1282983 := by
    simpa [prefixWord, tailWord_1282983, baseEnd_1282983] using wordTrace_append hprefix tailTrace_1282983
  have hstable : (prefixWord ++ tailWord_1282983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282983).length < 2 ^ (prefixWord ++ tailWord_1282983).sum := by decide
  have hdescent : baseEnd_1282983 < baseStart_1282983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282996 : List Nat := [2, 5, 2, 1, 1, 2, 1, 2, 1, 6]
def baseStart_1282996 : Nat := 118140960795 + 1282996 * 2 ^ 59
def prefixEnd_1282996 : Nat := 4983230072969 + 3 ^ 40 * 1282996 * 2
def baseEnd_1282996 : Nat := 219597875265322501983205

theorem tailTrace_1282996 : CollatzResearch.WordTrace tailWord_1282996 prefixEnd_1282996 219597875265322501983205 := by
  unfold tailWord_1282996
  simp only [CollatzResearch.WordTrace]
  refine ⟨23397354229966042558506421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31196472306621390078008561 23397354229966042558506421)
  ·
    refine ⟨2193501959059316489859977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23397354229966042558506421 2193501959059316489859977)
    ·
      refine ⟨1645126469294487367394983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2193501959059316489859977 1645126469294487367394983)
      ·
        refine ⟨2467689703941731051092475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1645126469294487367394983 2467689703941731051092475)
        ·
          refine ⟨3701534555912596576638713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2467689703941731051092475 3701534555912596576638713)
          ·
            refine ⟨2776150916934447432479035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3701534555912596576638713 2776150916934447432479035)
            ·
              refine ⟨4164226375401671148718553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2776150916934447432479035 4164226375401671148718553)
              ·
                refine ⟨3123169781551253361538915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4164226375401671148718553 3123169781551253361538915)
                ·
                  refine ⟨4684754672326880042308373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3123169781551253361538915 4684754672326880042308373)
                  ·
                    refine ⟨219597875265322501983205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4684754672326880042308373 219597875265322501983205)
                    ·
                      rfl

theorem cell23_1282996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_1282996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1282996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1282996 prefixEnd_1282996 := by exact prefixLift 1282996
  have htrace : WordTrace (prefixWord ++ tailWord_1282996) baseStart_1282996 baseEnd_1282996 := by
    simpa [prefixWord, tailWord_1282996, baseEnd_1282996] using wordTrace_append hprefix tailTrace_1282996
  have hstable : (prefixWord ++ tailWord_1282996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282996).length < 2 ^ (prefixWord ++ tailWord_1282996).sum := by decide
  have hdescent : baseEnd_1282996 < baseStart_1282996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283022 : List Nat := [4, 1, 1, 1, 2, 3, 1, 1, 2, 7]
def baseStart_1283022 : Nat := 118140960795 + 1283022 * 2 ^ 59
def prefixEnd_1283022 : Nat := 4983230072969 + 3 ^ 40 * 1283022 * 2
def baseEnd_1283022 : Nat := 219602325430994801408165

theorem tailTrace_1283022 : CollatzResearch.WordTrace tailWord_1283022 prefixEnd_1283022 219602325430994801408165 := by
  unfold tailWord_1283022
  simp only [CollatzResearch.WordTrace]
  refine ⟨5849457094729736444682415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31197104505225261038306213 5849457094729736444682415)
  ·
    refine ⟨8774185642094604667023623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5849457094729736444682415 8774185642094604667023623)
    ·
      refine ⟨13161278463141907000535435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8774185642094604667023623 13161278463141907000535435)
      ·
        refine ⟨19741917694712860500803153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13161278463141907000535435 19741917694712860500803153)
        ·
          refine ⟨14806438271034645375602365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19741917694712860500803153 14806438271034645375602365)
          ·
            refine ⟨5552414351637992015850887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14806438271034645375602365 5552414351637992015850887)
            ·
              refine ⟨8328621527456988023776331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5552414351637992015850887 8328621527456988023776331)
              ·
                refine ⟨12492932291185482035664497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8328621527456988023776331 12492932291185482035664497)
                ·
                  refine ⟨9369699218389111526748373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12492932291185482035664497 9369699218389111526748373)
                  ·
                    refine ⟨219602325430994801408165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9369699218389111526748373 219602325430994801408165)
                    ·
                      rfl

theorem cell23_1283022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 2, 7].length) (baseStart_1283022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1283022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1283022 prefixEnd_1283022 := by exact prefixLift 1283022
  have htrace : WordTrace (prefixWord ++ tailWord_1283022) baseStart_1283022 baseEnd_1283022 := by
    simpa [prefixWord, tailWord_1283022, baseEnd_1283022] using wordTrace_append hprefix tailTrace_1283022
  have hstable : (prefixWord ++ tailWord_1283022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283022).length < 2 ^ (prefixWord ++ tailWord_1283022).sum := by decide
  have hdescent : baseEnd_1283022 < baseStart_1283022 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283093 : List Nat := [1, 3, 2, 1, 4, 3, 1, 1, 1, 4, 2]
def baseStart_1283093 : Nat := 118140960795 + 1283093 * 2 ^ 59
def prefixEnd_1283093 : Nat := 4983230072969 + 3 ^ 40 * 1283093 * 2
def baseEnd_1283093 : Nat := 658843433419453626436669

theorem tailTrace_1283093 : CollatzResearch.WordTrace tailWord_1283093 prefixEnd_1283093 658843433419453626436669 := by
  unfold tailWord_1283093
  simp only [CollatzResearch.WordTrace]
  refine ⟨46798246340580670683293933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31198830893720447122195955 46798246340580670683293933)
  ·
    refine ⟨17549342377717751506235225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46798246340580670683293933 17549342377717751506235225)
    ·
      refine ⟨13162006783288313629676419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17549342377717751506235225 13162006783288313629676419)
      ·
        refine ⟨19743010174932470444514629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13162006783288313629676419 19743010174932470444514629)
        ·
          refine ⟨3701814407799838208346493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19743010174932470444514629 3701814407799838208346493)
          ·
            refine ⟨1388180402924939328129935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3701814407799838208346493 1388180402924939328129935)
            ·
              refine ⟨2082270604387408992194903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1388180402924939328129935 2082270604387408992194903)
              ·
                refine ⟨3123405906581113488292355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2082270604387408992194903 3123405906581113488292355)
                ·
                  refine ⟨4685108859871670232438533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3123405906581113488292355 4685108859871670232438533)
                  ·
                    refine ⟨878457911225938168582225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4685108859871670232438533 878457911225938168582225)
                    ·
                      refine ⟨658843433419453626436669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 878457911225938168582225 658843433419453626436669)
                      ·
                        rfl

theorem cell23_1283093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 1, 1, 4, 2].length) (baseStart_1283093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1283093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1283093 prefixEnd_1283093 := by exact prefixLift 1283093
  have htrace : WordTrace (prefixWord ++ tailWord_1283093) baseStart_1283093 baseEnd_1283093 := by
    simpa [prefixWord, tailWord_1283093, baseEnd_1283093] using wordTrace_append hprefix tailTrace_1283093
  have hstable : (prefixWord ++ tailWord_1283093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283093).length < 2 ^ (prefixWord ++ tailWord_1283093).sum := by decide
  have hdescent : baseEnd_1283093 < baseStart_1283093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283129 : List Nat := [1, 2, 1, 5, 2, 1, 1, 1, 4, 5]
def baseStart_1283129 : Nat := 118140960795 + 1283129 * 2 ^ 59
def prefixEnd_1283129 : Nat := 4983230072969 + 3 ^ 40 * 1283129 * 2
def baseEnd_1283129 : Nat := 219620639574338495195501

theorem tailTrace_1283129 : CollatzResearch.WordTrace tailWord_1283129 prefixEnd_1283129 219620639574338495195501 := by
  unfold tailWord_1283129
  simp only [CollatzResearch.WordTrace]
  refine ⟨46799559368450248831604441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31199706245633499221069627 46799559368450248831604441)
  ·
    refine ⟨35099669526337686623703331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46799559368450248831604441 35099669526337686623703331)
    ·
      refine ⟨52649504289506529935554997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35099669526337686623703331 52649504289506529935554997)
      ·
        refine ⟨4935891027141237181458281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 52649504289506529935554997 4935891027141237181458281)
        ·
          refine ⟨3701918270355927886093711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4935891027141237181458281 3701918270355927886093711)
          ·
            refine ⟨5552877405533891829140567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3701918270355927886093711 5552877405533891829140567)
            ·
              refine ⟨8329316108300837743710851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5552877405533891829140567 8329316108300837743710851)
              ·
                refine ⟨12493974162451256615566277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8329316108300837743710851 12493974162451256615566277)
                ·
                  refine ⟨2342620155459610615418677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12493974162451256615566277 2342620155459610615418677)
                  ·
                    refine ⟨219620639574338495195501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2342620155459610615418677 219620639574338495195501)
                    ·
                      rfl

theorem cell23_1283129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 4, 5].length) (baseStart_1283129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1283129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1283129 prefixEnd_1283129 := by exact prefixLift 1283129
  have htrace : WordTrace (prefixWord ++ tailWord_1283129) baseStart_1283129 baseEnd_1283129 := by
    simpa [prefixWord, tailWord_1283129, baseEnd_1283129] using wordTrace_append hprefix tailTrace_1283129
  have hstable : (prefixWord ++ tailWord_1283129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283129).length < 2 ^ (prefixWord ++ tailWord_1283129).sum := by decide
  have hdescent : baseEnd_1283129 < baseStart_1283129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283133 : List Nat := [1, 4, 1, 3, 1, 3, 3, 2, 5]
def baseStart_1283133 : Nat := 118140960795 + 1283133 * 2 ^ 59
def prefixEnd_1283133 : Nat := 4983230072969 + 3 ^ 40 * 1283133 * 2
def baseEnd_1283133 : Nat := 73207108071737052215165

theorem tailTrace_1283133 : CollatzResearch.WordTrace tailWord_1283133 prefixEnd_1283133 73207108071737052215165 := by
  unfold tailWord_1283133
  simp only [CollatzResearch.WordTrace]
  refine ⟨46799705260435757514750053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31199803506957171676500035 46799705260435757514750053)
  ·
    refine ⟨8774944736331704534015635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46799705260435757514750053 8774944736331704534015635)
    ·
      refine ⟨13162417104497556801023453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8774944736331704534015635 13162417104497556801023453)
      ·
        refine ⟨4935906414186583800383795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13162417104497556801023453 4935906414186583800383795)
        ·
          refine ⟨7403859621279875700575693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4935906414186583800383795 7403859621279875700575693)
          ·
            refine ⟨2776447357979953387715885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7403859621279875700575693 2776447357979953387715885)
            ·
              refine ⟨1041167759242482520393457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2776447357979953387715885 1041167759242482520393457)
              ·
                refine ⟨780875819431861890295093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1041167759242482520393457 780875819431861890295093)
                ·
                  refine ⟨73207108071737052215165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 780875819431861890295093 73207108071737052215165)
                  ·
                    rfl

theorem cell23_1283133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 3, 2, 5].length) (baseStart_1283133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1283133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1283133 prefixEnd_1283133 := by exact prefixLift 1283133
  have htrace : WordTrace (prefixWord ++ tailWord_1283133) baseStart_1283133 baseEnd_1283133 := by
    simpa [prefixWord, tailWord_1283133, baseEnd_1283133] using wordTrace_append hprefix tailTrace_1283133
  have hstable : (prefixWord ++ tailWord_1283133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283133).length < 2 ^ (prefixWord ++ tailWord_1283133).sum := by decide
  have hdescent : baseEnd_1283133 < baseStart_1283133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283152 : List Nat := [2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 5]
def baseStart_1283152 : Nat := 118140960795 + 1283152 * 2 ^ 59
def prefixEnd_1283152 : Nat := 4983230072969 + 3 ^ 40 * 1283152 * 2
def baseEnd_1283152 : Nat := 658873728778068895598897

theorem tailTrace_1283152 : CollatzResearch.WordTrace tailWord_1283152 prefixEnd_1283152 658873728778068895598897 := by
  unfold tailWord_1283152
  simp only [CollatzResearch.WordTrace]
  refine ⟨23400199123683461879845855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31200265498244615839794473 23400199123683461879845855)
  ·
    refine ⟨35100298685525192819768783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23400199123683461879845855 35100298685525192819768783)
    ·
      refine ⟨52650448028287789229653175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35100298685525192819768783 52650448028287789229653175)
      ·
        refine ⟨78975672042431683844479763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52650448028287789229653175 78975672042431683844479763)
        ·
          refine ⟨118463508063647525766719645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78975672042431683844479763 118463508063647525766719645)
          ·
            refine ⟨44423815523867822162519867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 118463508063647525766719645 44423815523867822162519867)
            ·
              refine ⟨66635723285801733243779801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44423815523867822162519867 66635723285801733243779801)
              ·
                refine ⟨49976792464351299932834851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66635723285801733243779801 49976792464351299932834851)
                ·
                  refine ⟨74965188696526949899252277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49976792464351299932834851 74965188696526949899252277)
                  ·
                    refine ⟨7027986440299401553054901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 74965188696526949899252277 7027986440299401553054901)
                    ·
                      refine ⟨658873728778068895598897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7027986440299401553054901 658873728778068895598897)
                      ·
                        rfl

theorem cell23_1283152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 5].length) (baseStart_1283152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1283152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1283152 prefixEnd_1283152 := by exact prefixLift 1283152
  have htrace : WordTrace (prefixWord ++ tailWord_1283152) baseStart_1283152 baseEnd_1283152 := by
    simpa [prefixWord, tailWord_1283152, baseEnd_1283152] using wordTrace_append hprefix tailTrace_1283152
  have hstable : (prefixWord ++ tailWord_1283152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283152).length < 2 ^ (prefixWord ++ tailWord_1283152).sum := by decide
  have hdescent : baseEnd_1283152 < baseStart_1283152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283159 : List Nat := [1, 1, 3, 2, 2, 1, 1, 3, 5, 4]
def baseStart_1283159 : Nat := 118140960795 + 1283159 * 2 ^ 59
def prefixEnd_1283159 : Nat := 4983230072969 + 3 ^ 40 * 1283159 * 2
def baseEnd_1283159 : Nat := 219625774380883456070455

theorem tailTrace_1283159 : CollatzResearch.WordTrace tailWord_1283159 prefixEnd_1283159 219625774380883456070455 := by
  unfold tailWord_1283159
  simp only [CollatzResearch.WordTrace]
  refine ⟨46800653558341563955196531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31200435705561042636797687 46800653558341563955196531)
  ·
    refine ⟨70200980337512345932794797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46800653558341563955196531 70200980337512345932794797)
    ·
      refine ⟨26325367626567129724798049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70200980337512345932794797 26325367626567129724798049)
      ·
        refine ⟨19744025719925347293598537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26325367626567129724798049 19744025719925347293598537)
        ·
          refine ⟨14808019289944010470198903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19744025719925347293598537 14808019289944010470198903)
          ·
            refine ⟨22212028934916015705298355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14808019289944010470198903 22212028934916015705298355)
            ·
              refine ⟨33318043402374023557947533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22212028934916015705298355 33318043402374023557947533)
              ·
                refine ⟨12494266275890258834230325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33318043402374023557947533 12494266275890258834230325)
                ·
                  refine ⟨1171337463364711765709093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12494266275890258834230325 1171337463364711765709093)
                  ·
                    refine ⟨219625774380883456070455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1171337463364711765709093 219625774380883456070455)
                    ·
                      rfl

theorem cell23_1283159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 5, 4].length) (baseStart_1283159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1283159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1283159 prefixEnd_1283159 := by exact prefixLift 1283159
  have htrace : WordTrace (prefixWord ++ tailWord_1283159) baseStart_1283159 baseEnd_1283159 := by
    simpa [prefixWord, tailWord_1283159, baseEnd_1283159] using wordTrace_append hprefix tailTrace_1283159
  have hstable : (prefixWord ++ tailWord_1283159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283159).length < 2 ^ (prefixWord ++ tailWord_1283159).sum := by decide
  have hdescent : baseEnd_1283159 < baseStart_1283159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283169 : List Nat := [1, 2, 3, 1, 1, 2, 2, 3, 1, 4, 3]
def baseStart_1283169 : Nat := 118140960795 + 1283169 * 2 ^ 59
def prefixEnd_1283169 : Nat := 4983230072969 + 3 ^ 40 * 1283169 * 2
def baseEnd_1283169 : Nat := 658882457949195329086319

theorem tailTrace_1283169 : CollatzResearch.WordTrace tailWord_1283169 prefixEnd_1283169 658882457949195329086319 := by
  unfold tailWord_1283169
  simp only [CollatzResearch.WordTrace]
  refine ⟨46801018288305335663060561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31200678858870223775373707 46801018288305335663060561)
  ·
    refine ⟨35100763716229001747295421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46801018288305335663060561 35100763716229001747295421)
    ·
      refine ⟨13162786393585875655235783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35100763716229001747295421 13162786393585875655235783)
      ·
        refine ⟨19744179590378813482853675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13162786393585875655235783 19744179590378813482853675)
        ·
          refine ⟨29616269385568220224280513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19744179590378813482853675 29616269385568220224280513)
          ·
            refine ⟨22212202039176165168210385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29616269385568220224280513 22212202039176165168210385)
            ·
              refine ⟨16659151529382123876157789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22212202039176165168210385 16659151529382123876157789)
              ·
                refine ⟨6247181823518296453559171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16659151529382123876157789 6247181823518296453559171)
                ·
                  refine ⟨9370772735277444680338757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6247181823518296453559171 9370772735277444680338757)
                  ·
                    refine ⟨1757019887864520877563517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9370772735277444680338757 1757019887864520877563517)
                    ·
                      refine ⟨658882457949195329086319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1757019887864520877563517 658882457949195329086319)
                      ·
                        rfl

theorem cell23_1283169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 3, 1, 4, 3].length) (baseStart_1283169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1283169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1283169 prefixEnd_1283169 := by exact prefixLift 1283169
  have htrace : WordTrace (prefixWord ++ tailWord_1283169) baseStart_1283169 baseEnd_1283169 := by
    simpa [prefixWord, tailWord_1283169, baseEnd_1283169] using wordTrace_append hprefix tailTrace_1283169
  have hstable : (prefixWord ++ tailWord_1283169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283169).length < 2 ^ (prefixWord ++ tailWord_1283169).sum := by decide
  have hdescent : baseEnd_1283169 < baseStart_1283169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283186 : List Nat := [3, 2, 1, 2, 2, 1, 1, 4, 2, 2, 3]
def baseStart_1283186 : Nat := 118140960795 + 1283186 * 2 ^ 59
def prefixEnd_1283186 : Nat := 4983230072969 + 3 ^ 40 * 1283186 * 2
def baseEnd_1283186 : Nat := 658891187120321762573741

theorem tailTrace_1283186 : CollatzResearch.WordTrace tailWord_1283186 prefixEnd_1283186 658891187120321762573741 := by
  unfold tailWord_1283186
  simp only [CollatzResearch.WordTrace]
  refine ⟨11700409582310936891607353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31201092219495831710952941 11700409582310936891607353)
  ·
    refine ⟨8775307186733202668705515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11700409582310936891607353 8775307186733202668705515)
    ·
      refine ⟨13162960780099804003058273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8775307186733202668705515 13162960780099804003058273)
      ·
        refine ⟨9872220585074853002293705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13162960780099804003058273 9872220585074853002293705)
        ·
          refine ⟨7404165438806139751720279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9872220585074853002293705 7404165438806139751720279)
          ·
            refine ⟨11106248158209209627580419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7404165438806139751720279 11106248158209209627580419)
            ·
              refine ⟨16659372237313814441370629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11106248158209209627580419 16659372237313814441370629)
              ·
                refine ⟨3123632294496340207756993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16659372237313814441370629 3123632294496340207756993)
                ·
                  refine ⟨2342724220872255155817745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3123632294496340207756993 2342724220872255155817745)
                  ·
                    refine ⟨1757043165654191366863309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2342724220872255155817745 1757043165654191366863309)
                    ·
                      refine ⟨658891187120321762573741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1757043165654191366863309 658891187120321762573741)
                      ·
                        rfl

theorem cell23_1283186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 4, 2, 2, 3].length) (baseStart_1283186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1283186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1283186 prefixEnd_1283186 := by exact prefixLift 1283186
  have htrace : WordTrace (prefixWord ++ tailWord_1283186) baseStart_1283186 baseEnd_1283186 := by
    simpa [prefixWord, tailWord_1283186, baseEnd_1283186] using wordTrace_append hprefix tailTrace_1283186
  have hstable : (prefixWord ++ tailWord_1283186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283186).length < 2 ^ (prefixWord ++ tailWord_1283186).sum := by decide
  have hdescent : baseEnd_1283186 < baseStart_1283186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283219 : List Nat := [1, 1, 1, 2, 1, 2, 6, 1, 3, 5]
def baseStart_1283219 : Nat := 118140960795 + 1283219 * 2 ^ 59
def prefixEnd_1283219 : Nat := 4983230072969 + 3 ^ 40 * 1283219 * 2
def baseEnd_1283219 : Nat := 219636043993973377820363

theorem tailTrace_1283219 : CollatzResearch.WordTrace tailWord_1283219 prefixEnd_1283219 219636043993973377820363 := by
  unfold tailWord_1283219
  simp only [CollatzResearch.WordTrace]
  refine ⟨46802841938124194202380711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31201894625416129468253807 46802841938124194202380711)
  ·
    refine ⟨70204262907186291303571067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46802841938124194202380711 70204262907186291303571067)
    ·
      refine ⟨105306394360779436955356601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70204262907186291303571067 105306394360779436955356601)
      ·
        refine ⟨78979795770584577716517451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105306394360779436955356601 78979795770584577716517451)
        ·
          refine ⟨118469693655876866574776177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78979795770584577716517451 118469693655876866574776177)
          ·
            refine ⟨88852270241907649931082133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118469693655876866574776177 88852270241907649931082133)
            ·
              refine ⟨4164950167589421090519475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 88852270241907649931082133 4164950167589421090519475)
              ·
                refine ⟨6247425251384131635779213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4164950167589421090519475 6247425251384131635779213)
                ·
                  refine ⟨2342784469269049363417205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6247425251384131635779213 2342784469269049363417205)
                  ·
                    refine ⟨219636043993973377820363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2342784469269049363417205 219636043993973377820363)
                    ·
                      rfl

theorem cell23_1283219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 1, 3, 5].length) (baseStart_1283219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1283219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1283219 prefixEnd_1283219 := by exact prefixLift 1283219
  have htrace : WordTrace (prefixWord ++ tailWord_1283219) baseStart_1283219 baseEnd_1283219 := by
    simpa [prefixWord, tailWord_1283219, baseEnd_1283219] using wordTrace_append hprefix tailTrace_1283219
  have hstable : (prefixWord ++ tailWord_1283219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283219).length < 2 ^ (prefixWord ++ tailWord_1283219).sum := by decide
  have hdescent : baseEnd_1283219 < baseStart_1283219 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283250 : List Nat := [3, 2, 1, 1, 1, 4, 2, 4, 1, 1, 3]
def baseStart_1283250 : Nat := 118140960795 + 1283250 * 2 ^ 59
def prefixEnd_1283250 : Nat := 4983230072969 + 3 ^ 40 * 1283250 * 2
def baseEnd_1283250 : Nat := 658924049882209512173447

theorem tailTrace_1283250 : CollatzResearch.WordTrace tailWord_1283250 prefixEnd_1283250 658924049882209512173447 := by
  unfold tailWord_1283250
  simp only [CollatzResearch.WordTrace]
  refine ⟨11700993150252971624189801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31202648400674590997839469 11700993150252971624189801)
  ·
    refine ⟨8775744862689728718142351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11700993150252971624189801 8775744862689728718142351)
    ·
      refine ⟨13163617294034593077213527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8775744862689728718142351 13163617294034593077213527)
      ·
        refine ⟨19745425941051889615820291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13163617294034593077213527 19745425941051889615820291)
        ·
          refine ⟨29618138911577834423730437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19745425941051889615820291 29618138911577834423730437)
          ·
            refine ⟨5553401045920843954449457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29618138911577834423730437 5553401045920843954449457)
            ·
              refine ⟨4165050784440632965837093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5553401045920843954449457 4165050784440632965837093)
              ·
                refine ⟨780947022082618681094455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4165050784440632965837093 780947022082618681094455)
                ·
                  refine ⟨1171420533123928021641683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 780947022082618681094455 1171420533123928021641683)
                  ·
                    refine ⟨1757130799685892032462525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1171420533123928021641683 1757130799685892032462525)
                    ·
                      refine ⟨658924049882209512173447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1757130799685892032462525 658924049882209512173447)
                      ·
                        rfl

theorem cell23_1283250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 4, 1, 1, 3].length) (baseStart_1283250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1283250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1283250 prefixEnd_1283250 := by exact prefixLift 1283250
  have htrace : WordTrace (prefixWord ++ tailWord_1283250) baseStart_1283250 baseEnd_1283250 := by
    simpa [prefixWord, tailWord_1283250, baseEnd_1283250] using wordTrace_append hprefix tailTrace_1283250
  have hstable : (prefixWord ++ tailWord_1283250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283250).length < 2 ^ (prefixWord ++ tailWord_1283250).sum := by decide
  have hdescent : baseEnd_1283250 < baseStart_1283250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283259 : List Nat := [1, 1, 1, 1, 1, 2, 4, 1, 2, 6, 3]
def baseStart_1283259 : Nat := 118140960795 + 1283259 * 2 ^ 59
def prefixEnd_1283259 : Nat := 4983230072969 + 3 ^ 40 * 1283259 * 2
def baseEnd_1283259 : Nat := 658928671208099976960905

theorem tailTrace_1283259 : CollatzResearch.WordTrace tailWord_1283259 prefixEnd_1283259 658928671208099976960905 := by
  unfold tailWord_1283259
  simp only [CollatzResearch.WordTrace]
  refine ⟨46804300857979281033836831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31202867238652854022557887 46804300857979281033836831)
  ·
    refine ⟨70206451286968921550755247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46804300857979281033836831 70206451286968921550755247)
    ·
      refine ⟨105309676930453382326132871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70206451286968921550755247 105309676930453382326132871)
      ·
        refine ⟨157964515395680073489199307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105309676930453382326132871 157964515395680073489199307)
        ·
          refine ⟨236946773093520110233798961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157964515395680073489199307 236946773093520110233798961)
          ·
            refine ⟨177710079820140082675349221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 236946773093520110233798961 177710079820140082675349221)
            ·
              refine ⟨33320639966276265501627979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 177710079820140082675349221 33320639966276265501627979)
              ·
                refine ⟨49980959949414398252441969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33320639966276265501627979 49980959949414398252441969)
                ·
                  refine ⟨37485719962060798689331477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49980959949414398252441969 37485719962060798689331477)
                  ·
                    refine ⟨1757143123221599938562413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 37485719962060798689331477 1757143123221599938562413)
                    ·
                      refine ⟨658928671208099976960905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1757143123221599938562413 658928671208099976960905)
                      ·
                        rfl

theorem cell23_1283259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 6, 3].length) (baseStart_1283259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1283259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1283259 prefixEnd_1283259 := by exact prefixLift 1283259
  have htrace : WordTrace (prefixWord ++ tailWord_1283259) baseStart_1283259 baseEnd_1283259 := by
    simpa [prefixWord, tailWord_1283259, baseEnd_1283259] using wordTrace_append hprefix tailTrace_1283259
  have hstable : (prefixWord ++ tailWord_1283259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283259).length < 2 ^ (prefixWord ++ tailWord_1283259).sum := by decide
  have hdescent : baseEnd_1283259 < baseStart_1283259 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283319 : List Nat := [1, 1, 3, 1, 1, 1, 2, 2, 4, 2, 5]
def baseStart_1283319 : Nat := 118140960795 + 1283319 * 2 ^ 59
def prefixEnd_1283319 : Nat := 4983230072969 + 3 ^ 40 * 1283319 * 2
def baseEnd_1283319 : Nat := 658959480047369742210629

theorem tailTrace_1283319 : CollatzResearch.WordTrace tailWord_1283319 prefixEnd_1283319 658959480047369742210629 := by
  unfold tailWord_1283319
  simp only [CollatzResearch.WordTrace]
  refine ⟨46806489237761911281021011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31204326158507940854014007 46806489237761911281021011)
  ·
    refine ⟨70209733856642866921531517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46806489237761911281021011 70209733856642866921531517)
    ·
      refine ⟨26328650196241075095574319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70209733856642866921531517 26328650196241075095574319)
      ·
        refine ⟨39492975294361612643361479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26328650196241075095574319 39492975294361612643361479)
        ·
          refine ⟨59239462941542418965042219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39492975294361612643361479 59239462941542418965042219)
          ·
            refine ⟨88859194412313628447563329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59239462941542418965042219 88859194412313628447563329)
            ·
              refine ⟨66644395809235221335672497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88859194412313628447563329 66644395809235221335672497)
              ·
                refine ⟨49983296856926416001754373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66644395809235221335672497 49983296856926416001754373)
                ·
                  refine ⟨9371868160673703000328945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49983296856926416001754373 9371868160673703000328945)
                  ·
                    refine ⟨7028901120505277250246709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9371868160673703000328945 7028901120505277250246709)
                    ·
                      refine ⟨658959480047369742210629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7028901120505277250246709 658959480047369742210629)
                      ·
                        rfl

theorem cell23_1283319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 4, 2, 5].length) (baseStart_1283319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1283319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1283319 prefixEnd_1283319 := by exact prefixLift 1283319
  have htrace : WordTrace (prefixWord ++ tailWord_1283319) baseStart_1283319 baseEnd_1283319 := by
    simpa [prefixWord, tailWord_1283319, baseEnd_1283319] using wordTrace_append hprefix tailTrace_1283319
  have hstable : (prefixWord ++ tailWord_1283319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283319).length < 2 ^ (prefixWord ++ tailWord_1283319).sum := by decide
  have hdescent : baseEnd_1283319 < baseStart_1283319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283333 : List Nat := [1, 3, 1, 1, 2, 1, 5, 1, 3, 3, 2]
def baseStart_1283333 : Nat := 118140960795 + 1283333 * 2 ^ 59
def prefixEnd_1283333 : Nat := 4983230072969 + 3 ^ 40 * 1283333 * 2
def baseEnd_1283333 : Nat := 658966668776532687435565

theorem tailTrace_1283333 : CollatzResearch.WordTrace tailWord_1283333 prefixEnd_1283333 658966668776532687435565 := by
  unfold tailWord_1283333
  simp only [CollatzResearch.WordTrace]
  refine ⟨46806999859711191672030653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31204666573140794448020435 46806999859711191672030653)
  ·
    refine ⟨17552624947391696877011495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46806999859711191672030653 17552624947391696877011495)
    ·
      refine ⟨26328937421087545315517243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17552624947391696877011495 26328937421087545315517243)
      ·
        refine ⟨39493406131631317973275865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26328937421087545315517243 39493406131631317973275865)
        ·
          refine ⟨29620054598723488479956899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39493406131631317973275865 29620054598723488479956899)
          ·
            refine ⟨44430081898085232719935349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29620054598723488479956899 44430081898085232719935349)
            ·
              refine ⟨4165320177945490567493939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44430081898085232719935349 4165320177945490567493939)
              ·
                refine ⟨6247980266918235851240909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4165320177945490567493939 6247980266918235851240909)
                ·
                  refine ⟨2342992600094338444215341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6247980266918235851240909 2342992600094338444215341)
                  ·
                    refine ⟨878622225035376916580753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2342992600094338444215341 878622225035376916580753)
                    ·
                      refine ⟨658966668776532687435565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 878622225035376916580753 658966668776532687435565)
                      ·
                        rfl

theorem cell23_1283333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 1, 3, 3, 2].length) (baseStart_1283333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1283333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1283333 prefixEnd_1283333 := by exact prefixLift 1283333
  have htrace : WordTrace (prefixWord ++ tailWord_1283333) baseStart_1283333 baseEnd_1283333 := by
    simpa [prefixWord, tailWord_1283333, baseEnd_1283333] using wordTrace_append hprefix tailTrace_1283333
  have hstable : (prefixWord ++ tailWord_1283333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283333).length < 2 ^ (prefixWord ++ tailWord_1283333).sum := by decide
  have hdescent : baseEnd_1283333 < baseStart_1283333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283357 : List Nat := [1, 4, 2, 3, 1, 2, 2, 2, 2, 1, 3]
def baseStart_1283357 : Nat := 118140960795 + 1283357 * 2 ^ 59
def prefixEnd_1283357 : Nat := 4983230072969 + 3 ^ 40 * 1283357 * 2
def baseEnd_1283357 : Nat := 658978992312240593535455

theorem tailTrace_1283357 : CollatzResearch.WordTrace tailWord_1283357 prefixEnd_1283357 658978992312240593535455 := by
  unfold tailWord_1283357
  simp only [CollatzResearch.WordTrace]
  refine ⟨46807875211624243770904325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31205250141082829180602883 46807875211624243770904325)
  ·
    refine ⟨8776476602179545707044561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46807875211624243770904325 8776476602179545707044561)
    ·
      refine ⟨6582357451634659280283421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8776476602179545707044561 6582357451634659280283421)
      ·
        refine ⟨2468384044362997230106283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6582357451634659280283421 2468384044362997230106283)
        ·
          refine ⟨3702576066544495845159425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2468384044362997230106283 3702576066544495845159425)
          ·
            refine ⟨2776932049908371883869569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3702576066544495845159425 2776932049908371883869569)
            ·
              refine ⟨2082699037431278912902177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2776932049908371883869569 2082699037431278912902177)
              ·
                refine ⟨1562024278073459184676633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2082699037431278912902177 1562024278073459184676633)
                ·
                  refine ⟨1171518208555094388507475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1562024278073459184676633 1171518208555094388507475)
                  ·
                    refine ⟨1757277312832641582761213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1171518208555094388507475 1757277312832641582761213)
                    ·
                      refine ⟨658978992312240593535455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1757277312832641582761213 658978992312240593535455)
                      ·
                        rfl

theorem cell23_1283357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_1283357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1283357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1283357 prefixEnd_1283357 := by exact prefixLift 1283357
  have htrace : WordTrace (prefixWord ++ tailWord_1283357) baseStart_1283357 baseEnd_1283357 := by
    simpa [prefixWord, tailWord_1283357, baseEnd_1283357] using wordTrace_append hprefix tailTrace_1283357
  have hstable : (prefixWord ++ tailWord_1283357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283357).length < 2 ^ (prefixWord ++ tailWord_1283357).sum := by decide
  have hdescent : baseEnd_1283357 < baseStart_1283357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283373 : List Nat := [1, 5, 3, 1, 1, 1, 1, 1, 1, 8]
def baseStart_1283373 : Nat := 118140960795 + 1283373 * 2 ^ 59
def prefixEnd_1283373 : Nat := 4983230072969 + 3 ^ 40 * 1283373 * 2
def baseEnd_1283373 : Nat := 219662402667570843645127

theorem tailTrace_1283373 : CollatzResearch.WordTrace tailWord_1283373 prefixEnd_1283373 219662402667570843645127 := by
  unfold tailWord_1283373
  simp only [CollatzResearch.WordTrace]
  refine ⟨46808458779566278503486773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31205639186377519002324515 46808458779566278503486773)
  ·
    refine ⟨4388293010584338609701885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46808458779566278503486773 4388293010584338609701885)
    ·
      refine ⟨1645609878969126978638207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4388293010584338609701885 1645609878969126978638207)
      ·
        refine ⟨2468414818453690467957311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1645609878969126978638207 2468414818453690467957311)
        ·
          refine ⟨3702622227680535701935967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2468414818453690467957311 3702622227680535701935967)
          ·
            refine ⟨5553933341520803552903951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3702622227680535701935967 5553933341520803552903951)
            ·
              refine ⟨8330900012281205329355927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5553933341520803552903951 8330900012281205329355927)
              ·
                refine ⟨12496350018421807994033891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8330900012281205329355927 12496350018421807994033891)
                ·
                  refine ⟨18744525027632711991050837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12496350018421807994033891 18744525027632711991050837)
                  ·
                    refine ⟨219662402667570843645127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 18744525027632711991050837 219662402667570843645127)
                    ·
                      rfl

theorem cell23_1283373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_1283373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1283373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1283373 prefixEnd_1283373 := by exact prefixLift 1283373
  have htrace : WordTrace (prefixWord ++ tailWord_1283373) baseStart_1283373 baseEnd_1283373 := by
    simpa [prefixWord, tailWord_1283373, baseEnd_1283373] using wordTrace_append hprefix tailTrace_1283373
  have hstable : (prefixWord ++ tailWord_1283373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283373).length < 2 ^ (prefixWord ++ tailWord_1283373).sum := by decide
  have hdescent : baseEnd_1283373 < baseStart_1283373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283376 : List Nat := [2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 4]
def baseStart_1283376 : Nat := 118140960795 + 1283376 * 2 ^ 59
def prefixEnd_1283376 : Nat := 4983230072969 + 3 ^ 40 * 1283376 * 2
def baseEnd_1283376 : Nat := 658988748444676019197867

theorem tailTrace_1283376 : CollatzResearch.WordTrace tailWord_1283376 prefixEnd_1283376 658988748444676019197867 := by
  unfold tailWord_1283376
  simp only [CollatzResearch.WordTrace]
  refine ⟨23404284099277705007922991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31205712132370273343897321 23404284099277705007922991)
  ·
    refine ⟨35106426148916557511884487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23404284099277705007922991 35106426148916557511884487)
    ·
      refine ⟨52659639223374836267826731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35106426148916557511884487 52659639223374836267826731)
      ·
        refine ⟨78989458835062254401740097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52659639223374836267826731 78989458835062254401740097)
        ·
          refine ⟨59242094126296690801305073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78989458835062254401740097 59242094126296690801305073)
          ·
            refine ⟨44431570594722518100978805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59242094126296690801305073 44431570594722518100978805)
            ·
              refine ⟨4165459743255236071966763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44431570594722518100978805 4165459743255236071966763)
              ·
                refine ⟨6248189614882854107950145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4165459743255236071966763 6248189614882854107950145)
                ·
                  refine ⟨4686142211162140580962609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6248189614882854107950145 4686142211162140580962609)
                  ·
                    refine ⟨3514606658371605435721957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4686142211162140580962609 3514606658371605435721957)
                    ·
                      refine ⟨658988748444676019197867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3514606658371605435721957 658988748444676019197867)
                      ·
                        rfl

theorem cell23_1283376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 4].length) (baseStart_1283376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1283376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1283376 prefixEnd_1283376 := by exact prefixLift 1283376
  have htrace : WordTrace (prefixWord ++ tailWord_1283376) baseStart_1283376 baseEnd_1283376 := by
    simpa [prefixWord, tailWord_1283376, baseEnd_1283376] using wordTrace_append hprefix tailTrace_1283376
  have hstable : (prefixWord ++ tailWord_1283376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283376).length < 2 ^ (prefixWord ++ tailWord_1283376).sum := by decide
  have hdescent : baseEnd_1283376 < baseStart_1283376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283386 : List Nat := [3, 1, 1, 1, 4, 1, 3, 2, 7]
def baseStart_1283386 : Nat := 118140960795 + 1283386 * 2 ^ 59
def prefixEnd_1283386 : Nat := 4983230072969 + 3 ^ 40 * 1283386 * 2
def baseEnd_1283386 : Nat := 73221542583468997785869

theorem tailTrace_1283386 : CollatzResearch.WordTrace tailWord_1283386 prefixEnd_1283386 73221542583468997785869 := by
  unfold tailWord_1283386
  simp only [CollatzResearch.WordTrace]
  refine ⟨11702233232129795430927503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31205955285679454482473341 11702233232129795430927503)
  ·
    refine ⟨17553349848194693146391255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11702233232129795430927503 17553349848194693146391255)
    ·
      refine ⟨26330024772292039719586883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17553349848194693146391255 26330024772292039719586883)
      ·
        refine ⟨39495037158438059579380325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26330024772292039719586883 39495037158438059579380325)
        ·
          refine ⟨7405319467207136171133811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39495037158438059579380325 7405319467207136171133811)
          ·
            refine ⟨11107979200810704256700717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7405319467207136171133811 11107979200810704256700717)
            ·
              refine ⟨4165492200304014096262769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11107979200810704256700717 4165492200304014096262769)
              ·
                refine ⟨3124119150228010572197077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4165492200304014096262769 3124119150228010572197077)
                ·
                  refine ⟨73221542583468997785869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3124119150228010572197077 73221542583468997785869)
                  ·
                    rfl

theorem cell23_1283386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 2, 7].length) (baseStart_1283386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1283386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1283386 prefixEnd_1283386 := by exact prefixLift 1283386
  have htrace : WordTrace (prefixWord ++ tailWord_1283386) baseStart_1283386 baseEnd_1283386 := by
    simpa [prefixWord, tailWord_1283386, baseEnd_1283386] using wordTrace_append hprefix tailTrace_1283386
  have hstable : (prefixWord ++ tailWord_1283386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283386).length < 2 ^ (prefixWord ++ tailWord_1283386).sum := by decide
  have hdescent : baseEnd_1283386 < baseStart_1283386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283413 : List Nat := [1, 3, 2, 2, 3, 1, 1, 2, 2, 3, 3]
def baseStart_1283413 : Nat := 118140960795 + 1283413 * 2 ^ 59
def prefixEnd_1283413 : Nat := 4983230072969 + 3 ^ 40 * 1283413 * 2
def baseEnd_1283413 : Nat := 659007747228892374435197

theorem tailTrace_1283413 : CollatzResearch.WordTrace tailWord_1283413 prefixEnd_1283413 659007747228892374435197 := by
  unfold tailWord_1283413
  simp only [CollatzResearch.WordTrace]
  refine ⟨46809917699421365334942893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31206611799614243556628595 46809917699421365334942893)
  ·
    refine ⟨17553719137283012000603585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46809917699421365334942893 17553719137283012000603585)
    ·
      refine ⟨13165289352962259000452689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17553719137283012000603585 13165289352962259000452689)
      ·
        refine ⟨9873967014721694250339517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13165289352962259000452689 9873967014721694250339517)
        ·
          refine ⟨3702737630520635343877319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9873967014721694250339517 3702737630520635343877319)
          ·
            refine ⟨5554106445780953015815979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3702737630520635343877319 5554106445780953015815979)
            ·
              refine ⟨8331159668671429523723969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5554106445780953015815979 8331159668671429523723969)
              ·
                refine ⟨6248369751503572142792977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8331159668671429523723969 6248369751503572142792977)
                ·
                  refine ⟨4686277313627679107094733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6248369751503572142792977 4686277313627679107094733)
                  ·
                    refine ⟨1757353992610379665160525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4686277313627679107094733 1757353992610379665160525)
                    ·
                      refine ⟨659007747228892374435197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1757353992610379665160525 659007747228892374435197)
                      ·
                        rfl

theorem cell23_1283413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 2, 2, 3, 3].length) (baseStart_1283413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1283413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1283413 prefixEnd_1283413 := by exact prefixLift 1283413
  have htrace : WordTrace (prefixWord ++ tailWord_1283413) baseStart_1283413 baseEnd_1283413 := by
    simpa [prefixWord, tailWord_1283413, baseEnd_1283413] using wordTrace_append hprefix tailTrace_1283413
  have hstable : (prefixWord ++ tailWord_1283413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283413).length < 2 ^ (prefixWord ++ tailWord_1283413).sum := by decide
  have hdescent : baseEnd_1283413 < baseStart_1283413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283416 : List Nat := [2, 1, 2, 2, 1, 1, 4, 1, 4, 5]
def baseStart_1283416 : Nat := 118140960795 + 1283416 * 2 ^ 59
def prefixEnd_1283416 : Nat := 4983230072969 + 3 ^ 40 * 1283416 * 2
def baseEnd_1283416 : Nat := 219669762556951954232561

theorem tailTrace_1283416 : CollatzResearch.WordTrace tailWord_1283416 prefixEnd_1283416 219669762556951954232561 := by
  unfold tailWord_1283416
  simp only [CollatzResearch.WordTrace]
  refine ⟨23405013559205248423651051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31206684745606997898201401 23405013559205248423651051)
  ·
    refine ⟨35107520338807872635476577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23405013559205248423651051 35107520338807872635476577)
    ·
      refine ⟨26330640254105904476607433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35107520338807872635476577 26330640254105904476607433)
      ·
        refine ⟨19747980190579428357455575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26330640254105904476607433 19747980190579428357455575)
        ·
          refine ⟨29621970285869142536183363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19747980190579428357455575 29621970285869142536183363)
          ·
            refine ⟨44432955428803713804275045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29621970285869142536183363 44432955428803713804275045)
            ·
              refine ⟨8331179142900696338301571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44432955428803713804275045 8331179142900696338301571)
              ·
                refine ⟨12496768714351044507452357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8331179142900696338301571 12496768714351044507452357)
                ·
                  refine ⟨2343144133940820845147317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12496768714351044507452357 2343144133940820845147317)
                  ·
                    refine ⟨219669762556951954232561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2343144133940820845147317 219669762556951954232561)
                    ·
                      rfl

theorem cell23_1283416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 4, 5].length) (baseStart_1283416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1283416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1283416 prefixEnd_1283416 := by exact prefixLift 1283416
  have htrace : WordTrace (prefixWord ++ tailWord_1283416) baseStart_1283416 baseEnd_1283416 := by
    simpa [prefixWord, tailWord_1283416, baseEnd_1283416] using wordTrace_append hprefix tailTrace_1283416
  have hstable : (prefixWord ++ tailWord_1283416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283416).length < 2 ^ (prefixWord ++ tailWord_1283416).sum := by decide
  have hdescent : baseEnd_1283416 < baseStart_1283416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283453 : List Nat := [1, 4, 1, 1, 2, 2, 2, 3, 2, 1, 4]
def baseStart_1283453 : Nat := 118140960795 + 1283453 * 2 ^ 59
def prefixEnd_1283453 : Nat := 4983230072969 + 3 ^ 40 * 1283453 * 2
def baseEnd_1283453 : Nat := 659028286455072217935013

theorem tailTrace_1283453 : CollatzResearch.WordTrace tailWord_1283453 prefixEnd_1283453 659028286455072217935013 := by
  unfold tailWord_1283453
  simp only [CollatzResearch.WordTrace]
  refine ⟨46811376619276452166399013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31207584412850968110932675 46811376619276452166399013)
  ·
    refine ⟨8777133116114334781199815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46811376619276452166399013 8777133116114334781199815)
    ·
      refine ⟨13165699674171502171799723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8777133116114334781199815 13165699674171502171799723)
      ·
        refine ⟨19748549511257253257699585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13165699674171502171799723 19748549511257253257699585)
        ·
          refine ⟨14811412133442939943274689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19748549511257253257699585 14811412133442939943274689)
          ·
            refine ⟨11108559100082204957456017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14811412133442939943274689 11108559100082204957456017)
            ·
              refine ⟨8331419325061653718092013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11108559100082204957456017 8331419325061653718092013)
              ·
                refine ⟨3124282246898120144284505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8331419325061653718092013 3124282246898120144284505)
                ·
                  refine ⟨2343211685173590108213379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3124282246898120144284505 2343211685173590108213379)
                  ·
                    refine ⟨3514817527760385162320069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2343211685173590108213379 3514817527760385162320069)
                    ·
                      refine ⟨659028286455072217935013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3514817527760385162320069 659028286455072217935013)
                      ·
                        rfl

theorem cell23_1283453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 3, 2, 1, 4].length) (baseStart_1283453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1283453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1283453 prefixEnd_1283453 := by exact prefixLift 1283453
  have htrace : WordTrace (prefixWord ++ tailWord_1283453) baseStart_1283453 baseEnd_1283453 := by
    simpa [prefixWord, tailWord_1283453, baseEnd_1283453] using wordTrace_append hprefix tailTrace_1283453
  have hstable : (prefixWord ++ tailWord_1283453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283453).length < 2 ^ (prefixWord ++ tailWord_1283453).sum := by decide
  have hdescent : baseEnd_1283453 < baseStart_1283453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283473 : List Nat := [1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 3]
def baseStart_1283473 : Nat := 118140960795 + 1283473 * 2 ^ 59
def prefixEnd_1283473 : Nat := 4983230072969 + 3 ^ 40 * 1283473 * 2
def baseEnd_1283473 : Nat := 659038556068162139684921

theorem tailTrace_1283473 : CollatzResearch.WordTrace tailWord_1283473 prefixEnd_1283473 659038556068162139684921 := by
  unfold tailWord_1283473
  simp only [CollatzResearch.WordTrace]
  refine ⟨46812106079203995582127073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31208070719469330388084715 46812106079203995582127073)
  ·
    refine ⟨35109079559402996686595305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46812106079203995582127073 35109079559402996686595305)
    ·
      refine ⟨26331809669552247514946479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35109079559402996686595305 26331809669552247514946479)
      ·
        refine ⟨39497714504328371272419719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26331809669552247514946479 39497714504328371272419719)
        ·
          refine ⟨59246571756492556908629579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39497714504328371272419719 59246571756492556908629579)
          ·
            refine ⟨88869857634738835362944369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59246571756492556908629579 88869857634738835362944369)
            ·
              refine ⟨66652393226054126522208277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88869857634738835362944369 66652393226054126522208277)
              ·
                refine ⟨3124330932471287180728513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 66652393226054126522208277 3124330932471287180728513)
                ·
                  refine ⟨2343248199353465385546385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3124330932471287180728513 2343248199353465385546385)
                  ·
                    refine ⟨1757436149515099039159789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2343248199353465385546385 1757436149515099039159789)
                    ·
                      refine ⟨659038556068162139684921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1757436149515099039159789 659038556068162139684921)
                      ·
                        rfl

theorem cell23_1283473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 3].length) (baseStart_1283473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1283473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1283473 prefixEnd_1283473 := by exact prefixLift 1283473
  have htrace : WordTrace (prefixWord ++ tailWord_1283473) baseStart_1283473 baseEnd_1283473 := by
    simpa [prefixWord, tailWord_1283473, baseEnd_1283473] using wordTrace_append hprefix tailTrace_1283473
  have hstable : (prefixWord ++ tailWord_1283473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283473).length < 2 ^ (prefixWord ++ tailWord_1283473).sum := by decide
  have hdescent : baseEnd_1283473 < baseStart_1283473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283523 : List Nat := [1, 1, 1, 3, 1, 1, 4, 5, 1, 5]
def baseStart_1283523 : Nat := 118140960795 + 1283523 * 2 ^ 59
def prefixEnd_1283523 : Nat := 4983230072969 + 3 ^ 40 * 1283523 * 2
def baseEnd_1283523 : Nat := 219688076700295648019897

theorem tailTrace_1283523 : CollatzResearch.WordTrace tailWord_1283523 prefixEnd_1283523 219688076700295648019897 := by
  unfold tailWord_1283523
  simp only [CollatzResearch.WordTrace]
  refine ⟨46813929729022854121447223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31209286486015236080964815 46813929729022854121447223)
  ·
    refine ⟨70220894593534281182170835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46813929729022854121447223 70220894593534281182170835)
    ·
      refine ⟨105331341890301421773256253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70220894593534281182170835 105331341890301421773256253)
      ·
        refine ⟨39499253208863033164971095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105331341890301421773256253 39499253208863033164971095)
        ·
          refine ⟨59248879813294549747456643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39499253208863033164971095 59248879813294549747456643)
          ·
            refine ⟨88873319719941824621184965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59248879813294549747456643 88873319719941824621184965)
            ·
              refine ⟨16663747447489092116472181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 88873319719941824621184965 16663747447489092116472181)
              ·
                refine ⟨1562226323202102385919267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16663747447489092116472181 1562226323202102385919267)
                ·
                  refine ⟨2343339484803153578878901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1562226323202102385919267 2343339484803153578878901)
                  ·
                    refine ⟨219688076700295648019897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2343339484803153578878901 219688076700295648019897)
                    ·
                      rfl

theorem cell23_1283523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 5, 1, 5].length) (baseStart_1283523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1283523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1283523 prefixEnd_1283523 := by exact prefixLift 1283523
  have htrace : WordTrace (prefixWord ++ tailWord_1283523) baseStart_1283523 baseEnd_1283523 := by
    simpa [prefixWord, tailWord_1283523, baseEnd_1283523] using wordTrace_append hprefix tailTrace_1283523
  have hstable : (prefixWord ++ tailWord_1283523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283523).length < 2 ^ (prefixWord ++ tailWord_1283523).sum := by decide
  have hdescent : baseEnd_1283523 < baseStart_1283523 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283553 : List Nat := [1, 2, 3, 1, 2, 3, 1, 3, 1, 6]
def baseStart_1283553 : Nat := 118140960795 + 1283553 * 2 ^ 59
def prefixEnd_1283553 : Nat := 4983230072969 + 3 ^ 40 * 1283553 * 2
def baseEnd_1283553 : Nat := 219693211506840608894851

theorem tailTrace_1283553 : CollatzResearch.WordTrace tailWord_1283553 prefixEnd_1283553 219693211506840608894851 := by
  unfold tailWord_1283553
  simp only [CollatzResearch.WordTrace]
  refine ⟨46815023918914169245039313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31210015945942779496692875 46815023918914169245039313)
  ·
    refine ⟨35111267939185626933779485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46815023918914169245039313 35111267939185626933779485)
    ·
      refine ⟨13166725477194610100167307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35111267939185626933779485 13166725477194610100167307)
      ·
        refine ⟨19750088215791915150250961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13166725477194610100167307 19750088215791915150250961)
        ·
          refine ⟨14812566161843936362688221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19750088215791915150250961 14812566161843936362688221)
          ·
            refine ⟨5554712310691476136008083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14812566161843936362688221 5554712310691476136008083)
            ·
              refine ⟨8332068466037214204012125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5554712310691476136008083 8332068466037214204012125)
              ·
                refine ⟨3124525674763955326504547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8332068466037214204012125 3124525674763955326504547)
                ·
                  refine ⟨4686788512145932989756821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3124525674763955326504547 4686788512145932989756821)
                  ·
                    refine ⟨219693211506840608894851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4686788512145932989756821 219693211506840608894851)
                    ·
                      rfl

theorem cell23_1283553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 3, 1, 6].length) (baseStart_1283553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1283553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1283553 prefixEnd_1283553 := by exact prefixLift 1283553
  have htrace : WordTrace (prefixWord ++ tailWord_1283553) baseStart_1283553 baseEnd_1283553 := by
    simpa [prefixWord, tailWord_1283553, baseEnd_1283553] using wordTrace_append hprefix tailTrace_1283553
  have hstable : (prefixWord ++ tailWord_1283553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283553).length < 2 ^ (prefixWord ++ tailWord_1283553).sum := by decide
  have hdescent : baseEnd_1283553 < baseStart_1283553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283560 : List Nat := [2, 1, 4, 1, 1, 2, 2, 4, 1, 1, 4]
def baseStart_1283560 : Nat := 118140960795 + 1283560 * 2 ^ 59
def prefixEnd_1283560 : Nat := 4983230072969 + 3 ^ 40 * 1283560 * 2
def baseEnd_1283560 : Nat := 659083228885103299297021

theorem tailTrace_1283560 : CollatzResearch.WordTrace tailWord_1283560 prefixEnd_1283560 659083228885103299297021 := by
  unfold tailWord_1283560
  simp only [CollatzResearch.WordTrace]
  refine ⟨23407639614944404720272067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31210186153259206293696089 23407639614944404720272067)
  ·
    refine ⟨35111459422416607080408101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23407639614944404720272067 35111459422416607080408101)
    ·
      refine ⟨6583398641703113827576519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35111459422416607080408101 6583398641703113827576519)
      ·
        refine ⟨9875097962554670741364779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6583398641703113827576519 9875097962554670741364779)
        ·
          refine ⟨14812646943832006112047169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9875097962554670741364779 14812646943832006112047169)
          ·
            refine ⟨11109485207874004584035377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14812646943832006112047169 11109485207874004584035377)
            ·
              refine ⟨8332113905905503438026533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11109485207874004584035377 8332113905905503438026533)
              ·
                refine ⟨1562271357357281894629975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8332113905905503438026533 1562271357357281894629975)
                ·
                  refine ⟨2343407036035922841944963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1562271357357281894629975 2343407036035922841944963)
                  ·
                    refine ⟨3515110554053884262917445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2343407036035922841944963 3515110554053884262917445)
                    ·
                      refine ⟨659083228885103299297021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3515110554053884262917445 659083228885103299297021)
                      ·
                        rfl

theorem cell23_1283560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 4, 1, 1, 4].length) (baseStart_1283560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1283560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1283560 prefixEnd_1283560 := by exact prefixLift 1283560
  have htrace : WordTrace (prefixWord ++ tailWord_1283560) baseStart_1283560 baseEnd_1283560 := by
    simpa [prefixWord, tailWord_1283560, baseEnd_1283560] using wordTrace_append hprefix tailTrace_1283560
  have hstable : (prefixWord ++ tailWord_1283560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283560).length < 2 ^ (prefixWord ++ tailWord_1283560).sum := by decide
  have hdescent : baseEnd_1283560 < baseStart_1283560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283570 : List Nat := [3, 2, 1, 4, 1, 1, 2, 2, 1, 6]
def baseStart_1283570 : Nat := 118140960795 + 1283570 * 2 ^ 59
def prefixEnd_1283570 : Nat := 4983230072969 + 3 ^ 40 * 1283570 * 2
def baseEnd_1283570 : Nat := 219696121230549420057325

theorem tailTrace_1283570 : CollatzResearch.WordTrace tailWord_1283570 prefixEnd_1283570 219696121230549420057325 := by
  unfold tailWord_1283570
  simp only [CollatzResearch.WordTrace]
  refine ⟨11703910989963145287102041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31210429306568387432272109 11703910989963145287102041)
  ·
    refine ⟨8777933242472358965326531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11703910989963145287102041 8777933242472358965326531)
    ·
      refine ⟨13166899863708538447989797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8777933242472358965326531 13166899863708538447989797)
      ·
        refine ⟨2468793724445350958998087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13166899863708538447989797 2468793724445350958998087)
        ·
          refine ⟨3703190586668026438497131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2468793724445350958998087 3703190586668026438497131)
          ·
            refine ⟨5554785880002039657745697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3703190586668026438497131 5554785880002039657745697)
            ·
              refine ⟨4166089410001529743309273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5554785880002039657745697 4166089410001529743309273)
              ·
                refine ⟨3124567057501147307481955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4166089410001529743309273 3124567057501147307481955)
                ·
                  refine ⟨4686850586251720961222933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3124567057501147307481955 4686850586251720961222933)
                  ·
                    refine ⟨219696121230549420057325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4686850586251720961222933 219696121230549420057325)
                    ·
                      rfl

theorem cell23_1283570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 2, 1, 6].length) (baseStart_1283570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1283570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1283570 prefixEnd_1283570 := by exact prefixLift 1283570
  have htrace : WordTrace (prefixWord ++ tailWord_1283570) baseStart_1283570 baseEnd_1283570 := by
    simpa [prefixWord, tailWord_1283570, baseEnd_1283570] using wordTrace_append hprefix tailTrace_1283570
  have hstable : (prefixWord ++ tailWord_1283570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283570).length < 2 ^ (prefixWord ++ tailWord_1283570).sum := by decide
  have hdescent : baseEnd_1283570 < baseStart_1283570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283574 : List Nat := [5, 1, 1, 1, 2, 4, 2, 1, 1, 5]
def baseStart_1283574 : Nat := 118140960795 + 1283574 * 2 ^ 59
def prefixEnd_1283574 : Nat := 4983230072969 + 3 ^ 40 * 1283574 * 2
def baseEnd_1283574 : Nat := 219696805871422081507319

theorem tailTrace_1283574 : CollatzResearch.WordTrace tailWord_1283574 prefixEnd_1283574 219696805871422081507319 := by
  unfold tailWord_1283574
  simp only [CollatzResearch.WordTrace]
  refine ⟨2925986865739880614472111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31210526567892059887702517 2925986865739880614472111)
  ·
    refine ⟨4388980298609820921708167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2925986865739880614472111 4388980298609820921708167)
    ·
      refine ⟨6583470447914731382562251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4388980298609820921708167 6583470447914731382562251)
      ·
        refine ⟨9875205671872097073843377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6583470447914731382562251 9875205671872097073843377)
        ·
          refine ⟨7406404253904072805382533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9875205671872097073843377 7406404253904072805382533)
          ·
            refine ⟨1388700797607013651009225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7406404253904072805382533 1388700797607013651009225)
            ·
              refine ⟨1041525598205260238256919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1388700797607013651009225 1041525598205260238256919)
              ·
                refine ⟨1562288397307890357385379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1041525598205260238256919 1562288397307890357385379)
                ·
                  refine ⟨2343432595961835536078069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1562288397307890357385379 2343432595961835536078069)
                  ·
                    refine ⟨219696805871422081507319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2343432595961835536078069 219696805871422081507319)
                    ·
                      rfl

theorem cell23_1283574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 2, 1, 1, 5].length) (baseStart_1283574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1283574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1283574 prefixEnd_1283574 := by exact prefixLift 1283574
  have htrace : WordTrace (prefixWord ++ tailWord_1283574) baseStart_1283574 baseEnd_1283574 := by
    simpa [prefixWord, tailWord_1283574, baseEnd_1283574] using wordTrace_append hprefix tailTrace_1283574
  have hstable : (prefixWord ++ tailWord_1283574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283574).length < 2 ^ (prefixWord ++ tailWord_1283574).sum := by decide
  have hdescent : baseEnd_1283574 < baseStart_1283574 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
