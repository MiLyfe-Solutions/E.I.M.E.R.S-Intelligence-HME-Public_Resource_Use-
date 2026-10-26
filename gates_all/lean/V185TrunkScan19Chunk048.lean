import V185TrunkScan19Chunk047

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental

namespace V185TrunkScan19Incremental

def tailWord_481337 : List Nat := [1, 2, 1, 5, 3, 2, 1, 4]
def baseStart_481337 : Nat := 118140960795 + 481337 * 2 ^ 59
def prefixEnd_481337 : Nat := 4983230072969 + 3 ^ 40 * 481337 * 2
def baseEnd_481337 : Nat := 146463548321948741021557

theorem tailTrace_481337 : CollatzResearch.WordTrace tailWord_481337 prefixEnd_481337 146463548321948741021557 := by
  unfold tailWord_481337
  simp only [CollatzResearch.WordTrace]
  refine ⟨17555802657205729659970265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11703868438137153106646843 17555802657205729659970265)
  ·
    refine ⟨13166851992904297244977699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17555802657205729659970265 13166851992904297244977699)
    ·
      refine ⟨19750277989356445867466549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13166851992904297244977699 19750277989356445867466549)
      ·
        refine ⟨1851588561502166800074989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19750277989356445867466549 1851588561502166800074989)
        ·
          refine ⟨694345710563312550028121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1851588561502166800074989 694345710563312550028121)
          ·
            refine ⟨520759282922484412521091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 694345710563312550028121 520759282922484412521091)
            ·
              refine ⟨781138924383726618781637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 520759282922484412521091 781138924383726618781637)
              ·
                refine ⟨146463548321948741021557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 781138924383726618781637 146463548321948741021557)
                ·
                  rfl

theorem cell19_481337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 4].length) (baseStart_481337 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_481337 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_481337 prefixEnd_481337 := by exact prefixLift 481337
  have htrace : WordTrace (prefixWord ++ tailWord_481337) baseStart_481337 baseEnd_481337 := by
    simpa [prefixWord, tailWord_481337, baseEnd_481337] using wordTrace_append hprefix tailTrace_481337
  have hstable : (prefixWord ++ tailWord_481337).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481337).length < 2 ^ (prefixWord ++ tailWord_481337).sum := by decide
  have hdescent : baseEnd_481337 < baseStart_481337 := by decide
  rcases family_descends (prefixWord ++ tailWord_481337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481413 : List Nat := [1, 3, 1, 1, 5, 3, 2, 3]
def baseStart_481413 : Nat := 118140960795 + 481413 * 2 ^ 59
def prefixEnd_481413 : Nat := 4983230072969 + 3 ^ 40 * 481413 * 2
def baseEnd_481413 : Nat := 146486673969203083332461

theorem tailTrace_481413 : CollatzResearch.WordTrace tailWord_481413 prefixEnd_481413 146486673969203083332461 := by
  unfold tailWord_481413
  simp only [CollatzResearch.WordTrace]
  refine ⟨17558574604930394639736893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11705716403286929759824595 17558574604930394639736893)
  ·
    refine ⟨6584465476848897989901335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17558574604930394639736893 6584465476848897989901335)
    ·
      refine ⟨9876698215273346984852003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6584465476848897989901335 9876698215273346984852003)
      ·
        refine ⟨14815047322910020477278005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9876698215273346984852003 14815047322910020477278005)
        ·
          refine ⟨1388910686522814419744813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14815047322910020477278005 1388910686522814419744813)
          ·
            refine ⟨520841507446055407404305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1388910686522814419744813 520841507446055407404305)
            ·
              refine ⟨390631130584541555553229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 520841507446055407404305 390631130584541555553229)
              ·
                refine ⟨146486673969203083332461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 390631130584541555553229 146486673969203083332461)
                ·
                  rfl

theorem cell19_481413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 2, 3].length) (baseStart_481413 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_481413 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_481413 prefixEnd_481413 := by exact prefixLift 481413
  have htrace : WordTrace (prefixWord ++ tailWord_481413) baseStart_481413 baseEnd_481413 := by
    simpa [prefixWord, tailWord_481413, baseEnd_481413] using wordTrace_append hprefix tailTrace_481413
  have hstable : (prefixWord ++ tailWord_481413).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481413).length < 2 ^ (prefixWord ++ tailWord_481413).sum := by decide
  have hdescent : baseEnd_481413 < baseStart_481413 := by decide
  rcases family_descends (prefixWord ++ tailWord_481413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481415 : List Nat := [1, 1, 4, 2, 1, 1, 6, 3]
def baseStart_481415 : Nat := 118140960795 + 481415 * 2 ^ 59
def prefixEnd_481415 : Nat := 4983230072969 + 3 ^ 40 * 481415 * 2
def baseEnd_481415 : Nat := 146487282538867671288011

theorem tailTrace_481415 : CollatzResearch.WordTrace tailWord_481415 prefixEnd_481415 146487282538867671288011 := by
  unfold tailWord_481415
  simp only [CollatzResearch.WordTrace]
  refine ⟨17558647550923148981309699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11705765033948765987539799 17558647550923148981309699)
  ·
    refine ⟨26337971326384723471964549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17558647550923148981309699 26337971326384723471964549)
    ·
      refine ⟨4938369623697135650993353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26337971326384723471964549 4938369623697135650993353)
      ·
        refine ⟨3703777217772851738245015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4938369623697135650993353 3703777217772851738245015)
        ·
          refine ⟨5555665826659277607367523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3703777217772851738245015 5555665826659277607367523)
          ·
            refine ⟨8333498739988916411051285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5555665826659277607367523 8333498739988916411051285)
            ·
              refine ⟨390632753436980456768029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8333498739988916411051285 390632753436980456768029)
              ·
                refine ⟨146487282538867671288011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 390632753436980456768029 146487282538867671288011)
                ·
                  rfl

theorem cell19_481415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 6, 3].length) (baseStart_481415 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_481415 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_481415 prefixEnd_481415 := by exact prefixLift 481415
  have htrace : WordTrace (prefixWord ++ tailWord_481415) baseStart_481415 baseEnd_481415 := by
    simpa [prefixWord, tailWord_481415, baseEnd_481415] using wordTrace_append hprefix tailTrace_481415
  have hstable : (prefixWord ++ tailWord_481415).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481415).length < 2 ^ (prefixWord ++ tailWord_481415).sum := by decide
  have hdescent : baseEnd_481415 < baseStart_481415 := by decide
  rcases family_descends (prefixWord ++ tailWord_481415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481417 : List Nat := [1, 2, 1, 1, 4, 2, 3, 5]
def baseStart_481417 : Nat := 118140960795 + 481417 * 2 ^ 59
def prefixEnd_481417 : Nat := 4983230072969 + 3 ^ 40 * 481417 * 2
def baseEnd_481417 : Nat := 146487891108532259243561

theorem tailTrace_481417 : CollatzResearch.WordTrace tailWord_481417 prefixEnd_481417 146487891108532259243561 := by
  unfold tailWord_481417
  simp only [CollatzResearch.WordTrace]
  refine ⟨17558720496915903322882505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11705813664610602215255003 17558720496915903322882505)
  ·
    refine ⟨13169040372686927492161879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17558720496915903322882505 13169040372686927492161879)
    ·
      refine ⟨19753560559030391238242819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13169040372686927492161879 19753560559030391238242819)
      ·
        refine ⟨29630340838545586857364229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19753560559030391238242819 29630340838545586857364229)
        ·
          refine ⟨5555688907227297535755793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29630340838545586857364229 5555688907227297535755793)
          ·
            refine ⟨4166766680420473151816845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5555688907227297535755793 4166766680420473151816845)
            ·
              refine ⟨1562537505157677431931317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4166766680420473151816845 1562537505157677431931317)
              ·
                refine ⟨146487891108532259243561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1562537505157677431931317 146487891108532259243561)
                ·
                  rfl

theorem cell19_481417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 5].length) (baseStart_481417 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_481417 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_481417 prefixEnd_481417 := by exact prefixLift 481417
  have htrace : WordTrace (prefixWord ++ tailWord_481417) baseStart_481417 baseEnd_481417 := by
    simpa [prefixWord, tailWord_481417, baseEnd_481417] using wordTrace_append hprefix tailTrace_481417
  have hstable : (prefixWord ++ tailWord_481417).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481417).length < 2 ^ (prefixWord ++ tailWord_481417).sum := by decide
  have hdescent : baseEnd_481417 < baseStart_481417 := by decide
  rcases family_descends (prefixWord ++ tailWord_481417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481432 : List Nat := [2, 1, 2, 4, 4, 1, 5]
def baseStart_481432 : Nat := 118140960795 + 481432 * 2 ^ 59
def prefixEnd_481432 : Nat := 4983230072969 + 3 ^ 40 * 481432 * 2
def baseEnd_481432 : Nat := 48830818460338889636729

theorem tailTrace_481432 : CollatzResearch.WordTrace tailWord_481432 prefixEnd_481432 48830818460338889636729 := by
  unfold tailWord_481432
  simp only [CollatzResearch.WordTrace]
  refine ⟨8779633795930780442339275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11706178394574373923119033 8779633795930780442339275)
  ·
    refine ⟨13169450693896170663508913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8779633795930780442339275 13169450693896170663508913)
    ·
      refine ⟨9877088020422127997631685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13169450693896170663508913 9877088020422127997631685)
      ·
        refine ⟨1851954003829148999555941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9877088020422127997631685 1851954003829148999555941)
        ·
          refine ⟨347241375717965437416739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1851954003829148999555941 347241375717965437416739)
          ·
            refine ⟨520862063576948156125109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 347241375717965437416739 520862063576948156125109)
            ·
              refine ⟨48830818460338889636729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 520862063576948156125109 48830818460338889636729)
              ·
                rfl

theorem cell19_481432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 5].length) (baseStart_481432 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_481432 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_481432 prefixEnd_481432 := by exact prefixLift 481432
  have htrace : WordTrace (prefixWord ++ tailWord_481432) baseStart_481432 baseEnd_481432 := by
    simpa [prefixWord, tailWord_481432, baseEnd_481432] using wordTrace_append hprefix tailTrace_481432
  have hstable : (prefixWord ++ tailWord_481432).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481432).length < 2 ^ (prefixWord ++ tailWord_481432).sum := by decide
  have hdescent : baseEnd_481432 < baseStart_481432 := by decide
  rcases family_descends (prefixWord ++ tailWord_481432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481453 : List Nat := [1, 5, 2, 1, 2, 1, 1, 6]
def baseStart_481453 : Nat := 118140960795 + 481453 * 2 ^ 59
def prefixEnd_481453 : Nat := 4983230072969 + 3 ^ 40 * 481453 * 2
def baseEnd_481453 : Nat := 146498845362494842443463

theorem tailTrace_481453 : CollatzResearch.WordTrace tailWord_481453 prefixEnd_481453 146498845362494842443463 := by
  unfold tailWord_481453
  simp only [CollatzResearch.WordTrace]
  refine ⟨17560033524785481471193013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11706689016523654314128675 17560033524785481471193013)
  ·
    refine ⟨1646253142948638887924345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17560033524785481471193013 1646253142948638887924345)
    ·
      refine ⟨1234689857211479165943259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1646253142948638887924345 1234689857211479165943259)
      ·
        refine ⟨1852034785817218748914889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1234689857211479165943259 1852034785817218748914889)
        ·
          refine ⟨1389026089362914061686167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1852034785817218748914889 1389026089362914061686167)
          ·
            refine ⟨2083539134044371092529251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1389026089362914061686167 2083539134044371092529251)
            ·
              refine ⟨3125308701066556638793877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2083539134044371092529251 3125308701066556638793877)
              ·
                refine ⟨146498845362494842443463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3125308701066556638793877 146498845362494842443463)
                ·
                  rfl

theorem cell19_481453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 6].length) (baseStart_481453 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_481453 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_481453 prefixEnd_481453 := by exact prefixLift 481453
  have htrace : WordTrace (prefixWord ++ tailWord_481453) baseStart_481453 baseEnd_481453 := by
    simpa [prefixWord, tailWord_481453, baseEnd_481453] using wordTrace_append hprefix tailTrace_481453
  have hstable : (prefixWord ++ tailWord_481453).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481453).length < 2 ^ (prefixWord ++ tailWord_481453).sum := by decide
  have hdescent : baseEnd_481453 < baseStart_481453 := by decide
  rcases family_descends (prefixWord ++ tailWord_481453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481493 : List Nat := [1, 3, 2, 4, 9]
def baseStart_481493 : Nat := 118140960795 + 481493 * 2 ^ 59
def prefixEnd_481493 : Nat := 4983230072969 + 3 ^ 40 * 481493 * 2
def baseEnd_481493 : Nat := 5426333953918022279795

theorem tailTrace_481493 : CollatzResearch.WordTrace tailWord_481493 prefixEnd_481493 5426333953918022279795 := by
  unfold tailWord_481493
  simp only [CollatzResearch.WordTrace]
  refine ⟨17561492444640568302649133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11707661629760378868432755 17561492444640568302649133)
  ·
    refine ⟨6585559666740213113493425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17561492444640568302649133 6585559666740213113493425)
    ·
      refine ⟨4939169750055159835120069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6585559666740213113493425 4939169750055159835120069)
      ·
        refine ⟨926094328135342469085013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4939169750055159835120069 926094328135342469085013)
        ·
          refine ⟨5426333953918022279795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 926094328135342469085013 5426333953918022279795)
          ·
            rfl

theorem cell19_481493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 9].length) (baseStart_481493 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_481493 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_481493 prefixEnd_481493 := by exact prefixLift 481493
  have htrace : WordTrace (prefixWord ++ tailWord_481493) baseStart_481493 baseEnd_481493 := by
    simpa [prefixWord, tailWord_481493, baseEnd_481493] using wordTrace_append hprefix tailTrace_481493
  have hstable : (prefixWord ++ tailWord_481493).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481493).length < 2 ^ (prefixWord ++ tailWord_481493).sum := by decide
  have hdescent : baseEnd_481493 < baseStart_481493 := by decide
  rcases family_descends (prefixWord ++ tailWord_481493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481550 : List Nat := [4, 1, 1, 2, 1, 2, 8]
def baseStart_481550 : Nat := 118140960795 + 481550 * 2 ^ 59
def prefixEnd_481550 : Nat := 4983230072969 + 3 ^ 40 * 481550 * 2
def baseEnd_481550 : Nat := 48842786997075786095881

theorem tailTrace_481550 : CollatzResearch.WordTrace tailWord_481550 prefixEnd_481550 48842786997075786095881 := by
  unfold tailWord_481550
  simp only [CollatzResearch.WordTrace]
  refine ⟨2195446425679258379684263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11709047603622711358316069 2195446425679258379684263)
  ·
    refine ⟨3293169638518887569526395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2195446425679258379684263 3293169638518887569526395)
    ·
      refine ⟨4939754457778331354289593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3293169638518887569526395 4939754457778331354289593)
      ·
        refine ⟨3704815843333748515717195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4939754457778331354289593 3704815843333748515717195)
        ·
          refine ⟨5557223765000622773575793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3704815843333748515717195 5557223765000622773575793)
          ·
            refine ⟨4167917823750467080181845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5557223765000622773575793 4167917823750467080181845)
            ·
              refine ⟨48842786997075786095881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4167917823750467080181845 48842786997075786095881)
              ·
                rfl

theorem cell19_481550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 8].length) (baseStart_481550 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_481550 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_481550 prefixEnd_481550 := by exact prefixLift 481550
  have htrace : WordTrace (prefixWord ++ tailWord_481550) baseStart_481550 baseEnd_481550 := by
    simpa [prefixWord, tailWord_481550, baseEnd_481550] using wordTrace_append hprefix tailTrace_481550
  have hstable : (prefixWord ++ tailWord_481550).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481550).length < 2 ^ (prefixWord ++ tailWord_481550).sum := by decide
  have hdescent : baseEnd_481550 < baseStart_481550 := by decide
  rcases family_descends (prefixWord ++ tailWord_481550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481586 : List Nat := [3, 2, 1, 1, 5, 1, 1, 5]
def baseStart_481586 : Nat := 118140960795 + 481586 * 2 ^ 59
def prefixEnd_481586 : Nat := 4983230072969 + 3 ^ 40 * 481586 * 2
def baseEnd_481586 : Nat := 146539315245189941487545

theorem tailTrace_481586 : CollatzResearch.WordTrace tailWord_481586 prefixEnd_481586 146539315245189941487545 := by
  unfold tailWord_481586
  simp only [CollatzResearch.WordTrace]
  refine ⟨4391221108325911296446153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11709922955535763457189741 4391221108325911296446153)
  ·
    refine ⟨3293415831244433472334615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4391221108325911296446153 3293415831244433472334615)
    ·
      refine ⟨4940123746866650208501923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3293415831244433472334615 4940123746866650208501923)
      ·
        refine ⟨7410185620299975312752885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4940123746866650208501923 7410185620299975312752885)
        ·
          refine ⟨694704901903122685570583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7410185620299975312752885 694704901903122685570583)
          ·
            refine ⟨1042057352854684028355875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 694704901903122685570583 1042057352854684028355875)
            ·
              refine ⟨1563086029282026042533813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1042057352854684028355875 1563086029282026042533813)
              ·
                refine ⟨146539315245189941487545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1563086029282026042533813 146539315245189941487545)
                ·
                  rfl

theorem cell19_481586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 5].length) (baseStart_481586 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_481586 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_481586 prefixEnd_481586 := by exact prefixLift 481586
  have htrace : WordTrace (prefixWord ++ tailWord_481586) baseStart_481586 baseEnd_481586 := by
    simpa [prefixWord, tailWord_481586, baseEnd_481586] using wordTrace_append hprefix tailTrace_481586
  have hstable : (prefixWord ++ tailWord_481586).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481586).length < 2 ^ (prefixWord ++ tailWord_481586).sum := by decide
  have hdescent : baseEnd_481586 < baseStart_481586 := by decide
  rcases family_descends (prefixWord ++ tailWord_481586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481645 : List Nat := [1, 5, 1, 1, 1, 2, 1, 7]
def baseStart_481645 : Nat := 118140960795 + 481645 * 2 ^ 59
def prefixEnd_481645 : Nat := 4983230072969 + 3 ^ 40 * 481645 * 2
def baseEnd_481645 : Nat := 146557268050295286176273

theorem tailTrace_481645 : CollatzResearch.WordTrace tailWord_481645 prefixEnd_481645 146557268050295286176273 := by
  unfold tailWord_481645
  simp only [CollatzResearch.WordTrace]
  refine ⟨17567036340089898262182389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11711357560059932174788259 17567036340089898262182389)
  ·
    refine ⟨1646909656883427962079599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17567036340089898262182389 1646909656883427962079599)
    ·
      refine ⟨2470364485325141943119399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1646909656883427962079599 2470364485325141943119399)
      ·
        refine ⟨3705546727987712914679099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2470364485325141943119399 3705546727987712914679099)
        ·
          refine ⟨5558320091981569372018649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3705546727987712914679099 5558320091981569372018649)
          ·
            refine ⟨4168740068986177029013987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5558320091981569372018649 4168740068986177029013987)
            ·
              refine ⟨6253110103479265543520981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4168740068986177029013987 6253110103479265543520981)
              ·
                refine ⟨146557268050295286176273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6253110103479265543520981 146557268050295286176273)
                ·
                  rfl

theorem cell19_481645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 7].length) (baseStart_481645 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_481645 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_481645 prefixEnd_481645 := by exact prefixLift 481645
  have htrace : WordTrace (prefixWord ++ tailWord_481645) baseStart_481645 baseEnd_481645 := by
    simpa [prefixWord, tailWord_481645, baseEnd_481645] using wordTrace_append hprefix tailTrace_481645
  have hstable : (prefixWord ++ tailWord_481645).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481645).length < 2 ^ (prefixWord ++ tailWord_481645).sum := by decide
  have hdescent : baseEnd_481645 < baseStart_481645 := by decide
  rcases family_descends (prefixWord ++ tailWord_481645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481721 : List Nat := [1, 2, 1, 4, 3, 2, 6]
def baseStart_481721 : Nat := 118140960795 + 481721 * 2 ^ 59
def prefixEnd_481721 : Nat := 4983230072969 + 3 ^ 40 * 481721 * 2
def baseEnd_481721 : Nat := 48860131232516542829059

theorem tailTrace_481721 : CollatzResearch.WordTrace tailWord_481721 prefixEnd_481721 48860131232516542829059 := by
  unfold tailWord_481721
  simp only [CollatzResearch.WordTrace]
  refine ⟨17569808287814563241949017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11713205525209708827966011 17569808287814563241949017)
  ·
    refine ⟨13177356215860922431461763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17569808287814563241949017 13177356215860922431461763)
    ·
      refine ⟨19766034323791383647192645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13177356215860922431461763 19766034323791383647192645)
      ·
        refine ⟨3706131435710884433848621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19766034323791383647192645 3706131435710884433848621)
        ·
          refine ⟨1389799288391581662693233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3706131435710884433848621 1389799288391581662693233)
          ·
            refine ⟨1042349466293686247019925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1389799288391581662693233 1042349466293686247019925)
            ·
              refine ⟨48860131232516542829059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1042349466293686247019925 48860131232516542829059)
              ·
                rfl

theorem cell19_481721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 6].length) (baseStart_481721 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_481721 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_481721 prefixEnd_481721 := by exact prefixLift 481721
  have htrace : WordTrace (prefixWord ++ tailWord_481721) baseStart_481721 baseEnd_481721 := by
    simpa [prefixWord, tailWord_481721, baseEnd_481721] using wordTrace_append hprefix tailTrace_481721
  have hstable : (prefixWord ++ tailWord_481721).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481721).length < 2 ^ (prefixWord ++ tailWord_481721).sum := by decide
  have hdescent : baseEnd_481721 < baseStart_481721 := by decide
  rcases family_descends (prefixWord ++ tailWord_481721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481759 : List Nat := [1, 1, 2, 3, 3, 3, 1, 5]
def baseStart_481759 : Nat := 118140960795 + 481759 * 2 ^ 59
def prefixEnd_481759 : Nat := 4983230072969 + 3 ^ 40 * 481759 * 2
def baseEnd_481759 : Nat := 146591956521176799642629

theorem tailTrace_481759 : CollatzResearch.WordTrace tailWord_481759 prefixEnd_481759 146591956521176799642629 := by
  unfold tailWord_481759
  simp only [CollatzResearch.WordTrace]
  refine ⟨17571194261676895731832331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11714129507784597154554887 17571194261676895731832331)
  ·
    refine ⟨26356791392515343597748497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17571194261676895731832331 26356791392515343597748497)
    ·
      refine ⟨19767593544386507698311373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26356791392515343597748497 19767593544386507698311373)
      ·
        refine ⟨7412847579144940386866765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19767593544386507698311373 7412847579144940386866765)
        ·
          refine ⟨2779817842179352645075037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7412847579144940386866765 2779817842179352645075037)
          ·
            refine ⟨1042431690817257241903139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2779817842179352645075037 1042431690817257241903139)
            ·
              refine ⟨1563647536225885862854709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1042431690817257241903139 1563647536225885862854709)
              ·
                refine ⟨146591956521176799642629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1563647536225885862854709 146591956521176799642629)
                ·
                  rfl

theorem cell19_481759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 5].length) (baseStart_481759 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_481759 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_481759 prefixEnd_481759 := by exact prefixLift 481759
  have htrace : WordTrace (prefixWord ++ tailWord_481759) baseStart_481759 baseEnd_481759 := by
    simpa [prefixWord, tailWord_481759, baseEnd_481759] using wordTrace_append hprefix tailTrace_481759
  have hstable : (prefixWord ++ tailWord_481759).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481759).length < 2 ^ (prefixWord ++ tailWord_481759).sum := by decide
  have hdescent : baseEnd_481759 < baseStart_481759 := by decide
  rcases family_descends (prefixWord ++ tailWord_481759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481816 : List Nat := [2, 1, 2, 3, 3, 1, 2, 5]
def baseStart_481816 : Nat := 118140960795 + 481816 * 2 ^ 59
def prefixEnd_481816 : Nat := 4983230072969 + 3 ^ 40 * 481816 * 2
def baseEnd_481816 : Nat := 146609300756617556375807

theorem tailTrace_481816 : CollatzResearch.WordTrace tailWord_481816 prefixEnd_481816 146609300756617556375807 := by
  unfold tailWord_481816
  simp only [CollatzResearch.WordTrace]
  refine ⟨8786636611235197233328651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11715515481646929644438201 8786636611235197233328651)
  ·
    refine ⟨13179954916852795849992977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8786636611235197233328651 13179954916852795849992977)
    ·
      refine ⟨9884966187639596887494733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13179954916852795849992977 9884966187639596887494733)
      ·
        refine ⟨3706862320364848832810525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9884966187639596887494733 3706862320364848832810525)
        ·
          refine ⟨1390073370136818312303947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3706862320364848832810525 1390073370136818312303947)
          ·
            refine ⟨2085110055205227468455921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1390073370136818312303947 2085110055205227468455921)
            ·
              refine ⟨1563832541403920601341941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2085110055205227468455921 1563832541403920601341941)
              ·
                refine ⟨146609300756617556375807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1563832541403920601341941 146609300756617556375807)
                ·
                  rfl

theorem cell19_481816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 5].length) (baseStart_481816 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_481816 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_481816 prefixEnd_481816 := by exact prefixLift 481816
  have htrace : WordTrace (prefixWord ++ tailWord_481816) baseStart_481816 baseEnd_481816 := by
    simpa [prefixWord, tailWord_481816, baseEnd_481816] using wordTrace_append hprefix tailTrace_481816
  have hstable : (prefixWord ++ tailWord_481816).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481816).length < 2 ^ (prefixWord ++ tailWord_481816).sum := by decide
  have hdescent : baseEnd_481816 < baseStart_481816 := by decide
  rcases family_descends (prefixWord ++ tailWord_481816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481831 : List Nat := [1, 1, 7, 2, 2, 6]
def baseStart_481831 : Nat := 118140960795 + 481831 * 2 ^ 59
def prefixEnd_481831 : Nat := 4983230072969 + 3 ^ 40 * 481831 * 2
def baseEnd_481831 : Nat := 16290429447677996226937

theorem tailTrace_481831 : CollatzResearch.WordTrace tailWord_481831 prefixEnd_481831 16290429447677996226937 := by
  unfold tailWord_481831
  simp only [CollatzResearch.WordTrace]
  refine ⟨17573820317416052028453347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11715880211610701352302231 17573820317416052028453347)
  ·
    refine ⟨26360730476124078042680021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17573820317416052028453347 26360730476124078042680021)
    ·
      refine ⟨617829620534158079125313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 26360730476124078042680021 617829620534158079125313)
      ·
        refine ⟨463372215400618559343985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 617829620534158079125313 463372215400618559343985)
        ·
          refine ⟨347529161550463919507989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 463372215400618559343985 347529161550463919507989)
          ·
            refine ⟨16290429447677996226937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 347529161550463919507989 16290429447677996226937)
            ·
              rfl

theorem cell19_481831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 6].length) (baseStart_481831 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_481831 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_481831 prefixEnd_481831 := by exact prefixLift 481831
  have htrace : WordTrace (prefixWord ++ tailWord_481831) baseStart_481831 baseEnd_481831 := by
    simpa [prefixWord, tailWord_481831, baseEnd_481831] using wordTrace_append hprefix tailTrace_481831
  have hstable : (prefixWord ++ tailWord_481831).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481831).length < 2 ^ (prefixWord ++ tailWord_481831).sum := by decide
  have hdescent : baseEnd_481831 < baseStart_481831 := by decide
  rcases family_descends (prefixWord ++ tailWord_481831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481852 : List Nat := [2, 2, 2, 2, 3, 3, 1, 4]
def baseStart_481852 : Nat := 118140960795 + 481852 * 2 ^ 59
def prefixEnd_481852 : Nat := 4983230072969 + 3 ^ 40 * 481852 * 2
def baseEnd_481852 : Nat := 146620255010580139575709

theorem tailTrace_481852 : CollatzResearch.WordTrace tailWord_481852 prefixEnd_481852 146620255010580139575709 := by
  unfold tailWord_481852
  simp only [CollatzResearch.WordTrace]
  refine ⟨8787293125169986307483905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11716390833559981743311873 8787293125169986307483905)
  ·
    refine ⟨6590469843877489730612929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8787293125169986307483905 6590469843877489730612929)
    ·
      refine ⟨4942852382908117297959697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6590469843877489730612929 4942852382908117297959697)
      ·
        refine ⟨3707139287181087973469773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4942852382908117297959697 3707139287181087973469773)
        ·
          refine ⟨1390177232692907990051165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3707139287181087973469773 1390177232692907990051165)
          ·
            refine ⟨521316462259840496269187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1390177232692907990051165 521316462259840496269187)
            ·
              refine ⟨781974693389760744403781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 521316462259840496269187 781974693389760744403781)
              ·
                refine ⟨146620255010580139575709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 781974693389760744403781 146620255010580139575709)
                ·
                  rfl

theorem cell19_481852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 4].length) (baseStart_481852 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_481852 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_481852 prefixEnd_481852 := by exact prefixLift 481852
  have htrace : WordTrace (prefixWord ++ tailWord_481852) baseStart_481852 baseEnd_481852 := by
    simpa [prefixWord, tailWord_481852, baseEnd_481852] using wordTrace_append hprefix tailTrace_481852
  have hstable : (prefixWord ++ tailWord_481852).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481852).length < 2 ^ (prefixWord ++ tailWord_481852).sum := by decide
  have hdescent : baseEnd_481852 < baseStart_481852 := by decide
  rcases family_descends (prefixWord ++ tailWord_481852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481869 : List Nat := [1, 6, 1, 1, 2, 2, 3, 3]
def baseStart_481869 : Nat := 118140960795 + 481869 * 2 ^ 59
def prefixEnd_481869 : Nat := 4983230072969 + 3 ^ 40 * 481869 * 2
def baseEnd_481869 : Nat := 146625427852729137197885

theorem tailTrace_481869 : CollatzResearch.WordTrace tailWord_481869 prefixEnd_481869 146625427852729137197885 := by
  unfold tailWord_481869
  simp only [CollatzResearch.WordTrace]
  refine ⟨17575206291278384518336661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11716804194185589678891107 17575206291278384518336661)
  ·
    refine ⟨823837794903674274297031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 17575206291278384518336661 823837794903674274297031)
    ·
      refine ⟨1235756692355511411445547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 823837794903674274297031 1235756692355511411445547)
      ·
        refine ⟨1853635038533267117168321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1235756692355511411445547 1853635038533267117168321)
        ·
          refine ⟨1390226278899950337876241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1853635038533267117168321 1390226278899950337876241)
          ·
            refine ⟨1042669709174962753407181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1390226278899950337876241 1042669709174962753407181)
            ·
              refine ⟨391001140940611032527693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1042669709174962753407181 391001140940611032527693)
              ·
                refine ⟨146625427852729137197885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 391001140940611032527693 146625427852729137197885)
                ·
                  rfl

theorem cell19_481869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 3, 3].length) (baseStart_481869 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_481869 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_481869 prefixEnd_481869 := by exact prefixLift 481869
  have htrace : WordTrace (prefixWord ++ tailWord_481869) baseStart_481869 baseEnd_481869 := by
    simpa [prefixWord, tailWord_481869, baseEnd_481869] using wordTrace_append hprefix tailTrace_481869
  have hstable : (prefixWord ++ tailWord_481869).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481869).length < 2 ^ (prefixWord ++ tailWord_481869).sum := by decide
  have hdescent : baseEnd_481869 < baseStart_481869 := by decide
  rcases family_descends (prefixWord ++ tailWord_481869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481886 : List Nat := [4, 4, 1, 2, 1, 1, 6]
def baseStart_481886 : Nat := 118140960795 + 481886 * 2 ^ 59
def prefixEnd_481886 : Nat := 4983230072969 + 3 ^ 40 * 481886 * 2
def baseEnd_481886 : Nat := 48876866898292711606687

theorem tailTrace_481886 : CollatzResearch.WordTrace tailWord_481886 prefixEnd_481886 48876866898292711606687 := by
  unfold tailWord_481886
  simp only [CollatzResearch.WordTrace]
  refine ⟨2196978291527099552713189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11717217554811197614470341 2196978291527099552713189)
  ·
    refine ⟨411933429661331166133723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2196978291527099552713189 411933429661331166133723)
    ·
      refine ⟨617900144491996749200585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411933429661331166133723 617900144491996749200585)
      ·
        refine ⟨463425108368997561900439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 617900144491996749200585 463425108368997561900439)
        ·
          refine ⟨695137662553496342850659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 463425108368997561900439 695137662553496342850659)
          ·
            refine ⟨1042706493830244514275989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 695137662553496342850659 1042706493830244514275989)
            ·
              refine ⟨48876866898292711606687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1042706493830244514275989 48876866898292711606687)
              ·
                rfl

theorem cell19_481886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 6].length) (baseStart_481886 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_481886 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_481886 prefixEnd_481886 := by exact prefixLift 481886
  have htrace : WordTrace (prefixWord ++ tailWord_481886) baseStart_481886 baseEnd_481886 := by
    simpa [prefixWord, tailWord_481886, baseEnd_481886] using wordTrace_append hprefix tailTrace_481886
  have hstable : (prefixWord ++ tailWord_481886).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481886).length < 2 ^ (prefixWord ++ tailWord_481886).sum := by decide
  have hdescent : baseEnd_481886 < baseStart_481886 := by decide
  rcases family_descends (prefixWord ++ tailWord_481886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481966 : List Nat := [4, 1, 4, 1, 1, 1, 1, 6]
def baseStart_481966 : Nat := 118140960795 + 481966 * 2 ^ 59
def prefixEnd_481966 : Nat := 4983230072969 + 3 ^ 40 * 481966 * 2
def baseEnd_481966 : Nat := 146654943481461653042065

theorem tailTrace_481966 : CollatzResearch.WordTrace tailWord_481966 prefixEnd_481966 146654943481461653042065 := by
  unfold tailWord_481966
  simp only [CollatzResearch.WordTrace]
  refine ⟨2197343021490871260577219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11719162781284646723078501 2197343021490871260577219)
  ·
    refine ⟨3296014532236306890865829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2197343021490871260577219 3296014532236306890865829)
    ·
      refine ⟨618002724794307542037343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3296014532236306890865829 618002724794307542037343)
      ·
        refine ⟨927004087191461313056015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 618002724794307542037343 927004087191461313056015)
        ·
          refine ⟨1390506130787191969584023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 927004087191461313056015 1390506130787191969584023)
          ·
            refine ⟨2085759196180787954376035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1390506130787191969584023 2085759196180787954376035)
            ·
              refine ⟨3128638794271181931564053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2085759196180787954376035 3128638794271181931564053)
              ·
                refine ⟨146654943481461653042065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3128638794271181931564053 146654943481461653042065)
                ·
                  rfl

theorem cell19_481966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 6].length) (baseStart_481966 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_481966 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_481966 prefixEnd_481966 := by exact prefixLift 481966
  have htrace : WordTrace (prefixWord ++ tailWord_481966) baseStart_481966 baseEnd_481966 := by
    simpa [prefixWord, tailWord_481966, baseEnd_481966] using wordTrace_append hprefix tailTrace_481966
  have hstable : (prefixWord ++ tailWord_481966).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481966).length < 2 ^ (prefixWord ++ tailWord_481966).sum := by decide
  have hdescent : baseEnd_481966 < baseStart_481966 := by decide
  rcases family_descends (prefixWord ++ tailWord_481966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482004 : List Nat := [2, 4, 1, 3, 3, 6]
def baseStart_482004 : Nat := 118140960795 + 482004 * 2 ^ 59
def prefixEnd_482004 : Nat := 4983230072969 + 3 ^ 40 * 482004 * 2
def baseEnd_482004 : Nat := 16296278478343202688613

theorem tailTrace_482004 : CollatzResearch.WordTrace tailWord_482004 prefixEnd_482004 16296278478343202688613 := by
  unfold tailWord_482004
  simp only [CollatzResearch.WordTrace]
  refine ⟨8790065072894651287250533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11720086763859535049667377 8790065072894651287250533)
  ·
    refine ⟨1648137201167747116359475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8790065072894651287250533 1648137201167747116359475)
    ·
      refine ⟨2472205801751620674539213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1648137201167747116359475 2472205801751620674539213)
      ·
        refine ⟨927077175656857752952205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2472205801751620674539213 927077175656857752952205)
        ·
          refine ⟨347653940871321657357077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 927077175656857752952205 347653940871321657357077)
          ·
            refine ⟨16296278478343202688613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 347653940871321657357077 16296278478343202688613)
            ·
              rfl

theorem cell19_482004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 6].length) (baseStart_482004 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_482004 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_482004 prefixEnd_482004 := by exact prefixLift 482004
  have htrace : WordTrace (prefixWord ++ tailWord_482004) baseStart_482004 baseEnd_482004 := by
    simpa [prefixWord, tailWord_482004, baseEnd_482004] using wordTrace_append hprefix tailTrace_482004
  have hstable : (prefixWord ++ tailWord_482004).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482004).length < 2 ^ (prefixWord ++ tailWord_482004).sum := by decide
  have hdescent : baseEnd_482004 < baseStart_482004 := by decide
  rcases family_descends (prefixWord ++ tailWord_482004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482006 : List Nat := [5, 2, 1, 11]
def baseStart_482006 : Nat := 118140960795 + 482006 * 2 ^ 59
def prefixEnd_482006 : Nat := 4983230072969 + 3 ^ 40 * 482006 * 2
def baseEnd_482006 : Nat := 1810705121910535952507

theorem tailTrace_482006 : CollatzResearch.WordTrace tailWord_482006 prefixEnd_482006 1810705121910535952507 := by
  unfold tailWord_482006
  simp only [CollatzResearch.WordTrace]
  refine ⟨1098762693236378557254617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11720135394521371277382581 1098762693236378557254617)
  ·
    refine ⟨824072019927283917940963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1098762693236378557254617 824072019927283917940963)
    ·
      refine ⟨1236108029890925876911445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 824072019927283917940963 1236108029890925876911445)
      ·
        refine ⟨1810705121910535952507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 11 1236108029890925876911445 1810705121910535952507)
        ·
          rfl

theorem cell19_482006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 11].length) (baseStart_482006 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_482006 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_482006 prefixEnd_482006 := by exact prefixLift 482006
  have htrace : WordTrace (prefixWord ++ tailWord_482006) baseStart_482006 baseEnd_482006 := by
    simpa [prefixWord, tailWord_482006, baseEnd_482006] using wordTrace_append hprefix tailTrace_482006
  have hstable : (prefixWord ++ tailWord_482006).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482006).length < 2 ^ (prefixWord ++ tailWord_482006).sum := by decide
  have hdescent : baseEnd_482006 < baseStart_482006 := by decide
  rcases family_descends (prefixWord ++ tailWord_482006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482008 : List Nat := [2, 1, 2, 2, 3, 9]
def baseStart_482008 : Nat := 118140960795 + 482008 * 2 ^ 59
def prefixEnd_482008 : Nat := 4983230072969 + 3 ^ 40 * 482008 * 2
def baseEnd_482008 : Nat := 16296413716046444456513

theorem tailTrace_482008 : CollatzResearch.WordTrace tailWord_482008 prefixEnd_482008 16296413716046444456513 := by
  unfold tailWord_482008
  simp only [CollatzResearch.WordTrace]
  refine ⟨8790138018887405628823339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11720184025183207505097785 8790138018887405628823339)
  ·
    refine ⟨13185207028331108443235009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8790138018887405628823339 13185207028331108443235009)
    ·
      refine ⟨9888905271248331332426257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13185207028331108443235009 9888905271248331332426257)
      ·
        refine ⟨7416678953436248499319693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9888905271248331332426257 7416678953436248499319693)
        ·
          refine ⟨2781254607538593187244885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7416678953436248499319693 2781254607538593187244885)
          ·
            refine ⟨16296413716046444456513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2781254607538593187244885 16296413716046444456513)
            ·
              rfl

theorem cell19_482008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 9].length) (baseStart_482008 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_482008 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_482008 prefixEnd_482008 := by exact prefixLift 482008
  have htrace : WordTrace (prefixWord ++ tailWord_482008) baseStart_482008 baseEnd_482008 := by
    simpa [prefixWord, tailWord_482008, baseEnd_482008] using wordTrace_append hprefix tailTrace_482008
  have hstable : (prefixWord ++ tailWord_482008).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482008).length < 2 ^ (prefixWord ++ tailWord_482008).sum := by decide
  have hdescent : baseEnd_482008 < baseStart_482008 := by decide
  rcases family_descends (prefixWord ++ tailWord_482008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482093 : List Nat := [1, 5, 3, 2, 2, 1, 2, 3]
def baseStart_482093 : Nat := 118140960795 + 482093 * 2 ^ 59
def prefixEnd_482093 : Nat := 4983230072969 + 3 ^ 40 * 482093 * 2
def baseEnd_482093 : Nat := 146693587655162988219497

theorem tailTrace_482093 : CollatzResearch.WordTrace tailWord_482093 prefixEnd_482093 146693587655162988219497 := by
  unfold tailWord_482093
  simp only [CollatzResearch.WordTrace]
  refine ⟨17583376242466870774490933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11722250828311247182993955 17583376242466870774490933)
  ·
    refine ⟨1648441522731269135108525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17583376242466870774490933 1648441522731269135108525)
    ·
      refine ⟨618165571024225925665697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1648441522731269135108525 618165571024225925665697)
      ·
        refine ⟨463624178268169444249273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 618165571024225925665697 463624178268169444249273)
        ·
          refine ⟨347718133701127083186955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 463624178268169444249273 347718133701127083186955)
          ·
            refine ⟨521577200551690624780433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 347718133701127083186955 521577200551690624780433)
            ·
              refine ⟨391182900413767968585325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 521577200551690624780433 391182900413767968585325)
              ·
                refine ⟨146693587655162988219497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 391182900413767968585325 146693587655162988219497)
                ·
                  rfl

theorem cell19_482093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 2, 3].length) (baseStart_482093 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_482093 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_482093 prefixEnd_482093 := by exact prefixLift 482093
  have htrace : WordTrace (prefixWord ++ tailWord_482093) baseStart_482093 baseEnd_482093 := by
    simpa [prefixWord, tailWord_482093, baseEnd_482093] using wordTrace_append hprefix tailTrace_482093
  have hstable : (prefixWord ++ tailWord_482093).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482093).length < 2 ^ (prefixWord ++ tailWord_482093).sum := by decide
  have hdescent : baseEnd_482093 < baseStart_482093 := by decide
  rcases family_descends (prefixWord ++ tailWord_482093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482099 : List Nat := [1, 1, 1, 2, 6, 3, 2, 3]
def baseStart_482099 : Nat := 118140960795 + 482099 * 2 ^ 59
def prefixEnd_482099 : Nat := 4983230072969 + 3 ^ 40 * 482099 * 2
def baseEnd_482099 : Nat := 146695413364156752086147

theorem tailTrace_482099 : CollatzResearch.WordTrace tailWord_482099 prefixEnd_482099 146695413364156752086147 := by
  unfold tailWord_482099
  simp only [CollatzResearch.WordTrace]
  refine ⟨17583595080445133799209351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11722396720296755866139567 17583595080445133799209351)
  ·
    refine ⟨26375392620667700698814027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17583595080445133799209351 26375392620667700698814027)
    ·
      refine ⟨39563088931001551048221041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26375392620667700698814027 39563088931001551048221041)
      ·
        refine ⟨29672316698251163286165781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39563088931001551048221041 29672316698251163286165781)
        ·
          refine ⟨1390889845230523279039021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 29672316698251163286165781 1390889845230523279039021)
          ·
            refine ⟨521583691961446229639633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1390889845230523279039021 521583691961446229639633)
            ·
              refine ⟨391187768971084672229725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 521583691961446229639633 391187768971084672229725)
              ·
                refine ⟨146695413364156752086147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 391187768971084672229725 146695413364156752086147)
                ·
                  rfl

theorem cell19_482099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 2, 3].length) (baseStart_482099 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_482099 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_482099 prefixEnd_482099 := by exact prefixLift 482099
  have htrace : WordTrace (prefixWord ++ tailWord_482099) baseStart_482099 baseEnd_482099 := by
    simpa [prefixWord, tailWord_482099, baseEnd_482099] using wordTrace_append hprefix tailTrace_482099
  have hstable : (prefixWord ++ tailWord_482099).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482099).length < 2 ^ (prefixWord ++ tailWord_482099).sum := by decide
  have hdescent : baseEnd_482099 < baseStart_482099 := by decide
  rcases family_descends (prefixWord ++ tailWord_482099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482101 : List Nat := [1, 3, 3, 1, 3, 2, 1, 5]
def baseStart_482101 : Nat := 118140960795 + 482101 * 2 ^ 59
def prefixEnd_482101 : Nat := 4983230072969 + 3 ^ 40 * 482101 * 2
def baseEnd_482101 : Nat := 146696021933821340041697

theorem tailTrace_482101 : CollatzResearch.WordTrace tailWord_482101 prefixEnd_482101 146696021933821340041697 := by
  unfold tailWord_482101
  simp only [CollatzResearch.WordTrace]
  refine ⟨17583668026437888140782157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11722445350958592093854771 17583668026437888140782157)
  ·
    refine ⟨6593875509914208052793309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17583668026437888140782157 6593875509914208052793309)
    ·
      refine ⟨2472703316217828019797491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6593875509914208052793309 2472703316217828019797491)
      ·
        refine ⟨3709054974326742029696237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2472703316217828019797491 3709054974326742029696237)
        ·
          refine ⟨1390895615372528261136089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3709054974326742029696237 1390895615372528261136089)
          ·
            refine ⟨1043171711529396195852067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1390895615372528261136089 1043171711529396195852067)
            ·
              refine ⟨1564757567294094293778101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1043171711529396195852067 1564757567294094293778101)
              ·
                refine ⟨146696021933821340041697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1564757567294094293778101 146696021933821340041697)
                ·
                  rfl

theorem cell19_482101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 5].length) (baseStart_482101 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_482101 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_482101 prefixEnd_482101 := by exact prefixLift 482101
  have htrace : WordTrace (prefixWord ++ tailWord_482101) baseStart_482101 baseEnd_482101 := by
    simpa [prefixWord, tailWord_482101, baseEnd_482101] using wordTrace_append hprefix tailTrace_482101
  have hstable : (prefixWord ++ tailWord_482101).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482101).length < 2 ^ (prefixWord ++ tailWord_482101).sum := by decide
  have hdescent : baseEnd_482101 < baseStart_482101 := by decide
  rcases family_descends (prefixWord ++ tailWord_482101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482103 : List Nat := [1, 1, 3, 1, 2, 1, 5, 5]
def baseStart_482103 : Nat := 118140960795 + 482103 * 2 ^ 59
def prefixEnd_482103 : Nat := 4983230072969 + 3 ^ 40 * 482103 * 2
def baseEnd_482103 : Nat := 146696630503485927997247

theorem tailTrace_482103 : CollatzResearch.WordTrace tailWord_482103 prefixEnd_482103 146696630503485927997247 := by
  unfold tailWord_482103
  simp only [CollatzResearch.WordTrace]
  refine ⟨17583740972430642482354963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11722493981620428321569975 17583740972430642482354963)
  ·
    refine ⟨26375611458645963723532445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17583740972430642482354963 26375611458645963723532445)
    ·
      refine ⟨9890854296992236396324667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26375611458645963723532445 9890854296992236396324667)
      ·
        refine ⟨14836281445488354594487001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9890854296992236396324667 14836281445488354594487001)
        ·
          refine ⟨11127211084116265945865251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14836281445488354594487001 11127211084116265945865251)
          ·
            refine ⟨16690816626174398918797877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11127211084116265945865251 16690816626174398918797877)
            ·
              refine ⟨1564764058703849898637301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16690816626174398918797877 1564764058703849898637301)
              ·
                refine ⟨146696630503485927997247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1564764058703849898637301 146696630503485927997247)
                ·
                  rfl

theorem cell19_482103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 5].length) (baseStart_482103 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_482103 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_482103 prefixEnd_482103 := by exact prefixLift 482103
  have htrace : WordTrace (prefixWord ++ tailWord_482103) baseStart_482103 baseEnd_482103 := by
    simpa [prefixWord, tailWord_482103, baseEnd_482103] using wordTrace_append hprefix tailTrace_482103
  have hstable : (prefixWord ++ tailWord_482103).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482103).length < 2 ^ (prefixWord ++ tailWord_482103).sum := by decide
  have hdescent : baseEnd_482103 < baseStart_482103 := by decide
  rcases family_descends (prefixWord ++ tailWord_482103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482116 : List Nat := [2, 3, 4, 2, 1, 2, 5]
def baseStart_482116 : Nat := 118140960795 + 482116 * 2 ^ 59
def prefixEnd_482116 : Nat := 4983230072969 + 3 ^ 40 * 482116 * 2
def baseEnd_482116 : Nat := 48900195402101916569441

theorem tailTrace_482116 : CollatzResearch.WordTrace tailWord_482116 prefixEnd_482116 48900195402101916569441 := by
  unfold tailWord_482116
  simp only [CollatzResearch.WordTrace]
  refine ⟨8792107560691772851289101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11722810080922363801718801 8792107560691772851289101)
  ·
    refine ⟨3297040335259414819233413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8792107560691772851289101 3297040335259414819233413)
    ·
      refine ⟨618195062861140278606265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3297040335259414819233413 618195062861140278606265)
      ·
        refine ⟨463646297145855208954699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 618195062861140278606265 463646297145855208954699)
        ·
          refine ⟨695469445718782813432049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 463646297145855208954699 695469445718782813432049)
          ·
            refine ⟨521602084289087110074037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 695469445718782813432049 521602084289087110074037)
            ·
              refine ⟨48900195402101916569441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 521602084289087110074037 48900195402101916569441)
              ·
                rfl

theorem cell19_482116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 5].length) (baseStart_482116 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_482116 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_482116 prefixEnd_482116 := by exact prefixLift 482116
  have htrace : WordTrace (prefixWord ++ tailWord_482116) baseStart_482116 baseEnd_482116 := by
    simpa [prefixWord, tailWord_482116, baseEnd_482116] using wordTrace_append hprefix tailTrace_482116
  have hstable : (prefixWord ++ tailWord_482116).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482116).length < 2 ^ (prefixWord ++ tailWord_482116).sum := by decide
  have hdescent : baseEnd_482116 < baseStart_482116 := by decide
  rcases family_descends (prefixWord ++ tailWord_482116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482160 : List Nat := [2, 1, 1, 1, 4, 1, 4, 5]
def baseStart_482160 : Nat := 118140960795 + 482160 * 2 ^ 59
def prefixEnd_482160 : Nat := 4983230072969 + 3 ^ 40 * 482160 * 2
def baseEnd_482160 : Nat := 146713974738926684730425

theorem tailTrace_482160 : CollatzResearch.WordTrace tailWord_482160 prefixEnd_482160 146713974738926684730425 := by
  unfold tailWord_482160
  simp only [CollatzResearch.WordTrace]
  refine ⟨8792909966612070608589967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11723879955482760811453289 8792909966612070608589967)
  ·
    refine ⟨13189364949918105912884951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8792909966612070608589967 13189364949918105912884951)
    ·
      refine ⟨19784047424877158869327427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13189364949918105912884951 19784047424877158869327427)
      ·
        refine ⟨29676071137315738303991141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19784047424877158869327427 29676071137315738303991141)
        ·
          refine ⟨5564263338246700931998339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29676071137315738303991141 5564263338246700931998339)
          ·
            refine ⟨8346395007370051397997509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5564263338246700931998339 8346395007370051397997509)
            ·
              refine ⟨1564949063881884637124533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8346395007370051397997509 1564949063881884637124533)
              ·
                refine ⟨146713974738926684730425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1564949063881884637124533 146713974738926684730425)
                ·
                  rfl

theorem cell19_482160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 5].length) (baseStart_482160 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_482160 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_482160 prefixEnd_482160 := by exact prefixLift 482160
  have htrace : WordTrace (prefixWord ++ tailWord_482160) baseStart_482160 baseEnd_482160 := by
    simpa [prefixWord, tailWord_482160, baseEnd_482160] using wordTrace_append hprefix tailTrace_482160
  have hstable : (prefixWord ++ tailWord_482160).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482160).length < 2 ^ (prefixWord ++ tailWord_482160).sum := by decide
  have hdescent : baseEnd_482160 < baseStart_482160 := by decide
  rcases family_descends (prefixWord ++ tailWord_482160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482306 : List Nat := [3, 4, 1, 3, 1, 1, 2, 4]
def baseStart_482306 : Nat := 118140960795 + 482306 * 2 ^ 59
def prefixEnd_482306 : Nat := 4983230072969 + 3 ^ 40 * 482306 * 2
def baseEnd_482306 : Nat := 146758400324441605485583

theorem tailTrace_482306 : CollatzResearch.WordTrace tailWord_482306 prefixEnd_482306 146758400324441605485583 := by
  unfold tailWord_482306
  simp only [CollatzResearch.WordTrace]
  refine ⟨4397786247673802037998693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11727429993796805434663181 4397786247673802037998693)
  ·
    refine ⟨824584921438837882124755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4397786247673802037998693 824584921438837882124755)
    ·
      refine ⟨1236877382158256823187133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 824584921438837882124755 1236877382158256823187133)
      ·
        refine ⟨463829018309346308695175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1236877382158256823187133 463829018309346308695175)
        ·
          refine ⟨695743527464019463042763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 463829018309346308695175 695743527464019463042763)
          ·
            refine ⟨1043615291196029194564145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 695743527464019463042763 1043615291196029194564145)
            ·
              refine ⟨782711468397021895923109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1043615291196029194564145 782711468397021895923109)
              ·
                refine ⟨146758400324441605485583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 782711468397021895923109 146758400324441605485583)
                ·
                  rfl

theorem cell19_482306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 4].length) (baseStart_482306 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_482306 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_482306 prefixEnd_482306 := by exact prefixLift 482306
  have htrace : WordTrace (prefixWord ++ tailWord_482306) baseStart_482306 baseEnd_482306 := by
    simpa [prefixWord, tailWord_482306, baseEnd_482306] using wordTrace_append hprefix tailTrace_482306
  have hstable : (prefixWord ++ tailWord_482306).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482306).length < 2 ^ (prefixWord ++ tailWord_482306).sum := by decide
  have hdescent : baseEnd_482306 < baseStart_482306 := by decide
  rcases family_descends (prefixWord ++ tailWord_482306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482312 : List Nat := [2, 1, 3, 2, 1, 3, 1, 6]
def baseStart_482312 : Nat := 118140960795 + 482312 * 2 ^ 59
def prefixEnd_482312 : Nat := 4983230072969 + 3 ^ 40 * 482312 * 2
def baseEnd_482312 : Nat := 146760226033435369352233

theorem tailTrace_482312 : CollatzResearch.WordTrace tailWord_482312 prefixEnd_482312 146760226033435369352233 := by
  unfold tailWord_482312
  simp only [CollatzResearch.WordTrace]
  refine ⟨8795681914336735588356595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11727575885782314117808793 8795681914336735588356595)
  ·
    refine ⟨13193522871505103382534893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8795681914336735588356595 13193522871505103382534893)
    ·
      refine ⟨4947571076814413768450585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13193522871505103382534893 4947571076814413768450585)
      ·
        refine ⟨3710678307610810326337939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4947571076814413768450585 3710678307610810326337939)
        ·
          refine ⟨5566017461416215489506909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3710678307610810326337939 5566017461416215489506909)
          ·
            refine ⟨2087256548031080808565091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5566017461416215489506909 2087256548031080808565091)
            ·
              refine ⟨3130884822046621212847637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2087256548031080808565091 3130884822046621212847637)
              ·
                refine ⟨146760226033435369352233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3130884822046621212847637 146760226033435369352233)
                ·
                  rfl

theorem cell19_482312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 6].length) (baseStart_482312 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_482312 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_482312 prefixEnd_482312 := by exact prefixLift 482312
  have htrace : WordTrace (prefixWord ++ tailWord_482312) baseStart_482312 baseEnd_482312 := by
    simpa [prefixWord, tailWord_482312, baseEnd_482312] using wordTrace_append hprefix tailTrace_482312
  have hstable : (prefixWord ++ tailWord_482312).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482312).length < 2 ^ (prefixWord ++ tailWord_482312).sum := by decide
  have hdescent : baseEnd_482312 < baseStart_482312 := by decide
  rcases family_descends (prefixWord ++ tailWord_482312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482388 : List Nat := [2, 4, 1, 1, 1, 1, 2, 7]
def baseStart_482388 : Nat := 118140960795 + 482388 * 2 ^ 59
def prefixEnd_482388 : Nat := 4983230072969 + 3 ^ 40 * 482388 * 2
def baseEnd_482388 : Nat := 146783351680689711663137

theorem tailTrace_482388 : CollatzResearch.WordTrace tailWord_482388 prefixEnd_482388 146783351680689711663137 := by
  unfold tailWord_482388
  simp only [CollatzResearch.WordTrace]
  refine ⟨8797067888199068078239909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11729423850932090770986545 8797067888199068078239909)
  ·
    refine ⟨1649450229037325264669983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8797067888199068078239909 1649450229037325264669983)
    ·
      refine ⟨2474175343555987897004975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1649450229037325264669983 2474175343555987897004975)
      ·
        refine ⟨3711263015333981845507463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2474175343555987897004975 3711263015333981845507463)
        ·
          refine ⟨5566894523000972768261195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3711263015333981845507463 5566894523000972768261195)
          ·
            refine ⟨8350341784501459152391793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5566894523000972768261195 8350341784501459152391793)
            ·
              refine ⟨6262756338376094364293845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8350341784501459152391793 6262756338376094364293845)
              ·
                refine ⟨146783351680689711663137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6262756338376094364293845 146783351680689711663137)
                ·
                  rfl

theorem cell19_482388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 7].length) (baseStart_482388 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_482388 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_482388 prefixEnd_482388 := by exact prefixLift 482388
  have htrace : WordTrace (prefixWord ++ tailWord_482388) baseStart_482388 baseEnd_482388 := by
    simpa [prefixWord, tailWord_482388, baseEnd_482388] using wordTrace_append hprefix tailTrace_482388
  have hstable : (prefixWord ++ tailWord_482388).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482388).length < 2 ^ (prefixWord ++ tailWord_482388).sum := by decide
  have hdescent : baseEnd_482388 < baseStart_482388 := by decide
  rcases family_descends (prefixWord ++ tailWord_482388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482407 : List Nat := [1, 1, 5, 1, 1, 4, 6]
def baseStart_482407 : Nat := 118140960795 + 482407 * 2 ^ 59
def prefixEnd_482407 : Nat := 4983230072969 + 3 ^ 40 * 482407 * 2
def baseEnd_482407 : Nat := 48929711030834432413621

theorem tailTrace_482407 : CollatzResearch.WordTrace tailWord_482407 prefixEnd_482407 48929711030834432413621 := by
  unfold tailWord_482407
  simp only [CollatzResearch.WordTrace]
  refine ⟨17594828763329302401421475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11729885842219534934280983 17594828763329302401421475)
  ·
    refine ⟨26392243144993953602132213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17594828763329302401421475 26392243144993953602132213)
    ·
      refine ⟨2474272794843183150199895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26392243144993953602132213 2474272794843183150199895)
      ·
        refine ⟨3711409192264774725299843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2474272794843183150199895 3711409192264774725299843)
        ·
          refine ⟨5567113788397162087949765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3711409192264774725299843 5567113788397162087949765)
          ·
            refine ⟨1043833835324467891490581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5567113788397162087949765 1043833835324467891490581)
            ·
              refine ⟨48929711030834432413621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1043833835324467891490581 48929711030834432413621)
              ·
                rfl

theorem cell19_482407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 6].length) (baseStart_482407 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_482407 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_482407 prefixEnd_482407 := by exact prefixLift 482407
  have htrace : WordTrace (prefixWord ++ tailWord_482407) baseStart_482407 baseEnd_482407 := by
    simpa [prefixWord, tailWord_482407, baseEnd_482407] using wordTrace_append hprefix tailTrace_482407
  have hstable : (prefixWord ++ tailWord_482407).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482407).length < 2 ^ (prefixWord ++ tailWord_482407).sum := by decide
  have hdescent : baseEnd_482407 < baseStart_482407 := by decide
  rcases family_descends (prefixWord ++ tailWord_482407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482462 : List Nat := [4, 3, 1, 1, 2, 1, 7]
def baseStart_482462 : Nat := 118140960795 + 482462 * 2 ^ 59
def prefixEnd_482462 : Nat := 4983230072969 + 3 ^ 40 * 482462 * 2
def baseEnd_482462 : Nat := 48935289586093155339497

theorem tailTrace_482462 : CollatzResearch.WordTrace tailWord_482462 prefixEnd_482462 48935289586093155339497 := by
  unfold tailWord_482462
  simp only [CollatzResearch.WordTrace]
  refine ⟨2199604347266255849334205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11731223185420031196449093 2199604347266255849334205)
  ·
    refine ⟨824851630224845943500327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2199604347266255849334205 824851630224845943500327)
    ·
      refine ⟨1237277445337268915250491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 824851630224845943500327 1237277445337268915250491)
      ·
        refine ⟨1855916168005903372875737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1237277445337268915250491 1855916168005903372875737)
        ·
          refine ⟨1391937126004427529656803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1855916168005903372875737 1391937126004427529656803)
          ·
            refine ⟨2087905689006641294485205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1391937126004427529656803 2087905689006641294485205)
            ·
              refine ⟨48935289586093155339497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2087905689006641294485205 48935289586093155339497)
              ·
                rfl

theorem cell19_482462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 7].length) (baseStart_482462 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_482462 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_482462 prefixEnd_482462 := by exact prefixLift 482462
  have htrace : WordTrace (prefixWord ++ tailWord_482462) baseStart_482462 baseEnd_482462 := by
    simpa [prefixWord, tailWord_482462, baseEnd_482462] using wordTrace_append hprefix tailTrace_482462
  have hstable : (prefixWord ++ tailWord_482462).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482462).length < 2 ^ (prefixWord ++ tailWord_482462).sum := by decide
  have hdescent : baseEnd_482462 < baseStart_482462 := by decide
  rcases family_descends (prefixWord ++ tailWord_482462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482481 : List Nat := [1, 2, 2, 5, 1, 2, 2, 4]
def baseStart_482481 : Nat := 118140960795 + 482481 * 2 ^ 59
def prefixEnd_482481 : Nat := 4983230072969 + 3 ^ 40 * 482481 * 2
def baseEnd_482481 : Nat := 146811650170093051596217

theorem tailTrace_482481 : CollatzResearch.WordTrace tailWord_482481 prefixEnd_482481 146811650170093051596217 := by
  unfold tailWord_482481
  simp only [CollatzResearch.WordTrace]
  refine ⟨17597527765061213039615297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11731685176707475359743531 17597527765061213039615297)
  ·
    refine ⟨13198145823795909779711473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17597527765061213039615297 13198145823795909779711473)
    ·
      refine ⟨9898609367846932334783605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13198145823795909779711473 9898609367846932334783605)
      ·
        refine ⟨927994628235649906385963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9898609367846932334783605 927994628235649906385963)
        ·
          refine ⟨1391991942353474859578945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 927994628235649906385963 1391991942353474859578945)
          ·
            refine ⟨1043993956765106144684209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1391991942353474859578945 1043993956765106144684209)
            ·
              refine ⟨782995467573829608513157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1043993956765106144684209 782995467573829608513157)
              ·
                refine ⟨146811650170093051596217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 782995467573829608513157 146811650170093051596217)
                ·
                  rfl

theorem cell19_482481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 4].length) (baseStart_482481 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_482481 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_482481 prefixEnd_482481 := by exact prefixLift 482481
  have htrace : WordTrace (prefixWord ++ tailWord_482481) baseStart_482481 baseEnd_482481 := by
    simpa [prefixWord, tailWord_482481, baseEnd_482481] using wordTrace_append hprefix tailTrace_482481
  have hstable : (prefixWord ++ tailWord_482481).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482481).length < 2 ^ (prefixWord ++ tailWord_482481).sum := by decide
  have hdescent : baseEnd_482481 < baseStart_482481 := by decide
  rcases family_descends (prefixWord ++ tailWord_482481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482538 : List Nat := [3, 1, 3, 1, 1, 5, 1, 4]
def baseStart_482538 : Nat := 118140960795 + 482538 * 2 ^ 59
def prefixEnd_482538 : Nat := 4983230072969 + 3 ^ 40 * 482538 * 2
def baseEnd_482538 : Nat := 146828994405533808329395

theorem tailTrace_482538 : CollatzResearch.WordTrace tailWord_482538 prefixEnd_482538 146828994405533808329395 := by
  unfold tailWord_482538
  simp only [CollatzResearch.WordTrace]
  refine ⟨4399901681463677943610067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11733071150569807849626845 4399901681463677943610067)
  ·
    refine ⟨6599852522195516915415101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4399901681463677943610067 6599852522195516915415101)
    ·
      refine ⟨2474944695823318843280663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6599852522195516915415101 2474944695823318843280663)
      ·
        refine ⟨3712417043734978264920995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2474944695823318843280663 3712417043734978264920995)
        ·
          refine ⟨5568625565602467397381493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3712417043734978264920995 5568625565602467397381493)
          ·
            refine ⟨522058646775231318504515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5568625565602467397381493 522058646775231318504515)
            ·
              refine ⟨783087970162846977756773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 522058646775231318504515 783087970162846977756773)
              ·
                refine ⟨146828994405533808329395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 783087970162846977756773 146828994405533808329395)
                ·
                  rfl

theorem cell19_482538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 4].length) (baseStart_482538 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_482538 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_482538 prefixEnd_482538 := by exact prefixLift 482538
  have htrace : WordTrace (prefixWord ++ tailWord_482538) baseStart_482538 baseEnd_482538 := by
    simpa [prefixWord, tailWord_482538, baseEnd_482538] using wordTrace_append hprefix tailTrace_482538
  have hstable : (prefixWord ++ tailWord_482538).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482538).length < 2 ^ (prefixWord ++ tailWord_482538).sum := by decide
  have hdescent : baseEnd_482538 < baseStart_482538 := by decide
  rcases family_descends (prefixWord ++ tailWord_482538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482540 : List Nat := [2, 2, 1, 1, 2, 4, 3, 4]
def baseStart_482540 : Nat := 118140960795 + 482540 * 2 ^ 59
def prefixEnd_482540 : Nat := 4983230072969 + 3 ^ 40 * 482540 * 2
def baseEnd_482540 : Nat := 146829602975198396284945

theorem tailTrace_482540 : CollatzResearch.WordTrace tailWord_482540 prefixEnd_482540 146829602975198396284945 := by
  unfold tailWord_482540
  simp only [CollatzResearch.WordTrace]
  refine ⟨8799839835923733058006537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11733119781231644077342049 8799839835923733058006537)
  ·
    refine ⟨6599879876942799793504903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8799839835923733058006537 6599879876942799793504903)
    ·
      refine ⟨9899819815414199690257355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6599879876942799793504903 9899819815414199690257355)
      ·
        refine ⟨14849729723121299535386033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9899819815414199690257355 14849729723121299535386033)
        ·
          refine ⟨11137297292340974651539525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14849729723121299535386033 11137297292340974651539525)
          ·
            refine ⟨2088243242313932747163661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11137297292340974651539525 2088243242313932747163661)
            ·
              refine ⟨783091215867724780186373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2088243242313932747163661 783091215867724780186373)
              ·
                refine ⟨146829602975198396284945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 783091215867724780186373 146829602975198396284945)
                ·
                  rfl

theorem cell19_482540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 4].length) (baseStart_482540 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_482540 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_482540 prefixEnd_482540 := by exact prefixLift 482540
  have htrace : WordTrace (prefixWord ++ tailWord_482540) baseStart_482540 baseEnd_482540 := by
    simpa [prefixWord, tailWord_482540, baseEnd_482540] using wordTrace_append hprefix tailTrace_482540
  have hstable : (prefixWord ++ tailWord_482540).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482540).length < 2 ^ (prefixWord ++ tailWord_482540).sum := by decide
  have hdescent : baseEnd_482540 < baseStart_482540 := by decide
  rcases family_descends (prefixWord ++ tailWord_482540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482646 : List Nat := [5, 2, 3, 1, 1, 1, 2, 4]
def baseStart_482646 : Nat := 118140960795 + 482646 * 2 ^ 59
def prefixEnd_482646 : Nat := 4983230072969 + 3 ^ 40 * 482646 * 2
def baseEnd_482646 : Nat := 146861857167421557929101

theorem tailTrace_482646 : CollatzResearch.WordTrace tailWord_482646 prefixEnd_482646 146861857167421557929101 := by
  unfold tailWord_482646
  simp only [CollatzResearch.WordTrace]
  refine ⟨1100221613091465388710737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11735697206308964146247861 1100221613091465388710737)
  ·
    refine ⟨825166209818599041533053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1100221613091465388710737 825166209818599041533053)
    ·
      refine ⟨309437328681974640574895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 825166209818599041533053 309437328681974640574895)
      ·
        refine ⟨464155993022961960862343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309437328681974640574895 464155993022961960862343)
        ·
          refine ⟨696233989534442941293515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 464155993022961960862343 696233989534442941293515)
          ·
            refine ⟨1044350984301664411940273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 696233989534442941293515 1044350984301664411940273)
            ·
              refine ⟨783263238226248308955205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1044350984301664411940273 783263238226248308955205)
              ·
                refine ⟨146861857167421557929101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 783263238226248308955205 146861857167421557929101)
                ·
                  rfl

theorem cell19_482646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 4].length) (baseStart_482646 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_482646 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_482646 prefixEnd_482646 := by exact prefixLift 482646
  have htrace : WordTrace (prefixWord ++ tailWord_482646) baseStart_482646 baseEnd_482646 := by
    simpa [prefixWord, tailWord_482646, baseEnd_482646] using wordTrace_append hprefix tailTrace_482646
  have hstable : (prefixWord ++ tailWord_482646).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482646).length < 2 ^ (prefixWord ++ tailWord_482646).sum := by decide
  have hdescent : baseEnd_482646 < baseStart_482646 := by decide
  rcases family_descends (prefixWord ++ tailWord_482646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482690 : List Nat := [3, 4, 2, 1, 1, 8]
def baseStart_482690 : Nat := 118140960795 + 482690 * 2 ^ 59
def prefixEnd_482690 : Nat := 4983230072969 + 3 ^ 40 * 482690 * 2
def baseEnd_482690 : Nat := 16319471744449165883467

theorem tailTrace_482690 : CollatzResearch.WordTrace tailWord_482690 prefixEnd_482690 16319471744449165883467 := by
  unfold tailWord_482690
  simp only [CollatzResearch.WordTrace]
  refine ⟨4401287655326010433493381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11736767080869361155982349 4401287655326010433493381)
  ·
    refine ⟨825241435373626956280009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4401287655326010433493381 825241435373626956280009)
    ·
      refine ⟨618931076530220217210007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 825241435373626956280009 618931076530220217210007)
      ·
        refine ⟨928396614795330325815011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 618931076530220217210007 928396614795330325815011)
        ·
          refine ⟨1392594922192995488722517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 928396614795330325815011 1392594922192995488722517)
          ·
            refine ⟨16319471744449165883467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1392594922192995488722517 16319471744449165883467)
            ·
              rfl

theorem cell19_482690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 8].length) (baseStart_482690 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_482690 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_482690 prefixEnd_482690 := by exact prefixLift 482690
  have htrace : WordTrace (prefixWord ++ tailWord_482690) baseStart_482690 baseEnd_482690 := by
    simpa [prefixWord, tailWord_482690, baseEnd_482690] using wordTrace_append hprefix tailTrace_482690
  have hstable : (prefixWord ++ tailWord_482690).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482690).length < 2 ^ (prefixWord ++ tailWord_482690).sum := by decide
  have hdescent : baseEnd_482690 < baseStart_482690 := by decide
  rcases family_descends (prefixWord ++ tailWord_482690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482732 : List Nat := [2, 2, 1, 1, 1, 1, 4, 7]
def baseStart_482732 : Nat := 118140960795 + 482732 * 2 ^ 59
def prefixEnd_482732 : Nat := 4983230072969 + 3 ^ 40 * 482732 * 2
def baseEnd_482732 : Nat := 146888025662998840017755

theorem tailTrace_482732 : CollatzResearch.WordTrace tailWord_482732 prefixEnd_482732 146888025662998840017755 := by
  unfold tailWord_482732
  simp only [CollatzResearch.WordTrace]
  refine ⟨8803341243575941453501225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11737788324767921938001633 8803341243575941453501225)
  ·
    refine ⟨6602505932681956090125919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8803341243575941453501225 6602505932681956090125919)
    ·
      refine ⟨9903758899022934135188879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6602505932681956090125919 9903758899022934135188879)
      ·
        refine ⟨14855638348534401202783319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9903758899022934135188879 14855638348534401202783319)
        ·
          refine ⟨22283457522801601804174979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14855638348534401202783319 22283457522801601804174979)
          ·
            refine ⟨33425186284202402706262469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22283457522801601804174979 33425186284202402706262469)
            ·
              refine ⟨6267222428287950507424213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33425186284202402706262469 6267222428287950507424213)
              ·
                refine ⟨146888025662998840017755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6267222428287950507424213 146888025662998840017755)
                ·
                  rfl

theorem cell19_482732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 7].length) (baseStart_482732 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_482732 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_482732 prefixEnd_482732 := by exact prefixLift 482732
  have htrace : WordTrace (prefixWord ++ tailWord_482732) baseStart_482732 baseEnd_482732 := by
    simpa [prefixWord, tailWord_482732, baseEnd_482732] using wordTrace_append hprefix tailTrace_482732
  have hstable : (prefixWord ++ tailWord_482732).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482732).length < 2 ^ (prefixWord ++ tailWord_482732).sum := by decide
  have hdescent : baseEnd_482732 < baseStart_482732 := by decide
  rcases family_descends (prefixWord ++ tailWord_482732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482785 : List Nat := [1, 2, 3, 1, 2, 5, 2, 3]
def baseStart_482785 : Nat := 118140960795 + 482785 * 2 ^ 59
def prefixEnd_482785 : Nat := 4983230072969 + 3 ^ 40 * 482785 * 2
def baseEnd_482785 : Nat := 146904152759110420839833

theorem tailTrace_482785 : CollatzResearch.WordTrace tailWord_482785 prefixEnd_482785 146904152759110420839833 := by
  unfold tailWord_482785
  simp only [CollatzResearch.WordTrace]
  refine ⟨17608615555959872958681809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11739077037306581972454539 17608615555959872958681809)
  ·
    refine ⟨13206461666969904719011357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17608615555959872958681809 13206461666969904719011357)
    ·
      refine ⟨4952423125113714269629259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13206461666969904719011357 4952423125113714269629259)
      ·
        refine ⟨7428634687670571404443889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4952423125113714269629259 7428634687670571404443889)
        ·
          refine ⟨5571476015752928553332917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7428634687670571404443889 5571476015752928553332917)
          ·
            refine ⟨522325876476837051874961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5571476015752928553332917 522325876476837051874961)
            ·
              refine ⟨391744407357627788906221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 522325876476837051874961 391744407357627788906221)
              ·
                refine ⟨146904152759110420839833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 391744407357627788906221 146904152759110420839833)
                ·
                  rfl

theorem cell19_482785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 2, 3].length) (baseStart_482785 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_482785 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_482785 prefixEnd_482785 := by exact prefixLift 482785
  have htrace : WordTrace (prefixWord ++ tailWord_482785) baseStart_482785 baseEnd_482785 := by
    simpa [prefixWord, tailWord_482785, baseEnd_482785] using wordTrace_append hprefix tailTrace_482785
  have hstable : (prefixWord ++ tailWord_482785).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482785).length < 2 ^ (prefixWord ++ tailWord_482785).sum := by decide
  have hdescent : baseEnd_482785 < baseStart_482785 := by decide
  rcases family_descends (prefixWord ++ tailWord_482785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482787 : List Nat := [1, 1, 1, 6, 2, 2, 1, 5]
def baseStart_482787 : Nat := 118140960795 + 482787 * 2 ^ 59
def prefixEnd_482787 : Nat := 4983230072969 + 3 ^ 40 * 482787 * 2
def baseEnd_482787 : Nat := 146904761328775008795383

theorem tailTrace_482787 : CollatzResearch.WordTrace tailWord_482787 prefixEnd_482787 146904761328775008795383 := by
  unfold tailWord_482787
  simp only [CollatzResearch.WordTrace]
  refine ⟨17608688501952627300254615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11739125667968418200169743 17608688501952627300254615)
  ·
    refine ⟨26413032752928940950381923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17608688501952627300254615 26413032752928940950381923)
    ·
      refine ⟨39619549129393411425572885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26413032752928940950381923 39619549129393411425572885)
      ·
        refine ⟨1857166365440316160573729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 39619549129393411425572885 1857166365440316160573729)
        ·
          refine ⟨1392874774080237120430297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1857166365440316160573729 1392874774080237120430297)
          ·
            refine ⟨1044656080560177840322723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1392874774080237120430297 1044656080560177840322723)
            ·
              refine ⟨1566984120840266760484085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1044656080560177840322723 1566984120840266760484085)
              ·
                refine ⟨146904761328775008795383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1566984120840266760484085 146904761328775008795383)
                ·
                  rfl

theorem cell19_482787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 5].length) (baseStart_482787 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_482787 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_482787 prefixEnd_482787 := by exact prefixLift 482787
  have htrace : WordTrace (prefixWord ++ tailWord_482787) baseStart_482787 baseEnd_482787 := by
    simpa [prefixWord, tailWord_482787, baseEnd_482787] using wordTrace_append hprefix tailTrace_482787
  have hstable : (prefixWord ++ tailWord_482787).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482787).length < 2 ^ (prefixWord ++ tailWord_482787).sum := by decide
  have hdescent : baseEnd_482787 < baseStart_482787 := by decide
  rcases family_descends (prefixWord ++ tailWord_482787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482806 : List Nat := [5, 1, 1, 1, 2, 2, 7]
def baseStart_482806 : Nat := 118140960795 + 482806 * 2 ^ 59
def prefixEnd_482806 : Nat := 4983230072969 + 3 ^ 40 * 482806 * 2
def baseEnd_482806 : Nat := 48970180913529531457703

theorem tailTrace_482806 : CollatzResearch.WordTrace tailWord_482806 prefixEnd_482806 48970180913529531457703 := by
  unfold tailWord_482806
  simp only [CollatzResearch.WordTrace]
  refine ⟨1100586343055237096574767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11739587659255862363464181 1100586343055237096574767)
  ·
    refine ⟨1650879514582855644862151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1100586343055237096574767 1650879514582855644862151)
    ·
      refine ⟨2476319271874283467293227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1650879514582855644862151 2476319271874283467293227)
      ·
        refine ⟨3714478907811425200939841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2476319271874283467293227 3714478907811425200939841)
        ·
          refine ⟨2785859180858568900704881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3714478907811425200939841 2785859180858568900704881)
          ·
            refine ⟨2089394385643926675528661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2785859180858568900704881 2089394385643926675528661)
            ·
              refine ⟨48970180913529531457703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2089394385643926675528661 48970180913529531457703)
              ·
                rfl

theorem cell19_482806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 7].length) (baseStart_482806 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_482806 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_482806 prefixEnd_482806 := by exact prefixLift 482806
  have htrace : WordTrace (prefixWord ++ tailWord_482806) baseStart_482806 baseEnd_482806 := by
    simpa [prefixWord, tailWord_482806, baseEnd_482806] using wordTrace_append hprefix tailTrace_482806
  have hstable : (prefixWord ++ tailWord_482806).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482806).length < 2 ^ (prefixWord ++ tailWord_482806).sum := by decide
  have hdescent : baseEnd_482806 < baseStart_482806 := by decide
  rcases family_descends (prefixWord ++ tailWord_482806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482808 : List Nat := [2, 1, 2, 1, 1, 5, 7]
def baseStart_482808 : Nat := 118140960795 + 482808 * 2 ^ 59
def prefixEnd_482808 : Nat := 4983230072969 + 3 ^ 40 * 482808 * 2
def baseEnd_482808 : Nat := 48970383770084394109553

theorem tailTrace_482808 : CollatzResearch.WordTrace tailWord_482808 prefixEnd_482808 48970383770084394109553 := by
  unfold tailWord_482808
  simp only [CollatzResearch.WordTrace]
  refine ⟨8804727217438273943384539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11739636289917698591179385 8804727217438273943384539)
  ·
    refine ⟨13207090826157410915076809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8804727217438273943384539 13207090826157410915076809)
    ·
      refine ⟨9905318119618058186307607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13207090826157410915076809 9905318119618058186307607)
      ·
        refine ⟨14857977179427087279461411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9905318119618058186307607 14857977179427087279461411)
        ·
          refine ⟨22286965769140630919192117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14857977179427087279461411 22286965769140630919192117)
          ·
            refine ⟨2089403040856934148674261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22286965769140630919192117 2089403040856934148674261)
            ·
              refine ⟨48970383770084394109553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2089403040856934148674261 48970383770084394109553)
              ·
                rfl

theorem cell19_482808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 7].length) (baseStart_482808 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_482808 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_482808 prefixEnd_482808 := by exact prefixLift 482808
  have htrace : WordTrace (prefixWord ++ tailWord_482808) baseStart_482808 baseEnd_482808 := by
    simpa [prefixWord, tailWord_482808, baseEnd_482808] using wordTrace_append hprefix tailTrace_482808
  have hstable : (prefixWord ++ tailWord_482808).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482808).length < 2 ^ (prefixWord ++ tailWord_482808).sum := by decide
  have hdescent : baseEnd_482808 < baseStart_482808 := by decide
  rcases family_descends (prefixWord ++ tailWord_482808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482920 : List Nat := [2, 1, 4, 3, 1, 2, 6]
def baseStart_482920 : Nat := 118140960795 + 482920 * 2 ^ 59
def prefixEnd_482920 : Nat := 4983230072969 + 3 ^ 40 * 482920 * 2
def baseEnd_482920 : Nat := 48981743737156702613155

theorem tailTrace_482920 : CollatzResearch.WordTrace tailWord_482920 prefixEnd_482920 48981743737156702613155 := by
  unfold tailWord_482920
  simp only [CollatzResearch.WordTrace]
  refine ⟨8806769705235395507423107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11742359606980527343230809 8806769705235395507423107)
  ·
    refine ⟨13210154557853093261134661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8806769705235395507423107 13210154557853093261134661)
    ·
      refine ⟨2476903979597454986462749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13210154557853093261134661 2476903979597454986462749)
      ·
        refine ⟨928838992349045619923531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2476903979597454986462749 928838992349045619923531)
        ·
          refine ⟨1393258488523568429885297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 928838992349045619923531 1393258488523568429885297)
          ·
            refine ⟨1044943866392676322413973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1393258488523568429885297 1044943866392676322413973)
            ·
              refine ⟨48981743737156702613155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1044943866392676322413973 48981743737156702613155)
              ·
                rfl

theorem cell19_482920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 6].length) (baseStart_482920 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_482920 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_482920 prefixEnd_482920 := by exact prefixLift 482920
  have htrace : WordTrace (prefixWord ++ tailWord_482920) baseStart_482920 baseEnd_482920 := by
    simpa [prefixWord, tailWord_482920, baseEnd_482920] using wordTrace_append hprefix tailTrace_482920
  have hstable : (prefixWord ++ tailWord_482920).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482920).length < 2 ^ (prefixWord ++ tailWord_482920).sum := by decide
  have hdescent : baseEnd_482920 < baseStart_482920 := by decide
  rcases family_descends (prefixWord ++ tailWord_482920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482952 : List Nat := [2, 1, 3, 5, 2, 1, 2, 3]
def baseStart_482952 : Nat := 118140960795 + 482952 * 2 ^ 59
def prefixEnd_482952 : Nat := 4983230072969 + 3 ^ 40 * 482952 * 2
def baseEnd_482952 : Nat := 146954968326103515128267

theorem tailTrace_482952 : CollatzResearch.WordTrace tailWord_482952 prefixEnd_482952 146954968326103515128267 := by
  unfold tailWord_482952
  simp only [CollatzResearch.WordTrace]
  refine ⟨8807353273177430240005555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11743137697569906986674073 8807353273177430240005555)
  ·
    refine ⟨13211029909766145360008333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8807353273177430240005555 13211029909766145360008333)
    ·
      refine ⟨4954136216162304510003125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13211029909766145360008333 4954136216162304510003125)
      ·
        refine ⟨464450270265216047812793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4954136216162304510003125 464450270265216047812793)
        ·
          refine ⟨348337702698912035859595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 464450270265216047812793 348337702698912035859595)
          ·
            refine ⟨522506554048368053789393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 348337702698912035859595 522506554048368053789393)
            ·
              refine ⟨391879915536276040342045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 522506554048368053789393 391879915536276040342045)
              ·
                refine ⟨146954968326103515128267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 391879915536276040342045 146954968326103515128267)
                ·
                  rfl

theorem cell19_482952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 2, 3].length) (baseStart_482952 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_482952 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_482952 prefixEnd_482952 := by exact prefixLift 482952
  have htrace : WordTrace (prefixWord ++ tailWord_482952) baseStart_482952 baseEnd_482952 := by
    simpa [prefixWord, tailWord_482952, baseEnd_482952] using wordTrace_append hprefix tailTrace_482952
  have hstable : (prefixWord ++ tailWord_482952).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482952).length < 2 ^ (prefixWord ++ tailWord_482952).sum := by decide
  have hdescent : baseEnd_482952 < baseStart_482952 := by decide
  rcases family_descends (prefixWord ++ tailWord_482952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482958 : List Nat := [4, 1, 1, 3, 1, 3, 1, 5]
def baseStart_482958 : Nat := 118140960795 + 482958 * 2 ^ 59
def prefixEnd_482958 : Nat := 4983230072969 + 3 ^ 40 * 482958 * 2
def baseEnd_482958 : Nat := 146956794035097278994917

theorem tailTrace_482958 : CollatzResearch.WordTrace tailWord_482958 prefixEnd_482958 146956794035097278994917 := by
  unfold tailWord_482958
  simp only [CollatzResearch.WordTrace]
  refine ⟨2201865673041640438091191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11743283589555415669819685 2201865673041640438091191)
  ·
    refine ⟨3302798509562460657136787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2201865673041640438091191 3302798509562460657136787)
    ·
      refine ⟨4954197764343690985705181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3302798509562460657136787 4954197764343690985705181)
      ·
        refine ⟨1857824161628884119639443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4954197764343690985705181 1857824161628884119639443)
        ·
          refine ⟨2786736242443326179459165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1857824161628884119639443 2786736242443326179459165)
          ·
            refine ⟨1045026090916247317297187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2786736242443326179459165 1045026090916247317297187)
            ·
              refine ⟨1567539136374370975945781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1045026090916247317297187 1567539136374370975945781)
              ·
                refine ⟨146956794035097278994917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1567539136374370975945781 146956794035097278994917)
                ·
                  rfl

theorem cell19_482958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_482958 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_482958 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_482958 prefixEnd_482958 := by exact prefixLift 482958
  have htrace : WordTrace (prefixWord ++ tailWord_482958) baseStart_482958 baseEnd_482958 := by
    simpa [prefixWord, tailWord_482958, baseEnd_482958] using wordTrace_append hprefix tailTrace_482958
  have hstable : (prefixWord ++ tailWord_482958).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482958).length < 2 ^ (prefixWord ++ tailWord_482958).sum := by decide
  have hdescent : baseEnd_482958 < baseStart_482958 := by decide
  rcases family_descends (prefixWord ++ tailWord_482958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482975 : List Nat := [1, 1, 2, 7, 1, 2, 5]
def baseStart_482975 : Nat := 118140960795 + 482975 * 2 ^ 59
def prefixEnd_482975 : Nat := 4983230072969 + 3 ^ 40 * 482975 * 2
def baseEnd_482975 : Nat := 48987322292415425539031

theorem tailTrace_482975 : CollatzResearch.WordTrace tailWord_482975 prefixEnd_482975 48987322292415425539031 := by
  unfold tailWord_482975
  simp only [CollatzResearch.WordTrace]
  refine ⟨17615545425271535408098379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11743696950181023605398919 17615545425271535408098379)
  ·
    refine ⟨26423318137907303112147569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17615545425271535408098379 26423318137907303112147569)
    ·
      refine ⟨19817488603430477334110677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26423318137907303112147569 19817488603430477334110677)
      ·
        refine ⟨464472389142901812518219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 19817488603430477334110677 464472389142901812518219)
        ·
          refine ⟨696708583714352718777329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 464472389142901812518219 696708583714352718777329)
          ·
            refine ⟨522531437785764539082997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 696708583714352718777329 522531437785764539082997)
            ·
              refine ⟨48987322292415425539031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 522531437785764539082997 48987322292415425539031)
              ·
                rfl

theorem cell19_482975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 5].length) (baseStart_482975 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_482975 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_482975 prefixEnd_482975 := by exact prefixLift 482975
  have htrace : WordTrace (prefixWord ++ tailWord_482975) baseStart_482975 baseEnd_482975 := by
    simpa [prefixWord, tailWord_482975, baseEnd_482975] using wordTrace_append hprefix tailTrace_482975
  have hstable : (prefixWord ++ tailWord_482975).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482975).length < 2 ^ (prefixWord ++ tailWord_482975).sum := by decide
  have hdescent : baseEnd_482975 < baseStart_482975 := by decide
  rcases family_descends (prefixWord ++ tailWord_482975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482977 : List Nat := [1, 2, 3, 3, 2, 3, 5]
def baseStart_482977 : Nat := 118140960795 + 482977 * 2 ^ 59
def prefixEnd_482977 : Nat := 4983230072969 + 3 ^ 40 * 482977 * 2
def baseEnd_482977 : Nat := 48987525148970288190881

theorem tailTrace_482977 : CollatzResearch.WordTrace tailWord_482977 prefixEnd_482977 48987525148970288190881 := by
  unfold tailWord_482977
  simp only [CollatzResearch.WordTrace]
  refine ⟨17615618371264289749671185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11743745580842859833114123 17615618371264289749671185)
  ·
    refine ⟨13211713778448217312253389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17615618371264289749671185 13211713778448217312253389)
    ·
      refine ⟨4954392666918081492095021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13211713778448217312253389 4954392666918081492095021)
      ·
        refine ⟨1857897250094280559535633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4954392666918081492095021 1857897250094280559535633)
        ·
          refine ⟨1393422937570710419651725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1857897250094280559535633 1393422937570710419651725)
          ·
            refine ⟨522533601589016407369397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1393422937570710419651725 522533601589016407369397)
            ·
              refine ⟨48987525148970288190881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 522533601589016407369397 48987525148970288190881)
              ·
                rfl

theorem cell19_482977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 5].length) (baseStart_482977 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_482977 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_482977 prefixEnd_482977 := by exact prefixLift 482977
  have htrace : WordTrace (prefixWord ++ tailWord_482977) baseStart_482977 baseEnd_482977 := by
    simpa [prefixWord, tailWord_482977, baseEnd_482977] using wordTrace_append hprefix tailTrace_482977
  have hstable : (prefixWord ++ tailWord_482977).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482977).length < 2 ^ (prefixWord ++ tailWord_482977).sum := by decide
  have hdescent : baseEnd_482977 < baseStart_482977 := by decide
  rcases family_descends (prefixWord ++ tailWord_482977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483030 : List Nat := [5, 2, 1, 3, 2, 6]
def baseStart_483030 : Nat := 118140960795 + 483030 * 2 ^ 59
def prefixEnd_483030 : Nat := 4983230072969 + 3 ^ 40 * 483030 * 2
def baseEnd_483030 : Nat := 16330966949224716154969

theorem tailTrace_483030 : CollatzResearch.WordTrace tailWord_483030 prefixEnd_483030 16330966949224716154969 := by
  unfold tailWord_483030
  simp only [CollatzResearch.WordTrace]
  refine ⟨1101096965004517487584409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11745034293381519867567029 1101096965004517487584409)
  ·
    refine ⟨825822723753388115688307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1101096965004517487584409 825822723753388115688307)
    ·
      refine ⟨1238734085630082173532461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 825822723753388115688307 1238734085630082173532461)
      ·
        refine ⟨464525282111280815074673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1238734085630082173532461 464525282111280815074673)
        ·
          refine ⟨348393961583460611306005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 464525282111280815074673 348393961583460611306005)
          ·
            refine ⟨16330966949224716154969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 348393961583460611306005 16330966949224716154969)
            ·
              rfl

theorem cell19_483030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 6].length) (baseStart_483030 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_483030 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_483030 prefixEnd_483030 := by exact prefixLift 483030
  have htrace : WordTrace (prefixWord ++ tailWord_483030) baseStart_483030 baseEnd_483030 := by
    simpa [prefixWord, tailWord_483030, baseEnd_483030] using wordTrace_append hprefix tailTrace_483030
  have hstable : (prefixWord ++ tailWord_483030).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483030).length < 2 ^ (prefixWord ++ tailWord_483030).sum := by decide
  have hdescent : baseEnd_483030 < baseStart_483030 := by decide
  rcases family_descends (prefixWord ++ tailWord_483030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483053 : List Nat := [1, 5, 1, 2, 1, 2, 3, 4]
def baseStart_483053 : Nat := 118140960795 + 483053 * 2 ^ 59
def prefixEnd_483053 : Nat := 4983230072969 + 3 ^ 40 * 483053 * 2
def baseEnd_483053 : Nat := 146985701094165206883547

theorem tailTrace_483053 : CollatzResearch.WordTrace tailWord_483053 prefixEnd_483053 146985701094165206883547 := by
  unfold tailWord_483053
  simp only [CollatzResearch.WordTrace]
  refine ⟨17618390318988954729437813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11745593545992636486291875 17618390318988954729437813)
  ·
    refine ⟨1651724092405214505884795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17618390318988954729437813 1651724092405214505884795)
    ·
      refine ⟨2477586138607821758827193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1651724092405214505884795 2477586138607821758827193)
      ·
        refine ⟨1858189603955866319120395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2477586138607821758827193 1858189603955866319120395)
        ·
          refine ⟨2787284405933799478680593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1858189603955866319120395 2787284405933799478680593)
          ·
            refine ⟨2090463304450349609010445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2787284405933799478680593 2090463304450349609010445)
            ·
              refine ⟨783923739168881103378917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2090463304450349609010445 783923739168881103378917)
              ·
                refine ⟨146985701094165206883547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 783923739168881103378917 146985701094165206883547)
                ·
                  rfl

theorem cell19_483053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 4].length) (baseStart_483053 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_483053 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_483053 prefixEnd_483053 := by exact prefixLift 483053
  have htrace : WordTrace (prefixWord ++ tailWord_483053) baseStart_483053 baseEnd_483053 := by
    simpa [prefixWord, tailWord_483053, baseEnd_483053] using wordTrace_append hprefix tailTrace_483053
  have hstable : (prefixWord ++ tailWord_483053).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483053).length < 2 ^ (prefixWord ++ tailWord_483053).sum := by decide
  have hdescent : baseEnd_483053 < baseStart_483053 := by decide
  rcases family_descends (prefixWord ++ tailWord_483053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483085 : List Nat := [1, 7, 2, 1, 1, 1, 6]
def baseStart_483085 : Nat := 118140960795 + 483085 * 2 ^ 59
def prefixEnd_483085 : Nat := 4983230072969 + 3 ^ 40 * 483085 * 2
def baseEnd_483085 : Nat := 48998479402932871390783

theorem tailTrace_483085 : CollatzResearch.WordTrace tailWord_483085 prefixEnd_483085 48998479402932871390783 := by
  unfold tailWord_483085
  simp only [CollatzResearch.WordTrace]
  refine ⟨17619557454873024194602709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11746371636582016129735139 17619557454873024194602709)
  ·
    refine ⟨412958377848586504561001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 17619557454873024194602709 412958377848586504561001)
    ·
      refine ⟨309718783386439878420751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 412958377848586504561001 309718783386439878420751)
      ·
        refine ⟨464578175079659817631127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309718783386439878420751 464578175079659817631127)
        ·
          refine ⟨696867262619489726446691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 464578175079659817631127 696867262619489726446691)
          ·
            refine ⟨1045300893929234589670037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 696867262619489726446691 1045300893929234589670037)
            ·
              refine ⟨48998479402932871390783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1045300893929234589670037 48998479402932871390783)
              ·
                rfl

theorem cell19_483085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 6].length) (baseStart_483085 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_483085 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_483085 prefixEnd_483085 := by exact prefixLift 483085
  have htrace : WordTrace (prefixWord ++ tailWord_483085) baseStart_483085 baseEnd_483085 := by
    simpa [prefixWord, tailWord_483085, baseEnd_483085] using wordTrace_append hprefix tailTrace_483085
  have hstable : (prefixWord ++ tailWord_483085).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483085).length < 2 ^ (prefixWord ++ tailWord_483085).sum := by decide
  have hdescent : baseEnd_483085 < baseStart_483085 := by decide
  rcases family_descends (prefixWord ++ tailWord_483085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483093 : List Nat := [1, 3, 2, 1, 2, 4, 6]
def baseStart_483093 : Nat := 118140960795 + 483093 * 2 ^ 59
def prefixEnd_483093 : Nat := 4983230072969 + 3 ^ 40 * 483093 * 2
def baseEnd_483093 : Nat := 48999290829152321998183

theorem tailTrace_483093 : CollatzResearch.WordTrace tailWord_483093 prefixEnd_483093 48999290829152321998183 := by
  unfold tailWord_483093
  simp only [CollatzResearch.WordTrace]
  refine ⟨17619849238844041560893933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11746566159229361040595955 17619849238844041560893933)
  ·
    refine ⟨6607443464566515585335225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17619849238844041560893933 6607443464566515585335225)
    ·
      refine ⟨4955582598424886689001419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6607443464566515585335225 4955582598424886689001419)
      ·
        refine ⟨7433373897637330033502129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4955582598424886689001419 7433373897637330033502129)
        ·
          refine ⟨5575030423227997525126597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7433373897637330033502129 5575030423227997525126597)
          ·
            refine ⟨1045318204355249535961237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5575030423227997525126597 1045318204355249535961237)
            ·
              refine ⟨48999290829152321998183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1045318204355249535961237 48999290829152321998183)
              ·
                rfl

theorem cell19_483093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 6].length) (baseStart_483093 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_483093 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_483093 prefixEnd_483093 := by exact prefixLift 483093
  have htrace : WordTrace (prefixWord ++ tailWord_483093) baseStart_483093 baseEnd_483093 := by
    simpa [prefixWord, tailWord_483093, baseEnd_483093] using wordTrace_append hprefix tailTrace_483093
  have hstable : (prefixWord ++ tailWord_483093).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483093).length < 2 ^ (prefixWord ++ tailWord_483093).sum := by decide
  have hdescent : baseEnd_483093 < baseStart_483093 := by decide
  rcases family_descends (prefixWord ++ tailWord_483093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483125 : List Nat := [1, 3, 3, 1, 5, 1, 2, 3]
def baseStart_483125 : Nat := 118140960795 + 483125 * 2 ^ 59
def prefixEnd_483125 : Nat := 4983230072969 + 3 ^ 40 * 483125 * 2
def baseEnd_483125 : Nat := 147007609602090373283351

theorem tailTrace_483125 : CollatzResearch.WordTrace tailWord_483125 prefixEnd_483125 147007609602090373283351 := by
  unfold tailWord_483125
  simp only [CollatzResearch.WordTrace]
  refine ⟨17621016374728111026058829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11747344249818740684039219 17621016374728111026058829)
  ·
    refine ⟨6607881140523041634772061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17621016374728111026058829 6607881140523041634772061)
    ·
      refine ⟨2477955427696140613039523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6607881140523041634772061 2477955427696140613039523)
      ·
        refine ⟨3716933141544210919559285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2477955427696140613039523 3716933141544210919559285)
        ·
          refine ⟨348462482019769773708683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3716933141544210919559285 348462482019769773708683)
          ·
            refine ⟨522693723029654660563025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 348462482019769773708683 522693723029654660563025)
            ·
              refine ⟨392020292272240995422269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 522693723029654660563025 392020292272240995422269)
              ·
                refine ⟨147007609602090373283351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 392020292272240995422269 147007609602090373283351)
                ·
                  rfl

theorem cell19_483125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 2, 3].length) (baseStart_483125 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_483125 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_483125 prefixEnd_483125 := by exact prefixLift 483125
  have htrace : WordTrace (prefixWord ++ tailWord_483125) baseStart_483125 baseEnd_483125 := by
    simpa [prefixWord, tailWord_483125, baseEnd_483125] using wordTrace_append hprefix tailTrace_483125
  have hstable : (prefixWord ++ tailWord_483125).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483125).length < 2 ^ (prefixWord ++ tailWord_483125).sum := by decide
  have hdescent : baseEnd_483125 < baseStart_483125 := by decide
  rcases family_descends (prefixWord ++ tailWord_483125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483148 : List Nat := [2, 2, 1, 3, 4, 2, 5]
def baseStart_483148 : Nat := 118140960795 + 483148 * 2 ^ 59
def prefixEnd_483148 : Nat := 4983230072969 + 3 ^ 40 * 483148 * 2
def baseEnd_483148 : Nat := 49004869384411044924059

theorem tailTrace_483148 : CollatzResearch.WordTrace tailWord_483148 prefixEnd_483148 49004869384411044924059 := by
  unfold tailWord_483148
  simp only [CollatzResearch.WordTrace]
  refine ⟨8810927626822392977073049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11747903502429857302764065 8810927626822392977073049)
  ·
    refine ⟨6608195720116794732804787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8810927626822392977073049 6608195720116794732804787)
    ·
      refine ⟨9912293580175192099207181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6608195720116794732804787 9912293580175192099207181)
      ·
        refine ⟨3717110092565697037202693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9912293580175192099207181 3717110092565697037202693)
        ·
          refine ⟨696958142356068194475505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3717110092565697037202693 696958142356068194475505)
          ·
            refine ⟨522718606767051145856629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 696958142356068194475505 522718606767051145856629)
            ·
              refine ⟨49004869384411044924059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 522718606767051145856629 49004869384411044924059)
              ·
                rfl

theorem cell19_483148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 5].length) (baseStart_483148 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_483148 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_483148 prefixEnd_483148 := by exact prefixLift 483148
  have htrace : WordTrace (prefixWord ++ tailWord_483148) baseStart_483148 baseEnd_483148 := by
    simpa [prefixWord, tailWord_483148, baseEnd_483148] using wordTrace_append hprefix tailTrace_483148
  have hstable : (prefixWord ++ tailWord_483148).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483148).length < 2 ^ (prefixWord ++ tailWord_483148).sum := by decide
  have hdescent : baseEnd_483148 < baseStart_483148 := by decide
  rcases family_descends (prefixWord ++ tailWord_483148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483169 : List Nat := [1, 2, 3, 1, 1, 1, 6, 4]
def baseStart_483169 : Nat := 118140960795 + 483169 * 2 ^ 59
def prefixEnd_483169 : Nat := 4983230072969 + 3 ^ 40 * 483169 * 2
def baseEnd_483169 : Nat := 147020998134711308305453

theorem tailTrace_483169 : CollatzResearch.WordTrace tailWord_483169 prefixEnd_483169 147020998134711308305453 := by
  unfold tailWord_483169
  simp only [CollatzResearch.WordTrace]
  refine ⟨17622621186568706540660561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11748414124379137693773707 17622621186568706540660561)
  ·
    refine ⟨13216965889926529905495421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17622621186568706540660561 13216965889926529905495421)
    ·
      refine ⟨4956362208722448714560783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13216965889926529905495421 4956362208722448714560783)
      ·
        refine ⟨7434543313083673071841175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4956362208722448714560783 7434543313083673071841175)
        ·
          refine ⟨11151814969625509607761763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7434543313083673071841175 11151814969625509607761763)
          ·
            refine ⟨16727722454438264411642645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11151814969625509607761763 16727722454438264411642645)
            ·
              refine ⟨784111990051793644295749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16727722454438264411642645 784111990051793644295749)
              ·
                refine ⟨147020998134711308305453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 784111990051793644295749 147020998134711308305453)
                ·
                  rfl

theorem cell19_483169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 4].length) (baseStart_483169 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_483169 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_483169 prefixEnd_483169 := by exact prefixLift 483169
  have htrace : WordTrace (prefixWord ++ tailWord_483169) baseStart_483169 baseEnd_483169 := by
    simpa [prefixWord, tailWord_483169, baseEnd_483169] using wordTrace_append hprefix tailTrace_483169
  have hstable : (prefixWord ++ tailWord_483169).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483169).length < 2 ^ (prefixWord ++ tailWord_483169).sum := by decide
  have hdescent : baseEnd_483169 < baseStart_483169 := by decide
  rcases family_descends (prefixWord ++ tailWord_483169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483207 : List Nat := [1, 1, 4, 2, 4, 7]
def baseStart_483207 : Nat := 118140960795 + 483207 * 2 ^ 59
def prefixEnd_483207 : Nat := 4983230072969 + 3 ^ 40 * 483207 * 2
def baseEnd_483207 : Nat := 16336951217593164384545

theorem tailTrace_483207 : CollatzResearch.WordTrace tailWord_483207 prefixEnd_483207 16336951217593164384545 := by
  unfold tailWord_483207
  simp only [CollatzResearch.WordTrace]
  refine ⟨17624007160431039030543875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11749338106954026020362583 17624007160431039030543875)
  ·
    refine ⟨26436010740646558545815813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17624007160431039030543875 26436010740646558545815813)
    ·
      refine ⟨4956752013871229727340465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26436010740646558545815813 4956752013871229727340465)
      ·
        refine ⟨3717564010403422295505349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4956752013871229727340465 3717564010403422295505349)
        ·
          refine ⟨697043251950641680407253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3717564010403422295505349 697043251950641680407253)
          ·
            refine ⟨16336951217593164384545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 697043251950641680407253 16336951217593164384545)
            ·
              rfl

theorem cell19_483207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 7].length) (baseStart_483207 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_483207 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_483207 prefixEnd_483207 := by exact prefixLift 483207
  have htrace : WordTrace (prefixWord ++ tailWord_483207) baseStart_483207 baseEnd_483207 := by
    simpa [prefixWord, tailWord_483207, baseEnd_483207] using wordTrace_append hprefix tailTrace_483207
  have hstable : (prefixWord ++ tailWord_483207).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483207).length < 2 ^ (prefixWord ++ tailWord_483207).sum := by decide
  have hdescent : baseEnd_483207 < baseStart_483207 := by decide
  rcases family_descends (prefixWord ++ tailWord_483207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483292 : List Nat := [2, 2, 6, 1, 2, 1, 2, 3]
def baseStart_483292 : Nat := 118140960795 + 483292 * 2 ^ 59
def prefixEnd_483292 : Nat := 4983230072969 + 3 ^ 40 * 483292 * 2
def baseEnd_483292 : Nat := 147058425169083467571785

theorem tailTrace_483292 : CollatzResearch.WordTrace tailWord_483292 prefixEnd_483292 147058425169083467571785 := by
  unfold tailWord_483292
  simp only [CollatzResearch.WordTrace]
  refine ⟨8813553682561549273694065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11751404910082065698258753 8813553682561549273694065)
  ·
    refine ⟨6610165261921161955270549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8813553682561549273694065 6610165261921161955270549)
    ·
      refine ⟨309851496652554466653307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 6610165261921161955270549 309851496652554466653307)
      ·
        refine ⟨464777244978831699979961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309851496652554466653307 464777244978831699979961)
        ·
          refine ⟨348582933734123774984971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 464777244978831699979961 348582933734123774984971)
          ·
            refine ⟨522874400601185662477457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 348582933734123774984971 522874400601185662477457)
            ·
              refine ⟨392155800450889246858093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 522874400601185662477457 392155800450889246858093)
              ·
                refine ⟨147058425169083467571785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 392155800450889246858093 147058425169083467571785)
                ·
                  rfl

theorem cell19_483292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 2, 3].length) (baseStart_483292 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_483292 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_483292 prefixEnd_483292 := by exact prefixLift 483292
  have htrace : WordTrace (prefixWord ++ tailWord_483292) baseStart_483292 baseEnd_483292 := by
    simpa [prefixWord, tailWord_483292, baseEnd_483292] using wordTrace_append hprefix tailTrace_483292
  have hstable : (prefixWord ++ tailWord_483292).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483292).length < 2 ^ (prefixWord ++ tailWord_483292).sum := by decide
  have hdescent : baseEnd_483292 < baseStart_483292 := by decide
  rcases family_descends (prefixWord ++ tailWord_483292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483298 : List Nat := [3, 3, 3, 1, 2, 1, 1, 5]
def baseStart_483298 : Nat := 118140960795 + 483298 * 2 ^ 59
def prefixEnd_483298 : Nat := 4983230072969 + 3 ^ 40 * 483298 * 2
def baseEnd_483298 : Nat := 147060250878077231438435

theorem tailTrace_483298 : CollatzResearch.WordTrace tailWord_483298 prefixEnd_483298 147060250878077231438435 := by
  unfold tailWord_483298
  simp only [CollatzResearch.WordTrace]
  refine ⟨4406831550775340393026637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11751550802067574381404365 4406831550775340393026637)
  ·
    refine ⟨1652561831540752647384989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4406831550775340393026637 1652561831540752647384989)
    ·
      refine ⟨619710686827782242769371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1652561831540752647384989 619710686827782242769371)
      ·
        refine ⟨929566030241673364154057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 619710686827782242769371 929566030241673364154057)
        ·
          refine ⟨697174522681255023115543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 929566030241673364154057 697174522681255023115543)
          ·
            refine ⟨1045761784021882534673315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 697174522681255023115543 1045761784021882534673315)
            ·
              refine ⟨1568642676032823802009973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1045761784021882534673315 1568642676032823802009973)
              ·
                refine ⟨147060250878077231438435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1568642676032823802009973 147060250878077231438435)
                ·
                  rfl

theorem cell19_483298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 5].length) (baseStart_483298 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_483298 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_483298 prefixEnd_483298 := by exact prefixLift 483298
  have htrace : WordTrace (prefixWord ++ tailWord_483298) baseStart_483298 baseEnd_483298 := by
    simpa [prefixWord, tailWord_483298, baseEnd_483298] using wordTrace_append hprefix tailTrace_483298
  have hstable : (prefixWord ++ tailWord_483298).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483298).length < 2 ^ (prefixWord ++ tailWord_483298).sum := by decide
  have hdescent : baseEnd_483298 < baseStart_483298 := by decide
  rcases family_descends (prefixWord ++ tailWord_483298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483321 : List Nat := [1, 2, 1, 3, 1, 6, 5]
def baseStart_483321 : Nat := 118140960795 + 483321 * 2 ^ 59
def prefixEnd_483321 : Nat := 4983230072969 + 3 ^ 40 * 483321 * 2
def baseEnd_483321 : Nat := 49022416476406664309087

theorem tailTrace_483321 : CollatzResearch.WordTrace tailWord_483321 prefixEnd_483321 49022416476406664309087 := by
  unfold tailWord_483321
  simp only [CollatzResearch.WordTrace]
  refine ⟨17628165082018036500193817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11752110054678691000129211 17628165082018036500193817)
  ·
    refine ⟨13221123811513527375145363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17628165082018036500193817 13221123811513527375145363)
    ·
      refine ⟨19831685717270291062718045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13221123811513527375145363 19831685717270291062718045)
      ·
        refine ⟨7436882143976359148519267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19831685717270291062718045 7436882143976359148519267)
        ·
          refine ⟨11155323215964538722778901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7436882143976359148519267 11155323215964538722778901)
          ·
            refine ⟨522905775748337752630261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 11155323215964538722778901 522905775748337752630261)
            ·
              refine ⟨49022416476406664309087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 522905775748337752630261 49022416476406664309087)
              ·
                rfl

theorem cell19_483321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 5].length) (baseStart_483321 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_483321 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_483321 prefixEnd_483321 := by exact prefixLift 483321
  have htrace : WordTrace (prefixWord ++ tailWord_483321) baseStart_483321 baseEnd_483321 := by
    simpa [prefixWord, tailWord_483321, baseEnd_483321] using wordTrace_append hprefix tailTrace_483321
  have hstable : (prefixWord ++ tailWord_483321).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483321).length < 2 ^ (prefixWord ++ tailWord_483321).sum := by decide
  have hdescent : baseEnd_483321 < baseStart_483321 := by decide
  rcases family_descends (prefixWord ++ tailWord_483321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483323 : List Nat := [1, 1, 1, 1, 1, 3, 11]
def baseStart_483323 : Nat := 118140960795 + 483323 * 2 ^ 59
def prefixEnd_483323 : Nat := 4983230072969 + 3 ^ 40 * 483323 * 2
def baseEnd_483323 : Nat := 49022619332961526960937

theorem tailTrace_483323 : CollatzResearch.WordTrace tailWord_483323 prefixEnd_483323 49022619332961526960937 := by
  unfold tailWord_483323
  simp only [CollatzResearch.WordTrace]
  refine ⟨17628238028010790841766623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11752158685340527227844415 17628238028010790841766623)
  ·
    refine ⟨26442357042016186262649935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17628238028010790841766623 26442357042016186262649935)
    ·
      refine ⟨39663535563024279393974903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26442357042016186262649935 39663535563024279393974903)
      ·
        refine ⟨59495303344536419090962355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39663535563024279393974903 59495303344536419090962355)
        ·
          refine ⟨89242955016804628636443533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59495303344536419090962355 89242955016804628636443533)
          ·
            refine ⟨33466108131301735738666325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89242955016804628636443533 33466108131301735738666325)
            ·
              refine ⟨49022619332961526960937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 33466108131301735738666325 49022619332961526960937)
              ·
                rfl

theorem cell19_483323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 11].length) (baseStart_483323 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_483323 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_483323 prefixEnd_483323 := by exact prefixLift 483323
  have htrace : WordTrace (prefixWord ++ tailWord_483323) baseStart_483323 baseEnd_483323 := by
    simpa [prefixWord, tailWord_483323, baseEnd_483323] using wordTrace_append hprefix tailTrace_483323
  have hstable : (prefixWord ++ tailWord_483323).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483323).length < 2 ^ (prefixWord ++ tailWord_483323).sum := by decide
  have hdescent : baseEnd_483323 < baseStart_483323 := by decide
  rcases family_descends (prefixWord ++ tailWord_483323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483338 : List Nat := [3, 1, 2, 2, 4, 1, 2, 4]
def baseStart_483338 : Nat := 118140960795 + 483338 * 2 ^ 59
def prefixEnd_483338 : Nat := 4983230072969 + 3 ^ 40 * 483338 * 2
def baseEnd_483338 : Nat := 147072422271368990549437

theorem tailTrace_483338 : CollatzResearch.WordTrace tailWord_483338 prefixEnd_483338 147072422271368990549437 := by
  unfold tailWord_483338
  simp only [CollatzResearch.WordTrace]
  refine ⟨4407196280739112100890667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11752523415304298935708445 4407196280739112100890667)
  ·
    refine ⟨6610794421108668151336001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4407196280739112100890667 6610794421108668151336001)
    ·
      refine ⟨4958095815831501113502001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6610794421108668151336001 4958095815831501113502001)
      ·
        refine ⟨3718571861873625835126501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4958095815831501113502001 3718571861873625835126501)
        ·
          refine ⟨697232224101304844086219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3718571861873625835126501 697232224101304844086219)
          ·
            refine ⟨1045848336151957266129329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 697232224101304844086219 1045848336151957266129329)
            ·
              refine ⟨784386252113967949596997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1045848336151957266129329 784386252113967949596997)
              ·
                refine ⟨147072422271368990549437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 784386252113967949596997 147072422271368990549437)
                ·
                  rfl

theorem cell19_483338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 4].length) (baseStart_483338 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_483338 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_483338 prefixEnd_483338 := by exact prefixLift 483338
  have htrace : WordTrace (prefixWord ++ tailWord_483338) baseStart_483338 baseEnd_483338 := by
    simpa [prefixWord, tailWord_483338, baseEnd_483338] using wordTrace_append hprefix tailTrace_483338
  have hstable : (prefixWord ++ tailWord_483338).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483338).length < 2 ^ (prefixWord ++ tailWord_483338).sum := by decide
  have hdescent : baseEnd_483338 < baseStart_483338 := by decide
  rcases family_descends (prefixWord ++ tailWord_483338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483340 : List Nat := [2, 2, 1, 2, 3, 1, 4, 4]
def baseStart_483340 : Nat := 118140960795 + 483340 * 2 ^ 59
def prefixEnd_483340 : Nat := 4983230072969 + 3 ^ 40 * 483340 * 2
def baseEnd_483340 : Nat := 147073030841033578504987

theorem tailTrace_483340 : CollatzResearch.WordTrace tailWord_483340 prefixEnd_483340 147073030841033578504987 := by
  unfold tailWord_483340
  simp only [CollatzResearch.WordTrace]
  refine ⟨8814429034474601372567737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11752572045966135163423649 8814429034474601372567737)
  ·
    refine ⟨6610821775855951029425803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8814429034474601372567737 6610821775855951029425803)
    ·
      refine ⟨9916232663783926544138705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6610821775855951029425803 9916232663783926544138705)
      ·
        refine ⟨7437174497837944908104029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9916232663783926544138705 7437174497837944908104029)
        ·
          refine ⟨2788940436689229340539011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7437174497837944908104029 2788940436689229340539011)
          ·
            refine ⟨4183410655033844010808517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2788940436689229340539011 4183410655033844010808517)
            ·
              refine ⟨784389497818845752026597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4183410655033844010808517 784389497818845752026597)
              ·
                refine ⟨147073030841033578504987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 784389497818845752026597 147073030841033578504987)
                ·
                  rfl

theorem cell19_483340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 4].length) (baseStart_483340 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_483340 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_483340 prefixEnd_483340 := by exact prefixLift 483340
  have htrace : WordTrace (prefixWord ++ tailWord_483340) baseStart_483340 baseEnd_483340 := by
    simpa [prefixWord, tailWord_483340, baseEnd_483340] using wordTrace_append hprefix tailTrace_483340
  have hstable : (prefixWord ++ tailWord_483340).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483340).length < 2 ^ (prefixWord ++ tailWord_483340).sum := by decide
  have hdescent : baseEnd_483340 < baseStart_483340 := by decide
  rcases family_descends (prefixWord ++ tailWord_483340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483456 : List Nat := [2, 1, 1, 2, 1, 3, 1, 8]
def baseStart_483456 : Nat := 118140960795 + 483456 * 2 ^ 59
def prefixEnd_483456 : Nat := 4983230072969 + 3 ^ 40 * 483456 * 2
def baseEnd_483456 : Nat := 147108327881579679926893

theorem tailTrace_483456 : CollatzResearch.WordTrace tailWord_483456 prefixEnd_483456 147108327881579679926893 := by
  unfold tailWord_483456
  simp only [CollatzResearch.WordTrace]
  refine ⟨8816544468264477278179111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11755392624352636370905481 8816544468264477278179111)
  ·
    refine ⟨13224816702396715917268667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8816544468264477278179111 13224816702396715917268667)
    ·
      refine ⟨19837225053595073875903001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13224816702396715917268667 19837225053595073875903001)
      ·
        refine ⟨14877918790196305406927251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19837225053595073875903001 14877918790196305406927251)
        ·
          refine ⟨22316878185294458110390877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14877918790196305406927251 22316878185294458110390877)
          ·
            refine ⟨8368829319485421791396579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22316878185294458110390877 8368829319485421791396579)
            ·
              refine ⟨12553243979228132687094869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8368829319485421791396579 12553243979228132687094869)
              ·
                refine ⟨147108327881579679926893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12553243979228132687094869 147108327881579679926893)
                ·
                  rfl

theorem cell19_483456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 8].length) (baseStart_483456 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_483456 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_483456 prefixEnd_483456 := by exact prefixLift 483456
  have htrace : WordTrace (prefixWord ++ tailWord_483456) baseStart_483456 baseEnd_483456 := by
    simpa [prefixWord, tailWord_483456, baseEnd_483456] using wordTrace_append hprefix tailTrace_483456
  have hstable : (prefixWord ++ tailWord_483456).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483456).length < 2 ^ (prefixWord ++ tailWord_483456).sum := by decide
  have hdescent : baseEnd_483456 < baseStart_483456 := by decide
  rcases family_descends (prefixWord ++ tailWord_483456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483490 : List Nat := [3, 3, 1, 3, 1, 3, 5]
def baseStart_483490 : Nat := 118140960795 + 483490 * 2 ^ 59
def prefixEnd_483490 : Nat := 4983230072969 + 3 ^ 40 * 483490 * 2
def baseEnd_483490 : Nat := 49039557855292558390415

theorem tailTrace_483490 : CollatzResearch.WordTrace tailWord_483490 prefixEnd_483490 49039557855292558390415 := by
  unfold tailWord_483490
  simp only [CollatzResearch.WordTrace]
  refine ⟨4408582254601444590773981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11756219345603852242063949 4408582254601444590773981)
  ·
    refine ⟨1653218345475541721540243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4408582254601444590773981 1653218345475541721540243)
    ·
      refine ⟨2479827518213312582310365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1653218345475541721540243 2479827518213312582310365)
      ·
        refine ⟨929935319329992218366387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2479827518213312582310365 929935319329992218366387)
        ·
          refine ⟨1394902978994988327549581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 929935319329992218366387 1394902978994988327549581)
          ·
            refine ⟨523088617123120622831093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1394902978994988327549581 523088617123120622831093)
            ·
              refine ⟨49039557855292558390415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 523088617123120622831093 49039557855292558390415)
              ·
                rfl

theorem cell19_483490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 5].length) (baseStart_483490 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_483490 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_483490 prefixEnd_483490 := by exact prefixLift 483490
  have htrace : WordTrace (prefixWord ++ tailWord_483490) baseStart_483490 baseEnd_483490 := by
    simpa [prefixWord, tailWord_483490, baseEnd_483490] using wordTrace_append hprefix tailTrace_483490
  have hstable : (prefixWord ++ tailWord_483490).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483490).length < 2 ^ (prefixWord ++ tailWord_483490).sum := by decide
  have hdescent : baseEnd_483490 < baseStart_483490 := by decide
  rcases family_descends (prefixWord ++ tailWord_483490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483511 : List Nat := [1, 1, 3, 1, 4, 3, 2, 4]
def baseStart_483511 : Nat := 118140960795 + 483511 * 2 ^ 59
def prefixEnd_483511 : Nat := 4983230072969 + 3 ^ 40 * 483511 * 2
def baseEnd_483511 : Nat := 147125063547355848704521

theorem tailTrace_483511 : CollatzResearch.WordTrace tailWord_483511 prefixEnd_483511 147125063547355848704521 := by
  unfold tailWord_483511
  simp only [CollatzResearch.WordTrace]
  refine ⟨17635094951329698949610387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11756729967553132633073591 17635094951329698949610387)
  ·
    refine ⟨26452642426994548424415581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17635094951329698949610387 26452642426994548424415581)
    ·
      refine ⟨9919740910122955659155843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26452642426994548424415581 9919740910122955659155843)
      ·
        refine ⟨14879611365184433488733765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9919740910122955659155843 14879611365184433488733765)
        ·
          refine ⟨2789927130972081279137581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14879611365184433488733765 2789927130972081279137581)
          ·
            refine ⟨1046222674114530479676593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2789927130972081279137581 1046222674114530479676593)
            ·
              refine ⟨784667005585897859757445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1046222674114530479676593 784667005585897859757445)
              ·
                refine ⟨147125063547355848704521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 784667005585897859757445 147125063547355848704521)
                ·
                  rfl

theorem cell19_483511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 4].length) (baseStart_483511 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_483511 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_483511 prefixEnd_483511 := by exact prefixLift 483511
  have htrace : WordTrace (prefixWord ++ tailWord_483511) baseStart_483511 baseEnd_483511 := by
    simpa [prefixWord, tailWord_483511, baseEnd_483511] using wordTrace_append hprefix tailTrace_483511
  have hstable : (prefixWord ++ tailWord_483511).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483511).length < 2 ^ (prefixWord ++ tailWord_483511).sum := by decide
  have hdescent : baseEnd_483511 < baseStart_483511 := by decide
  rcases family_descends (prefixWord ++ tailWord_483511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483549 : List Nat := [1, 4, 3, 2, 1, 8]
def baseStart_483549 : Nat := 118140960795 + 483549 * 2 ^ 59
def prefixEnd_483549 : Nat := 4983230072969 + 3 ^ 40 * 483549 * 2
def baseEnd_483549 : Nat := 16348514041220335539997

theorem tailTrace_483549 : CollatzResearch.WordTrace tailWord_483549 prefixEnd_483549 16348514041220335539997 := by
  unfold tailWord_483549
  simp only [CollatzResearch.WordTrace]
  refine ⟨17636480925192031439493701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11757653950128020959662467 17636480925192031439493701)
  ·
    refine ⟨3306840173473505894905069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17636480925192031439493701 3306840173473505894905069)
    ·
      refine ⟨1240065065052564710589401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3306840173473505894905069 1240065065052564710589401)
      ·
        refine ⟨930048798789423532942051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1240065065052564710589401 930048798789423532942051)
        ·
          refine ⟨1395073198184135299413077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 930048798789423532942051 1395073198184135299413077)
          ·
            refine ⟨16348514041220335539997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1395073198184135299413077 16348514041220335539997)
            ·
              rfl

theorem cell19_483549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 8].length) (baseStart_483549 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_483549 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_483549 prefixEnd_483549 := by exact prefixLift 483549
  have htrace : WordTrace (prefixWord ++ tailWord_483549) baseStart_483549 baseEnd_483549 := by
    simpa [prefixWord, tailWord_483549, baseEnd_483549] using wordTrace_append hprefix tailTrace_483549
  have hstable : (prefixWord ++ tailWord_483549).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483549).length < 2 ^ (prefixWord ++ tailWord_483549).sum := by decide
  have hdescent : baseEnd_483549 < baseStart_483549 := by decide
  rcases family_descends (prefixWord ++ tailWord_483549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483587 : List Nat := [1, 1, 1, 3, 2, 3, 5, 3]
def baseStart_483587 : Nat := 118140960795 + 483587 * 2 ^ 59
def prefixEnd_483587 : Nat := 4983230072969 + 3 ^ 40 * 483587 * 2
def baseEnd_483587 : Nat := 147148189194610191015425

theorem tailTrace_483587 : CollatzResearch.WordTrace tailWord_483587 prefixEnd_483587 147148189194610191015425 := by
  unfold tailWord_483587
  simp only [CollatzResearch.WordTrace]
  refine ⟨17637866899054363929377015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11758577932702909286251343 17637866899054363929377015)
  ·
    refine ⟨26456800348581545894065523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17637866899054363929377015 26456800348581545894065523)
    ·
      refine ⟨39685200522872318841098285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26456800348581545894065523 39685200522872318841098285)
      ·
        refine ⟨14881950196077119565411857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39685200522872318841098285 14881950196077119565411857)
        ·
          refine ⟨11161462647057839674058893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14881950196077119565411857 11161462647057839674058893)
          ·
            refine ⟨4185548492646689877772085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11161462647057839674058893 4185548492646689877772085)
            ·
              refine ⟨392395171185627176041133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4185548492646689877772085 392395171185627176041133)
              ·
                refine ⟨147148189194610191015425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 392395171185627176041133 147148189194610191015425)
                ·
                  rfl

theorem cell19_483587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 5, 3].length) (baseStart_483587 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_483587 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_483587 prefixEnd_483587 := by exact prefixLift 483587
  have htrace : WordTrace (prefixWord ++ tailWord_483587) baseStart_483587 baseEnd_483587 := by
    simpa [prefixWord, tailWord_483587, baseEnd_483587] using wordTrace_append hprefix tailTrace_483587
  have hstable : (prefixWord ++ tailWord_483587).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483587).length < 2 ^ (prefixWord ++ tailWord_483587).sum := by decide
  have hdescent : baseEnd_483587 < baseStart_483587 := by decide
  rcases family_descends (prefixWord ++ tailWord_483587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483608 : List Nat := [2, 1, 2, 3, 1, 2, 8]
def baseStart_483608 : Nat := 118140960795 + 483608 * 2 ^ 59
def prefixEnd_483608 : Nat := 4983230072969 + 3 ^ 40 * 483608 * 2
def baseEnd_483608 : Nat := 49051526392029454849567

theorem tailTrace_483608 : CollatzResearch.WordTrace tailWord_483608 prefixEnd_483608 49051526392029454849567 := by
  unfold tailWord_483608
  simp only [CollatzResearch.WordTrace]
  refine ⟨8819316415989142257945739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11759088554652189677260985 8819316415989142257945739)
  ·
    refine ⟨13228974623983713386918609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8819316415989142257945739 13228974623983713386918609)
    ·
      refine ⟨9921730967987785040188957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13228974623983713386918609 9921730967987785040188957)
      ·
        refine ⟨3720649112995419390070859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9921730967987785040188957 3720649112995419390070859)
        ·
          refine ⟨5580973669493129085106289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3720649112995419390070859 5580973669493129085106289)
          ·
            refine ⟨4185730252119846813829717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5580973669493129085106289 4185730252119846813829717)
            ·
              refine ⟨49051526392029454849567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4185730252119846813829717 49051526392029454849567)
              ·
                rfl

theorem cell19_483608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 8].length) (baseStart_483608 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_483608 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_483608 prefixEnd_483608 := by exact prefixLift 483608
  have htrace : WordTrace (prefixWord ++ tailWord_483608) baseStart_483608 baseEnd_483608 := by
    simpa [prefixWord, tailWord_483608, baseEnd_483608] using wordTrace_append hprefix tailTrace_483608
  have hstable : (prefixWord ++ tailWord_483608).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483608).length < 2 ^ (prefixWord ++ tailWord_483608).sum := by decide
  have hdescent : baseEnd_483608 < baseStart_483608 := by decide
  rcases family_descends (prefixWord ++ tailWord_483608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483642 : List Nat := [3, 1, 1, 1, 4, 4, 2, 3]
def baseStart_483642 : Nat := 118140960795 + 483642 * 2 ^ 59
def prefixEnd_483642 : Nat := 4983230072969 + 3 ^ 40 * 483642 * 2
def baseEnd_483642 : Nat := 147164924860386359793053

theorem tailTrace_483642 : CollatzResearch.WordTrace tailWord_483642 prefixEnd_483642 147164924860386359793053 := by
  unfold tailWord_483642
  simp only [CollatzResearch.WordTrace]
  refine ⟨4409968228463777080657295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11759915275903405548419453 4409968228463777080657295)
  ·
    refine ⟨6614952342695665620985943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4409968228463777080657295 6614952342695665620985943)
    ·
      refine ⟨9922428514043498431478915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6614952342695665620985943 9922428514043498431478915)
      ·
        refine ⟨14883642771065247647218373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9922428514043498431478915 14883642771065247647218373)
        ·
          refine ⟨2790683019574733933853445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14883642771065247647218373 2790683019574733933853445)
          ·
            refine ⟨523253066170262612597521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2790683019574733933853445 523253066170262612597521)
            ·
              refine ⟨392439799627696959448141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 523253066170262612597521 392439799627696959448141)
              ·
                refine ⟨147164924860386359793053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 392439799627696959448141 147164924860386359793053)
                ·
                  rfl

theorem cell19_483642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 2, 3].length) (baseStart_483642 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_483642 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_483642 prefixEnd_483642 := by exact prefixLift 483642
  have htrace : WordTrace (prefixWord ++ tailWord_483642) baseStart_483642 baseEnd_483642 := by
    simpa [prefixWord, tailWord_483642, baseEnd_483642] using wordTrace_append hprefix tailTrace_483642
  have hstable : (prefixWord ++ tailWord_483642).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483642).length < 2 ^ (prefixWord ++ tailWord_483642).sum := by decide
  have hdescent : baseEnd_483642 < baseStart_483642 := by decide
  rcases family_descends (prefixWord ++ tailWord_483642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483665 : List Nat := [1, 2, 2, 1, 4, 2, 7]
def baseStart_483665 : Nat := 118140960795 + 483665 * 2 ^ 59
def prefixEnd_483665 : Nat := 4983230072969 + 3 ^ 40 * 483665 * 2
def baseEnd_483665 : Nat := 49057307803843040427293

theorem tailTrace_483665 : CollatzResearch.WordTrace tailWord_483665 prefixEnd_483665 49057307803843040427293 := by
  unfold tailWord_483665
  simp only [CollatzResearch.WordTrace]
  refine ⟨17640711792771783250716449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11760474528514522167144299 17640711792771783250716449)
  ·
    refine ⟨13230533844578837438037337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17640711792771783250716449 13230533844578837438037337)
    ·
      refine ⟨9922900383434128078528003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13230533844578837438037337 9922900383434128078528003)
      ·
        refine ⟨14884350575151192117792005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9922900383434128078528003 14884350575151192117792005)
        ·
          refine ⟨2790815732840848522086001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14884350575151192117792005 2790815732840848522086001)
          ·
            refine ⟨2093111799630636391564501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2790815732840848522086001 2093111799630636391564501)
            ·
              refine ⟨49057307803843040427293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2093111799630636391564501 49057307803843040427293)
              ·
                rfl

theorem cell19_483665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 7].length) (baseStart_483665 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_483665 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_483665 prefixEnd_483665 := by exact prefixLift 483665
  have htrace : WordTrace (prefixWord ++ tailWord_483665) baseStart_483665 baseEnd_483665 := by
    simpa [prefixWord, tailWord_483665, baseEnd_483665] using wordTrace_append hprefix tailTrace_483665
  have hstable : (prefixWord ++ tailWord_483665).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483665).length < 2 ^ (prefixWord ++ tailWord_483665).sum := by decide
  have hdescent : baseEnd_483665 < baseStart_483665 := by decide
  rcases family_descends (prefixWord ++ tailWord_483665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483682 : List Nat := [3, 3, 2, 1, 1, 2, 1, 6]
def baseStart_483682 : Nat := 118140960795 + 483682 * 2 ^ 59
def prefixEnd_483682 : Nat := 4983230072969 + 3 ^ 40 * 483682 * 2
def baseEnd_483682 : Nat := 147177096253678118904055

theorem tailTrace_483682 : CollatzResearch.WordTrace tailWord_483682 prefixEnd_483682 147177096253678118904055 := by
  unfold tailWord_483682
  simp only [CollatzResearch.WordTrace]
  refine ⟨4410332958427548788521325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11760887889140130102723533 4410332958427548788521325)
  ·
    refine ⟨1653874859410330795695497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4410332958427548788521325 1653874859410330795695497)
    ·
      refine ⟨1240406144557748096771623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1653874859410330795695497 1240406144557748096771623)
      ·
        refine ⟨1860609216836622145157435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1240406144557748096771623 1860609216836622145157435)
        ·
          refine ⟨2790913825254933217736153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1860609216836622145157435 2790913825254933217736153)
          ·
            refine ⟨2093185368941199913302115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2790913825254933217736153 2093185368941199913302115)
            ·
              refine ⟨3139778053411799869953173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2093185368941199913302115 3139778053411799869953173)
              ·
                refine ⟨147177096253678118904055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3139778053411799869953173 147177096253678118904055)
                ·
                  rfl

theorem cell19_483682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 6].length) (baseStart_483682 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_483682 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_483682 prefixEnd_483682 := by exact prefixLift 483682
  have htrace : WordTrace (prefixWord ++ tailWord_483682) baseStart_483682 baseEnd_483682 := by
    simpa [prefixWord, tailWord_483682, baseEnd_483682] using wordTrace_append hprefix tailTrace_483682
  have hstable : (prefixWord ++ tailWord_483682).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483682).length < 2 ^ (prefixWord ++ tailWord_483682).sum := by decide
  have hdescent : baseEnd_483682 < baseStart_483682 := by decide
  rcases family_descends (prefixWord ++ tailWord_483682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483701 : List Nat := [1, 3, 4, 1, 2, 1, 2, 5]
def baseStart_483701 : Nat := 118140960795 + 483701 * 2 ^ 59
def prefixEnd_483701 : Nat := 4983230072969 + 3 ^ 40 * 483701 * 2
def baseEnd_483701 : Nat := 147182877665491704481781

theorem tailTrace_483701 : CollatzResearch.WordTrace tailWord_483701 prefixEnd_483701 147182877665491704481781 := by
  unfold tailWord_483701
  simp only [CollatzResearch.WordTrace]
  refine ⟨17642024820641361399026957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11761349880427574266017971 17642024820641361399026957)
  ·
    refine ⟨6615759307740510524635109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17642024820641361399026957 6615759307740510524635109)
    ·
      refine ⟨1240454870201345723369083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6615759307740510524635109 1240454870201345723369083)
      ·
        refine ⟨1860682305302018585053625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1240454870201345723369083 1860682305302018585053625)
        ·
          refine ⟨1395511728976513938790219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1860682305302018585053625 1395511728976513938790219)
          ·
            refine ⟨2093267593464770908185329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1395511728976513938790219 2093267593464770908185329)
            ·
              refine ⟨1569950695098578181138997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2093267593464770908185329 1569950695098578181138997)
              ·
                refine ⟨147182877665491704481781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1569950695098578181138997 147182877665491704481781)
                ·
                  rfl

theorem cell19_483701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 5].length) (baseStart_483701 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_483701 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_483701 prefixEnd_483701 := by exact prefixLift 483701
  have htrace : WordTrace (prefixWord ++ tailWord_483701) baseStart_483701 baseEnd_483701 := by
    simpa [prefixWord, tailWord_483701, baseEnd_483701] using wordTrace_append hprefix tailTrace_483701
  have hstable : (prefixWord ++ tailWord_483701).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483701).length < 2 ^ (prefixWord ++ tailWord_483701).sum := by decide
  have hdescent : baseEnd_483701 < baseStart_483701 := by decide
  rcases family_descends (prefixWord ++ tailWord_483701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483811 : List Nat := [1, 1, 1, 6, 4, 1, 2, 3]
def baseStart_483811 : Nat := 118140960795 + 483811 * 2 ^ 59
def prefixEnd_483811 : Nat := 4983230072969 + 3 ^ 40 * 483811 * 2
def baseEnd_483811 : Nat := 147216348997044042037037

theorem tailTrace_483811 : CollatzResearch.WordTrace tailWord_483811 prefixEnd_483811 147216348997044042037037 := by
  unfold tailWord_483811
  simp only [CollatzResearch.WordTrace]
  refine ⟨17646036850242850185531287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11764024566828566790354191 17646036850242850185531287)
  ·
    refine ⟨26469055275364275278296931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17646036850242850185531287 26469055275364275278296931)
    ·
      refine ⟨39703582913046412917445397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26469055275364275278296931 39703582913046412917445397)
      ·
        refine ⟨1861105449049050605505253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 39703582913046412917445397 1861105449049050605505253)
        ·
          refine ⟨348957271696696988532235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1861105449049050605505253 348957271696696988532235)
          ·
            refine ⟨523435907545045482798353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 348957271696696988532235 523435907545045482798353)
            ·
              refine ⟨392576930658784112098765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 523435907545045482798353 392576930658784112098765)
              ·
                refine ⟨147216348997044042037037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 392576930658784112098765 147216348997044042037037)
                ·
                  rfl

theorem cell19_483811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 2, 3].length) (baseStart_483811 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_483811 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_483811 prefixEnd_483811 := by exact prefixLift 483811
  have htrace : WordTrace (prefixWord ++ tailWord_483811) baseStart_483811 baseEnd_483811 := by
    simpa [prefixWord, tailWord_483811, baseEnd_483811] using wordTrace_append hprefix tailTrace_483811
  have hstable : (prefixWord ++ tailWord_483811).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483811).length < 2 ^ (prefixWord ++ tailWord_483811).sum := by decide
  have hdescent : baseEnd_483811 < baseStart_483811 := by decide
  rcases family_descends (prefixWord ++ tailWord_483811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483969 : List Nat := [1, 2, 4, 2, 1, 1, 2, 6]
def baseStart_483969 : Nat := 118140960795 + 483969 * 2 ^ 59
def prefixEnd_483969 : Nat := 4983230072969 + 3 ^ 40 * 483969 * 2
def baseEnd_483969 : Nat := 147264426000546490525495

theorem tailTrace_483969 : CollatzResearch.WordTrace tailWord_483969 prefixEnd_483969 147264426000546490525495 := by
  unfold tailWord_483969
  simp only [CollatzResearch.WordTrace]
  refine ⟨17651799583670443169782961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11767866389113628779855307 17651799583670443169782961)
  ·
    refine ⟨13238849687752832377337221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17651799583670443169782961 13238849687752832377337221)
    ·
      refine ⟨2482284316453656070750729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13238849687752832377337221 2482284316453656070750729)
      ·
        refine ⟨1861713237340242053063047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2482284316453656070750729 1861713237340242053063047)
        ·
          refine ⟨2792569856010363079594571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1861713237340242053063047 2792569856010363079594571)
          ·
            refine ⟨4188854784015544619391857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2792569856010363079594571 4188854784015544619391857)
            ·
              refine ⟨3141641088011658464543893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4188854784015544619391857 3141641088011658464543893)
              ·
                refine ⟨147264426000546490525495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3141641088011658464543893 147264426000546490525495)
                ·
                  rfl

theorem cell19_483969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 6].length) (baseStart_483969 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_483969 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_483969 prefixEnd_483969 := by exact prefixLift 483969
  have htrace : WordTrace (prefixWord ++ tailWord_483969) baseStart_483969 baseEnd_483969 := by
    simpa [prefixWord, tailWord_483969, baseEnd_483969] using wordTrace_append hprefix tailTrace_483969
  have hstable : (prefixWord ++ tailWord_483969).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483969).length < 2 ^ (prefixWord ++ tailWord_483969).sum := by decide
  have hdescent : baseEnd_483969 < baseStart_483969 := by decide
  rcases family_descends (prefixWord ++ tailWord_483969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483986 : List Nat := [3, 2, 3, 1, 2, 2, 1, 5]
def baseStart_483986 : Nat := 118140960795 + 483986 * 2 ^ 59
def prefixEnd_483986 : Nat := 4983230072969 + 3 ^ 40 * 483986 * 2
def baseEnd_483986 : Nat := 147269598842695488147671

theorem tailTrace_483986 : CollatzResearch.WordTrace tailWord_483986 prefixEnd_483986 147269598842695488147671 := by
  unfold tailWord_483986
  simp only [CollatzResearch.WordTrace]
  refine ⟨4413104906152213768287953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11768279749739236715434541 4413104906152213768287953)
  ·
    refine ⟨3309828679614160326215965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4413104906152213768287953 3309828679614160326215965)
    ·
      refine ⟨1241185754855310122330987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3309828679614160326215965 1241185754855310122330987)
      ·
        refine ⟨1861778632282965183496481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1241185754855310122330987 1861778632282965183496481)
        ·
          refine ⟨1396333974212223887622361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1861778632282965183496481 1396333974212223887622361)
          ·
            refine ⟨1047250480659167915716771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1396333974212223887622361 1047250480659167915716771)
            ·
              refine ⟨1570875720988751873575157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1047250480659167915716771 1570875720988751873575157)
              ·
                refine ⟨147269598842695488147671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1570875720988751873575157 147269598842695488147671)
                ·
                  rfl

theorem cell19_483986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 5].length) (baseStart_483986 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_483986 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_483986 prefixEnd_483986 := by exact prefixLift 483986
  have htrace : WordTrace (prefixWord ++ tailWord_483986) baseStart_483986 baseEnd_483986 := by
    simpa [prefixWord, tailWord_483986, baseEnd_483986] using wordTrace_append hprefix tailTrace_483986
  have hstable : (prefixWord ++ tailWord_483986).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483986).length < 2 ^ (prefixWord ++ tailWord_483986).sum := by decide
  have hdescent : baseEnd_483986 < baseStart_483986 := by decide
  rcases family_descends (prefixWord ++ tailWord_483986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484026 : List Nat := [3, 1, 1, 1, 2, 3, 4, 4]
def baseStart_484026 : Nat := 118140960795 + 484026 * 2 ^ 59
def prefixEnd_484026 : Nat := 4983230072969 + 3 ^ 40 * 484026 * 2
def baseEnd_484026 : Nat := 147281770235987247258673

theorem tailTrace_484026 : CollatzResearch.WordTrace tailWord_484026 prefixEnd_484026 147281770235987247258673 := by
  unfold tailWord_484026
  simp only [CollatzResearch.WordTrace]
  refine ⟨4413469636115985476151983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11769252362975961269738621 4413469636115985476151983)
  ·
    refine ⟨6620204454173978214227975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4413469636115985476151983 6620204454173978214227975)
    ·
      refine ⟨9930306681260967321341963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6620204454173978214227975 9930306681260967321341963)
      ·
        refine ⟨14895460021891450982012945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9930306681260967321341963 14895460021891450982012945)
        ·
          refine ⟨11171595016418588236509709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14895460021891450982012945 11171595016418588236509709)
          ·
            refine ⟨4189348131156970588691141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11171595016418588236509709 4189348131156970588691141)
            ·
              refine ⟨785502774591931985379589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4189348131156970588691141 785502774591931985379589)
              ·
                refine ⟨147281770235987247258673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 785502774591931985379589 147281770235987247258673)
                ·
                  rfl

theorem cell19_484026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 4].length) (baseStart_484026 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_484026 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_484026 prefixEnd_484026 := by exact prefixLift 484026
  have htrace : WordTrace (prefixWord ++ tailWord_484026) baseStart_484026 baseEnd_484026 := by
    simpa [prefixWord, tailWord_484026, baseEnd_484026] using wordTrace_append hprefix tailTrace_484026
  have hstable : (prefixWord ++ tailWord_484026).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484026).length < 2 ^ (prefixWord ++ tailWord_484026).sum := by decide
  have hdescent : baseEnd_484026 < baseStart_484026 := by decide
  rcases family_descends (prefixWord ++ tailWord_484026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484098 : List Nat := [3, 4, 1, 1, 1, 3, 3, 3]
def baseStart_484098 : Nat := 118140960795 + 484098 * 2 ^ 59
def prefixEnd_484098 : Nat := 4983230072969 + 3 ^ 40 * 484098 * 2
def baseEnd_484098 : Nat := 147303678743912413658477

theorem tailTrace_484098 : CollatzResearch.WordTrace tailWord_484098 prefixEnd_484098 147303678743912413658477 := by
  unfold tailWord_484098
  simp only [CollatzResearch.WordTrace]
  refine ⟨4414126150050774550307237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11771003066802065467485965 4414126150050774550307237)
  ·
    refine ⟨827648653134520228182607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4414126150050774550307237 827648653134520228182607)
    ·
      refine ⟨1241472979701780342273911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 827648653134520228182607 1241472979701780342273911)
      ·
        refine ⟨1862209469552670513410867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1241472979701780342273911 1862209469552670513410867)
        ·
          refine ⟨2793314204329005770116301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1862209469552670513410867 2793314204329005770116301)
          ·
            refine ⟨1047492826623377163793613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2793314204329005770116301 1047492826623377163793613)
            ·
              refine ⟨392809809983766436422605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1047492826623377163793613 392809809983766436422605)
              ·
                refine ⟨147303678743912413658477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 392809809983766436422605 147303678743912413658477)
                ·
                  rfl

theorem cell19_484098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 3, 3].length) (baseStart_484098 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_484098 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_484098 prefixEnd_484098 := by exact prefixLift 484098
  have htrace : WordTrace (prefixWord ++ tailWord_484098) baseStart_484098 baseEnd_484098 := by
    simpa [prefixWord, tailWord_484098, baseEnd_484098] using wordTrace_append hprefix tailTrace_484098
  have hstable : (prefixWord ++ tailWord_484098).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484098).length < 2 ^ (prefixWord ++ tailWord_484098).sum := by decide
  have hdescent : baseEnd_484098 < baseStart_484098 := by decide
  rcases family_descends (prefixWord ++ tailWord_484098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484100 : List Nat := [2, 3, 2, 2, 1, 1, 5, 3]
def baseStart_484100 : Nat := 118140960795 + 484100 * 2 ^ 59
def prefixEnd_484100 : Nat := 4983230072969 + 3 ^ 40 * 484100 * 2
def baseEnd_484100 : Nat := 147304287313577001614027

theorem tailTrace_484100 : CollatzResearch.WordTrace tailWord_484100 prefixEnd_484100 147304287313577001614027 := by
  unfold tailWord_484100
  simp only [CollatzResearch.WordTrace]
  refine ⟨8828288773097926271400877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11771051697463901695201169 8828288773097926271400877)
  ·
    refine ⟨3310608289911722351775329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8828288773097926271400877 3310608289911722351775329)
    ·
      refine ⟨2482956217433791763831497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3310608289911722351775329 2482956217433791763831497)
      ·
        refine ⟨1862217163075343822873623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2482956217433791763831497 1862217163075343822873623)
        ·
          refine ⟨2793325744613015734310435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1862217163075343822873623 2793325744613015734310435)
          ·
            refine ⟨4189988616919523601465653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2793325744613015734310435 4189988616919523601465653)
            ·
              refine ⟨392811432836205337637405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4189988616919523601465653 392811432836205337637405)
              ·
                refine ⟨147304287313577001614027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 392811432836205337637405 147304287313577001614027)
                ·
                  rfl

theorem cell19_484100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 5, 3].length) (baseStart_484100 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_484100 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_484100 prefixEnd_484100 := by exact prefixLift 484100
  have htrace : WordTrace (prefixWord ++ tailWord_484100) baseStart_484100 baseEnd_484100 := by
    simpa [prefixWord, tailWord_484100, baseEnd_484100] using wordTrace_append hprefix tailTrace_484100
  have hstable : (prefixWord ++ tailWord_484100).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484100).length < 2 ^ (prefixWord ++ tailWord_484100).sum := by decide
  have hdescent : baseEnd_484100 < baseStart_484100 := by decide
  rcases family_descends (prefixWord ++ tailWord_484100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484157 : List Nat := [1, 4, 1, 4, 2, 1, 1, 5]
def baseStart_484157 : Nat := 118140960795 + 484157 * 2 ^ 59
def prefixEnd_484157 : Nat := 4983230072969 + 3 ^ 40 * 484157 * 2
def baseEnd_484157 : Nat := 147321631549017758347205

theorem tailTrace_484157 : CollatzResearch.WordTrace tailWord_484157 prefixEnd_484157 147321631549017758347205 := by
  unfold tailWord_484157
  simp only [CollatzResearch.WordTrace]
  refine ⟨17658656506989351277626725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11772437671326234185084483 17658656506989351277626725)
  ·
    refine ⟨3310998095060503364555011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17658656506989351277626725 3310998095060503364555011)
    ·
      refine ⟨4966497142590755046832517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3310998095060503364555011 4966497142590755046832517)
      ·
        refine ⟨931218214235766571281097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4966497142590755046832517 931218214235766571281097)
        ·
          refine ⟨698413660676824928460823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 931218214235766571281097 698413660676824928460823)
          ·
            refine ⟨1047620491015237392691235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 698413660676824928460823 1047620491015237392691235)
            ·
              refine ⟨1571430736522856089036853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1047620491015237392691235 1571430736522856089036853)
              ·
                refine ⟨147321631549017758347205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1571430736522856089036853 147321631549017758347205)
                ·
                  rfl

theorem cell19_484157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 5].length) (baseStart_484157 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_484157 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_484157 prefixEnd_484157 := by exact prefixLift 484157
  have htrace : WordTrace (prefixWord ++ tailWord_484157) baseStart_484157 baseEnd_484157 := by
    simpa [prefixWord, tailWord_484157, baseEnd_484157] using wordTrace_append hprefix tailTrace_484157
  have hstable : (prefixWord ++ tailWord_484157).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484157).length < 2 ^ (prefixWord ++ tailWord_484157).sum := by decide
  have hdescent : baseEnd_484157 < baseStart_484157 := by decide
  rcases family_descends (prefixWord ++ tailWord_484157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484159 : List Nat := [1, 1, 2, 2, 5, 2, 1, 5]
def baseStart_484159 : Nat := 118140960795 + 484159 * 2 ^ 59
def prefixEnd_484159 : Nat := 4983230072969 + 3 ^ 40 * 484159 * 2
def baseEnd_484159 : Nat := 147322240118682346302755

theorem tailTrace_484159 : CollatzResearch.WordTrace tailWord_484159 prefixEnd_484159 147322240118682346302755 := by
  unfold tailWord_484159
  simp only [CollatzResearch.WordTrace]
  refine ⟨17658729452982105619199531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11772486301988070412799687 17658729452982105619199531)
  ·
    refine ⟨26488094179473158428799297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17658729452982105619199531 26488094179473158428799297)
    ·
      refine ⟨19866070634604868821599473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26488094179473158428799297 19866070634604868821599473)
      ·
        refine ⟨14899552975953651616199605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19866070634604868821599473 14899552975953651616199605)
        ·
          refine ⟨1396833091495654839018713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14899552975953651616199605 1396833091495654839018713)
          ·
            refine ⟨1047624818621741129264035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1396833091495654839018713 1047624818621741129264035)
            ·
              refine ⟨1571437227932611693896053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1047624818621741129264035 1571437227932611693896053)
              ·
                refine ⟨147322240118682346302755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1571437227932611693896053 147322240118682346302755)
                ·
                  rfl

theorem cell19_484159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 5].length) (baseStart_484159 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_484159 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_484159 prefixEnd_484159 := by exact prefixLift 484159
  have htrace : WordTrace (prefixWord ++ tailWord_484159) baseStart_484159 baseEnd_484159 := by
    simpa [prefixWord, tailWord_484159, baseEnd_484159] using wordTrace_append hprefix tailTrace_484159
  have hstable : (prefixWord ++ tailWord_484159).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484159).length < 2 ^ (prefixWord ++ tailWord_484159).sum := by decide
  have hdescent : baseEnd_484159 < baseStart_484159 := by decide
  rcases family_descends (prefixWord ++ tailWord_484159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484214 : List Nat := [5, 1, 1, 3, 1, 1, 2, 5]
def baseStart_484214 : Nat := 118140960795 + 484214 * 2 ^ 59
def prefixEnd_484214 : Nat := 4983230072969 + 3 ^ 40 * 484214 * 2
def baseEnd_484214 : Nat := 147338975784458515080383

theorem tailTrace_484214 : CollatzResearch.WordTrace tailWord_484214 prefixEnd_484214 147338975784458515080383 := by
  unfold tailWord_484214
  simp only [CollatzResearch.WordTrace]
  refine ⟨1103795966736428125778231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11773823645188566674967797 1103795966736428125778231)
  ·
    refine ⟨1655693950104642188667347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1103795966736428125778231 1655693950104642188667347)
    ·
      refine ⟨2483540925156963283001021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1655693950104642188667347 2483540925156963283001021)
      ·
        refine ⟨931327846933861231125383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2483540925156963283001021 931327846933861231125383)
        ·
          refine ⟨1396991770400791846688075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 931327846933861231125383 1396991770400791846688075)
          ·
            refine ⟨2095487655601187770032113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1396991770400791846688075 2095487655601187770032113)
            ·
              refine ⟨1571615741700890827524085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2095487655601187770032113 1571615741700890827524085)
              ·
                refine ⟨147338975784458515080383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1571615741700890827524085 147338975784458515080383)
                ·
                  rfl

theorem cell19_484214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_484214 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_484214 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_484214 prefixEnd_484214 := by exact prefixLift 484214
  have htrace : WordTrace (prefixWord ++ tailWord_484214) baseStart_484214 baseEnd_484214 := by
    simpa [prefixWord, tailWord_484214, baseEnd_484214] using wordTrace_append hprefix tailTrace_484214
  have hstable : (prefixWord ++ tailWord_484214).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484214).length < 2 ^ (prefixWord ++ tailWord_484214).sum := by decide
  have hdescent : baseEnd_484214 < baseStart_484214 := by decide
  rcases family_descends (prefixWord ++ tailWord_484214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484250 : List Nat := [3, 1, 1, 4, 4, 1, 1, 4]
def baseStart_484250 : Nat := 118140960795 + 484250 * 2 ^ 59
def prefixEnd_484250 : Nat := 4983230072969 + 3 ^ 40 * 484250 * 2
def baseEnd_484250 : Nat := 147349930038421098280285

theorem tailTrace_484250 : CollatzResearch.WordTrace tailWord_484250 prefixEnd_484250 147349930038421098280285 := by
  unfold tailWord_484250
  simp only [CollatzResearch.WordTrace]
  refine ⟨4415512123913107040190551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11774698997101618773841469 4415512123913107040190551)
  ·
    refine ⟨6623268185869660560285827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4415512123913107040190551 6623268185869660560285827)
    ·
      refine ⟨9934902278804490840428741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6623268185869660560285827 9934902278804490840428741)
      ·
        refine ⟨1862794177275842032580389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9934902278804490840428741 1862794177275842032580389)
        ·
          refine ⟨349273908239220381108823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1862794177275842032580389 349273908239220381108823)
          ·
            refine ⟨523910862358830571663235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 349273908239220381108823 523910862358830571663235)
            ·
              refine ⟨785866293538245857494853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 523910862358830571663235 785866293538245857494853)
              ·
                refine ⟨147349930038421098280285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 785866293538245857494853 147349930038421098280285)
                ·
                  rfl

theorem cell19_484250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 4].length) (baseStart_484250 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_484250 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_484250 prefixEnd_484250 := by exact prefixLift 484250
  have htrace : WordTrace (prefixWord ++ tailWord_484250) baseStart_484250 baseEnd_484250 := by
    simpa [prefixWord, tailWord_484250, baseEnd_484250] using wordTrace_append hprefix tailTrace_484250
  have hstable : (prefixWord ++ tailWord_484250).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484250).length < 2 ^ (prefixWord ++ tailWord_484250).sum := by decide
  have hdescent : baseEnd_484250 < baseStart_484250 := by decide
  rcases family_descends (prefixWord ++ tailWord_484250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484330 : List Nat := [3, 1, 3, 1, 2, 3, 1, 5]
def baseStart_484330 : Nat := 118140960795 + 484330 * 2 ^ 59
def prefixEnd_484330 : Nat := 4983230072969 + 3 ^ 40 * 484330 * 2
def baseEnd_484330 : Nat := 147374272825004616502289

theorem tailTrace_484330 : CollatzResearch.WordTrace tailWord_484330 prefixEnd_484330 147374272825004616502289 := by
  unfold tailWord_484330
  simp only [CollatzResearch.WordTrace]
  refine ⟨4416241583840650455918611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11776644223575067882449629 4416241583840650455918611)
  ·
    refine ⟨6624362375760975683877917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4416241583840650455918611 6624362375760975683877917)
    ·
      refine ⟨2484135890910365881454219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6624362375760975683877917 2484135890910365881454219)
      ·
        refine ⟨3726203836365548822181329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2484135890910365881454219 3726203836365548822181329)
        ·
          refine ⟨2794652877274161616635997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3726203836365548822181329 2794652877274161616635997)
          ·
            refine ⟨1047994828977810606238499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2794652877274161616635997 1047994828977810606238499)
            ·
              refine ⟨1571992243466715909357749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1047994828977810606238499 1571992243466715909357749)
              ·
                refine ⟨147374272825004616502289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1571992243466715909357749 147374272825004616502289)
                ·
                  rfl

theorem cell19_484330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 5].length) (baseStart_484330 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_484330 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_484330 prefixEnd_484330 := by exact prefixLift 484330
  have htrace : WordTrace (prefixWord ++ tailWord_484330) baseStart_484330 baseEnd_484330 := by
    simpa [prefixWord, tailWord_484330, baseEnd_484330] using wordTrace_append hprefix tailTrace_484330
  have hstable : (prefixWord ++ tailWord_484330).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484330).length < 2 ^ (prefixWord ++ tailWord_484330).sum := by decide
  have hdescent : baseEnd_484330 < baseStart_484330 := by decide
  rcases family_descends (prefixWord ++ tailWord_484330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484389 : List Nat := [1, 3, 1, 2, 2, 2, 1, 7]
def baseStart_484389 : Nat := 118140960795 + 484389 * 2 ^ 59
def prefixEnd_484389 : Nat := 4983230072969 + 3 ^ 40 * 484389 * 2
def baseEnd_484389 : Nat := 147392225630109961191017

theorem tailTrace_484389 : CollatzResearch.WordTrace tailWord_484389 prefixEnd_484389 147392225630109961191017 := by
  unfold tailWord_484389
  simp only [CollatzResearch.WordTrace]
  refine ⟨17667118242148854900072221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11778078828099236600048147 17667118242148854900072221)
  ·
    refine ⟨6625169340805820587527083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17667118242148854900072221 6625169340805820587527083)
    ·
      refine ⟨9937754011208730881290625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6625169340805820587527083 9937754011208730881290625)
      ·
        refine ⟨7453315508406548160967969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9937754011208730881290625 7453315508406548160967969)
        ·
          refine ⟨5589986631304911120725977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7453315508406548160967969 5589986631304911120725977)
          ·
            refine ⟨4192489973478683340544483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5589986631304911120725977 4192489973478683340544483)
            ·
              refine ⟨6288734960218025010816725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4192489973478683340544483 6288734960218025010816725)
              ·
                refine ⟨147392225630109961191017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6288734960218025010816725 147392225630109961191017)
                ·
                  rfl

theorem cell19_484389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 7].length) (baseStart_484389 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_484389 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_484389 prefixEnd_484389 := by exact prefixLift 484389
  have htrace : WordTrace (prefixWord ++ tailWord_484389) baseStart_484389 baseEnd_484389 := by
    simpa [prefixWord, tailWord_484389, baseEnd_484389] using wordTrace_append hprefix tailTrace_484389
  have hstable : (prefixWord ++ tailWord_484389).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484389).length < 2 ^ (prefixWord ++ tailWord_484389).sum := by decide
  have hdescent : baseEnd_484389 < baseStart_484389 := by decide
  rcases family_descends (prefixWord ++ tailWord_484389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484406 : List Nat := [5, 1, 2, 1, 1, 9]
def baseStart_484406 : Nat := 118140960795 + 484406 * 2 ^ 59
def prefixEnd_484406 : Nat := 4983230072969 + 3 ^ 40 * 484406 * 2
def baseEnd_484406 : Nat := 16377488719139884312577

theorem tailTrace_484406 : CollatzResearch.WordTrace tailWord_484406 prefixEnd_484406 16377488719139884312577 := by
  unfold tailWord_484406
  simp only [CollatzResearch.WordTrace]
  refine ⟨1104233642692954175215067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11778492188724844535627381 1104233642692954175215067)
  ·
    refine ⟨1656350464039431262822601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1104233642692954175215067 1656350464039431262822601)
    ·
      refine ⟨1242262848029573447116951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1656350464039431262822601 1242262848029573447116951)
      ·
        refine ⟨1863394272044360170675427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1242262848029573447116951 1863394272044360170675427)
        ·
          refine ⟨2795091408066540256013141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1863394272044360170675427 2795091408066540256013141)
          ·
            refine ⟨16377488719139884312577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2795091408066540256013141 16377488719139884312577)
            ·
              rfl

theorem cell19_484406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 9].length) (baseStart_484406 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_484406 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_484406 prefixEnd_484406 := by exact prefixLift 484406
  have htrace : WordTrace (prefixWord ++ tailWord_484406) baseStart_484406 baseEnd_484406 := by
    simpa [prefixWord, tailWord_484406, baseEnd_484406] using wordTrace_append hprefix tailTrace_484406
  have hstable : (prefixWord ++ tailWord_484406).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484406).length < 2 ^ (prefixWord ++ tailWord_484406).sum := by decide
  have hdescent : baseEnd_484406 < baseStart_484406 := by decide
  rcases family_descends (prefixWord ++ tailWord_484406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484408 : List Nat := [2, 1, 2, 1, 5, 8]
def baseStart_484408 : Nat := 118140960795 + 484408 * 2 ^ 59
def prefixEnd_484408 : Nat := 4983230072969 + 3 ^ 40 * 484408 * 2
def baseEnd_484408 : Nat := 16377556337991505196527

theorem tailTrace_484408 : CollatzResearch.WordTrace tailWord_484408 prefixEnd_484408 16377556337991505196527 := by
  unfold tailWord_484408
  simp only [CollatzResearch.WordTrace]
  refine ⟨8833905614540010572506939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11778540819386680763342585 8833905614540010572506939)
  ·
    refine ⟨13250858421810015858760409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8833905614540010572506939 13250858421810015858760409)
    ·
      refine ⟨9938143816357511894070307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13250858421810015858760409 9938143816357511894070307)
      ·
        refine ⟨14907215724536267841105461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9938143816357511894070307 14907215724536267841105461)
        ·
          refine ⟨1397551474175275110103637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14907215724536267841105461 1397551474175275110103637)
          ·
            refine ⟨16377556337991505196527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1397551474175275110103637 16377556337991505196527)
            ·
              rfl

theorem cell19_484408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 8].length) (baseStart_484408 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_484408 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_484408 prefixEnd_484408 := by exact prefixLift 484408
  have htrace : WordTrace (prefixWord ++ tailWord_484408) baseStart_484408 baseEnd_484408 := by
    simpa [prefixWord, tailWord_484408, baseEnd_484408] using wordTrace_append hprefix tailTrace_484408
  have hstable : (prefixWord ++ tailWord_484408).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484408).length < 2 ^ (prefixWord ++ tailWord_484408).sum := by decide
  have hdescent : baseEnd_484408 < baseStart_484408 := by decide
  rcases family_descends (prefixWord ++ tailWord_484408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484438 : List Nat := [5, 2, 2, 1, 2, 1, 3, 3]
def baseStart_484438 : Nat := 118140960795 + 484438 * 2 ^ 59
def prefixEnd_484438 : Nat := 4983230072969 + 3 ^ 40 * 484438 * 2
def baseEnd_484438 : Nat := 147407135586892366101995

theorem tailTrace_484438 : CollatzResearch.WordTrace tailWord_484438 prefixEnd_484438 147407135586892366101995 := by
  unfold tailWord_484438
  simp only [CollatzResearch.WordTrace]
  refine ⟨1104306588685708516787873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11779270279314224179070645 1104306588685708516787873)
  ·
    refine ⟨828229941514281387590905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1104306588685708516787873 828229941514281387590905)
    ·
      refine ⟨621172456135711040693179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 828229941514281387590905 621172456135711040693179)
      ·
        refine ⟨931758684203566561039769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 621172456135711040693179 931758684203566561039769)
        ·
          refine ⟨698819013152674920779827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 931758684203566561039769 698819013152674920779827)
          ·
            refine ⟨1048228519729012381169741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 698819013152674920779827 1048228519729012381169741)
            ·
              refine ⟨393085694898379642938653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1048228519729012381169741 393085694898379642938653)
              ·
                refine ⟨147407135586892366101995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 393085694898379642938653 147407135586892366101995)
                ·
                  rfl

theorem cell19_484438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_484438 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_484438 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_484438 prefixEnd_484438 := by exact prefixLift 484438
  have htrace : WordTrace (prefixWord ++ tailWord_484438) baseStart_484438 baseEnd_484438 := by
    simpa [prefixWord, tailWord_484438, baseEnd_484438] using wordTrace_append hprefix tailTrace_484438
  have hstable : (prefixWord ++ tailWord_484438).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484438).length < 2 ^ (prefixWord ++ tailWord_484438).sum := by decide
  have hdescent : baseEnd_484438 < baseStart_484438 := by decide
  rcases family_descends (prefixWord ++ tailWord_484438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484541 : List Nat := [1, 4, 1, 2, 1, 1, 3, 6]
def baseStart_484541 : Nat := 118140960795 + 484541 * 2 ^ 59
def prefixEnd_484541 : Nat := 4983230072969 + 3 ^ 40 * 484541 * 2
def baseEnd_484541 : Nat := 147438476924618645812825

theorem tailTrace_484541 : CollatzResearch.WordTrace tailWord_484541 prefixEnd_484541 147438476924618645812825 := by
  unfold tailWord_484541
  simp only [CollatzResearch.WordTrace]
  refine ⟨17672662137598184859605477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11781774758398789906403651 17672662137598184859605477)
  ·
    refine ⟨3313624150799659661176027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17672662137598184859605477 3313624150799659661176027)
    ·
      refine ⟨4970436226199489491764041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3313624150799659661176027 4970436226199489491764041)
      ·
        refine ⟨3727827169649617118823031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4970436226199489491764041 3727827169649617118823031)
        ·
          refine ⟨5591740754474425678234547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3727827169649617118823031 5591740754474425678234547)
          ·
            refine ⟨8387611131711638517351821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5591740754474425678234547 8387611131711638517351821)
            ·
              refine ⟨3145354174391864444006933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8387611131711638517351821 3145354174391864444006933)
              ·
                refine ⟨147438476924618645812825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3145354174391864444006933 147438476924618645812825)
                ·
                  rfl

theorem cell19_484541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 6].length) (baseStart_484541 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_484541 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_484541 prefixEnd_484541 := by exact prefixLift 484541
  have htrace : WordTrace (prefixWord ++ tailWord_484541) baseStart_484541 baseEnd_484541 := by
    simpa [prefixWord, tailWord_484541, baseEnd_484541] using wordTrace_append hprefix tailTrace_484541
  have hstable : (prefixWord ++ tailWord_484541).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484541).length < 2 ^ (prefixWord ++ tailWord_484541).sum := by decide
  have hdescent : baseEnd_484541 < baseStart_484541 := by decide
  rcases family_descends (prefixWord ++ tailWord_484541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484594 : List Nat := [3, 2, 1, 3, 3, 2, 1, 4]
def baseStart_484594 : Nat := 118140960795 + 484594 * 2 ^ 59
def prefixEnd_484594 : Nat := 4983230072969 + 3 ^ 40 * 484594 * 2
def baseEnd_484594 : Nat := 147454604020730226634903

theorem tailTrace_484594 : CollatzResearch.WordTrace tailWord_484594 prefixEnd_484594 147454604020730226634903 := by
  unfold tailWord_484594
  simp only [CollatzResearch.WordTrace]
  refine ⟨4418648801601543727821209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11783063470937449940856557 4418648801601543727821209)
  ·
    refine ⟨3313986601201157795865907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4418648801601543727821209 3313986601201157795865907)
    ·
      refine ⟨4970979901801736693798861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3313986601201157795865907 4970979901801736693798861)
      ·
        refine ⟨1864117463175651260174573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4970979901801736693798861 1864117463175651260174573)
        ·
          refine ⟨699044048690869222565465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1864117463175651260174573 699044048690869222565465)
          ·
            refine ⟨524283036518151916924099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 699044048690869222565465 524283036518151916924099)
            ·
              refine ⟨786424554777227875386149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 524283036518151916924099 786424554777227875386149)
              ·
                refine ⟨147454604020730226634903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 786424554777227875386149 147454604020730226634903)
                ·
                  rfl

theorem cell19_484594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 4].length) (baseStart_484594 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_484594 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_484594 prefixEnd_484594 := by exact prefixLift 484594
  have htrace : WordTrace (prefixWord ++ tailWord_484594) baseStart_484594 baseEnd_484594 := by
    simpa [prefixWord, tailWord_484594, baseEnd_484594] using wordTrace_append hprefix tailTrace_484594
  have hstable : (prefixWord ++ tailWord_484594).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484594).length < 2 ^ (prefixWord ++ tailWord_484594).sum := by decide
  have hdescent : baseEnd_484594 < baseStart_484594 := by decide
  rcases family_descends (prefixWord ++ tailWord_484594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484693 : List Nat := [1, 3, 2, 2, 3, 1, 7]
def baseStart_484693 : Nat := 118140960795 + 484693 * 2 ^ 59
def prefixEnd_484693 : Nat := 4983230072969 + 3 ^ 40 * 484693 * 2
def baseEnd_484693 : Nat := 49161576073042443478211

theorem tailTrace_484693 : CollatzResearch.WordTrace tailWord_484693 prefixEnd_484693 49161576073042443478211 := by
  unfold tailWord_484693
  simp only [CollatzResearch.WordTrace]
  refine ⟨17678206033047514819138733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11785470688698343212759155 17678206033047514819138733)
  ·
    refine ⟨6629327262392818057177025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17678206033047514819138733 6629327262392818057177025)
    ·
      refine ⟨4971995446794613542882769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6629327262392818057177025 4971995446794613542882769)
      ·
        refine ⟨3728996585095960157162077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4971995446794613542882769 3728996585095960157162077)
        ·
          refine ⟨1398373719410985058935779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3728996585095960157162077 1398373719410985058935779)
          ·
            refine ⟨2097560579116477588403669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1398373719410985058935779 2097560579116477588403669)
            ·
              refine ⟨49161576073042443478211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2097560579116477588403669 49161576073042443478211)
              ·
                rfl

theorem cell19_484693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 7].length) (baseStart_484693 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_484693 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_484693 prefixEnd_484693 := by exact prefixLift 484693
  have htrace : WordTrace (prefixWord ++ tailWord_484693) baseStart_484693 baseEnd_484693 := by
    simpa [prefixWord, tailWord_484693, baseEnd_484693] using wordTrace_append hprefix tailTrace_484693
  have hstable : (prefixWord ++ tailWord_484693).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484693).length < 2 ^ (prefixWord ++ tailWord_484693).sum := by decide
  have hdescent : baseEnd_484693 < baseStart_484693 := by decide
  rcases family_descends (prefixWord ++ tailWord_484693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484750 : List Nat := [4, 1, 1, 4, 9]
def baseStart_484750 : Nat := 118140960795 + 484750 * 2 ^ 59
def prefixEnd_484750 : Nat := 4983230072969 + 3 ^ 40 * 484750 * 2
def baseEnd_484750 : Nat := 5463039720539558783993

theorem tailTrace_484750 : CollatzResearch.WordTrace tailWord_484750 prefixEnd_484750 5463039720539558783993 := by
  unfold tailWord_484750
  simp only [CollatzResearch.WordTrace]
  refine ⟨2210035624230126694245463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11786856662560675702642469 2210035624230126694245463)
  ·
    refine ⟨3315053436345190041368195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2210035624230126694245463 3315053436345190041368195)
    ·
      refine ⟨4972580154517785062052293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3315053436345190041368195 4972580154517785062052293)
      ·
        refine ⟨932358778972084699134805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4972580154517785062052293 932358778972084699134805)
        ·
          refine ⟨5463039720539558783993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 932358778972084699134805 5463039720539558783993)
          ·
            rfl

theorem cell19_484750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 9].length) (baseStart_484750 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_484750 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_484750 prefixEnd_484750 := by exact prefixLift 484750
  have htrace : WordTrace (prefixWord ++ tailWord_484750) baseStart_484750 baseEnd_484750 := by
    simpa [prefixWord, tailWord_484750, baseEnd_484750] using wordTrace_append hprefix tailTrace_484750
  have hstable : (prefixWord ++ tailWord_484750).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484750).length < 2 ^ (prefixWord ++ tailWord_484750).sum := by decide
  have hdescent : baseEnd_484750 < baseStart_484750 := by decide
  rcases family_descends (prefixWord ++ tailWord_484750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484767 : List Nat := [1, 1, 2, 5, 1, 4, 1, 4]
def baseStart_484767 : Nat := 118140960795 + 484767 * 2 ^ 59
def prefixEnd_484767 : Nat := 4983230072969 + 3 ^ 40 * 484767 * 2
def baseEnd_484767 : Nat := 147507245296717084789987

theorem tailTrace_484767 : CollatzResearch.WordTrace tailWord_484767 prefixEnd_484767 147507245296717084789987 := by
  unfold tailWord_484767
  simp only [CollatzResearch.WordTrace]
  refine ⟨17680905034779425457332555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11787270023186283638221703 17680905034779425457332555)
  ·
    refine ⟨26521357552169138185998833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17680905034779425457332555 26521357552169138185998833)
    ·
      refine ⟨19891018164126853639499125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26521357552169138185998833 19891018164126853639499125)
      ·
        refine ⟨1864782952886892528703043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19891018164126853639499125 1864782952886892528703043)
        ·
          refine ⟨2797174429330338793054565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1864782952886892528703043 2797174429330338793054565)
          ·
            refine ⟨524470205499438523697731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2797174429330338793054565 524470205499438523697731)
            ·
              refine ⟨786705308249157785546597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 524470205499438523697731 786705308249157785546597)
              ·
                refine ⟨147507245296717084789987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 786705308249157785546597 147507245296717084789987)
                ·
                  rfl

theorem cell19_484767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 4].length) (baseStart_484767 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_484767 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_484767 prefixEnd_484767 := by exact prefixLift 484767
  have htrace : WordTrace (prefixWord ++ tailWord_484767) baseStart_484767 baseEnd_484767 := by
    simpa [prefixWord, tailWord_484767, baseEnd_484767] using wordTrace_append hprefix tailTrace_484767
  have hstable : (prefixWord ++ tailWord_484767).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484767).length < 2 ^ (prefixWord ++ tailWord_484767).sum := by decide
  have hdescent : baseEnd_484767 < baseStart_484767 := by decide
  rcases family_descends (prefixWord ++ tailWord_484767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484877 : List Nat := [1, 7, 1, 1, 2, 1, 2, 4]
def baseStart_484877 : Nat := 118140960795 + 484877 * 2 ^ 59
def prefixEnd_484877 : Nat := 4983230072969 + 3 ^ 40 * 484877 * 2
def baseEnd_484877 : Nat := 147540716628269422345243

theorem tailTrace_484877 : CollatzResearch.WordTrace tailWord_484877 prefixEnd_484877 147540716628269422345243 := by
  unfold tailWord_484877
  simp only [CollatzResearch.WordTrace]
  refine ⟨17684917064380914243836885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11789944709587276162557923 17684917064380914243836885)
  ·
    refine ⟨414490243696427677589927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 17684917064380914243836885 414490243696427677589927)
    ·
      refine ⟨621735365544641516384891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 414490243696427677589927 621735365544641516384891)
      ·
        refine ⟨932603048316962274577337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 621735365544641516384891 932603048316962274577337)
        ·
          refine ⟨699452286237721705933003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 932603048316962274577337 699452286237721705933003)
          ·
            refine ⟨1049178429356582558899505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 699452286237721705933003 1049178429356582558899505)
            ·
              refine ⟨786883822017436919174629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1049178429356582558899505 786883822017436919174629)
              ·
                refine ⟨147540716628269422345243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 786883822017436919174629 147540716628269422345243)
                ·
                  rfl

theorem cell19_484877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 4].length) (baseStart_484877 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_484877 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_484877 prefixEnd_484877 := by exact prefixLift 484877
  have htrace : WordTrace (prefixWord ++ tailWord_484877) baseStart_484877 baseEnd_484877 := by
    simpa [prefixWord, tailWord_484877, baseEnd_484877] using wordTrace_append hprefix tailTrace_484877
  have hstable : (prefixWord ++ tailWord_484877).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484877).length < 2 ^ (prefixWord ++ tailWord_484877).sum := by decide
  have hdescent : baseEnd_484877 < baseStart_484877 := by decide
  rcases family_descends (prefixWord ++ tailWord_484877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484883 : List Nat := [1, 1, 1, 2, 1, 7, 2, 4]
def baseStart_484883 : Nat := 118140960795 + 484883 * 2 ^ 59
def prefixEnd_484883 : Nat := 4983230072969 + 3 ^ 40 * 484883 * 2
def baseEnd_484883 : Nat := 147542542337263186211893

theorem tailTrace_484883 : CollatzResearch.WordTrace tailWord_484883 prefixEnd_484883 147542542337263186211893 := by
  unfold tailWord_484883
  simp only [CollatzResearch.WordTrace]
  refine ⟨17685135902359177268555303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11790090601572784845703535 17685135902359177268555303)
  ·
    refine ⟨26527703853538765902832955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17685135902359177268555303 26527703853538765902832955)
    ·
      refine ⟨39791555780308148854249433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26527703853538765902832955 39791555780308148854249433)
      ·
        refine ⟨29843666835231111640687075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39791555780308148854249433 29843666835231111640687075)
        ·
          refine ⟨44765500252846667461030613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29843666835231111640687075 44765500252846667461030613)
          ·
            refine ⟨1049191412176093768617905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 44765500252846667461030613 1049191412176093768617905)
            ·
              refine ⟨786893559132070326463429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1049191412176093768617905 786893559132070326463429)
              ·
                refine ⟨147542542337263186211893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 786893559132070326463429 147542542337263186211893)
                ·
                  rfl

theorem cell19_484883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 4].length) (baseStart_484883 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_484883 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_484883 prefixEnd_484883 := by exact prefixLift 484883
  have htrace : WordTrace (prefixWord ++ tailWord_484883) baseStart_484883 baseEnd_484883 := by
    simpa [prefixWord, tailWord_484883, baseEnd_484883] using wordTrace_append hprefix tailTrace_484883
  have hstable : (prefixWord ++ tailWord_484883).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484883).length < 2 ^ (prefixWord ++ tailWord_484883).sum := by decide
  have hdescent : baseEnd_484883 < baseStart_484883 := by decide
  rcases family_descends (prefixWord ++ tailWord_484883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484934 : List Nat := [6, 1, 1, 1, 3, 2, 1, 4]
def baseStart_484934 : Nat := 118140960795 + 484934 * 2 ^ 59
def prefixEnd_484934 : Nat := 4983230072969 + 3 ^ 40 * 484934 * 2
def baseEnd_484934 : Nat := 147558060863710179078421

theorem tailTrace_484934 : CollatzResearch.WordTrace tailWord_484934 prefixEnd_484934 147558060863710179078421 := by
  unfold tailWord_484934
  simp only [CollatzResearch.WordTrace]
  refine ⟨552718625786700405583183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 11791330683449608652441237 552718625786700405583183)
  ·
    refine ⟨829077938680050608374775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 552718625786700405583183 829077938680050608374775)
    ·
      refine ⟨1243616908020075912562163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 829077938680050608374775 1243616908020075912562163)
      ·
        refine ⟨1865425362030113868843245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1243616908020075912562163 1865425362030113868843245)
        ·
          refine ⟨699534510761292700816217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1865425362030113868843245 699534510761292700816217)
          ·
            refine ⟨524650883070969525612163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 699534510761292700816217 524650883070969525612163)
            ·
              refine ⟨786976324606454288418245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 524650883070969525612163 786976324606454288418245)
              ·
                refine ⟨147558060863710179078421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 786976324606454288418245 147558060863710179078421)
                ·
                  rfl

theorem cell19_484934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_484934 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_484934 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_484934 prefixEnd_484934 := by exact prefixLift 484934
  have htrace : WordTrace (prefixWord ++ tailWord_484934) baseStart_484934 baseEnd_484934 := by
    simpa [prefixWord, tailWord_484934, baseEnd_484934] using wordTrace_append hprefix tailTrace_484934
  have hstable : (prefixWord ++ tailWord_484934).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484934).length < 2 ^ (prefixWord ++ tailWord_484934).sum := by decide
  have hdescent : baseEnd_484934 < baseStart_484934 := by decide
  rcases family_descends (prefixWord ++ tailWord_484934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484940 : List Nat := [2, 2, 1, 3, 1, 3, 3, 4]
def baseStart_484940 : Nat := 118140960795 + 484940 * 2 ^ 59
def prefixEnd_484940 : Nat := 4983230072969 + 3 ^ 40 * 484940 * 2
def baseEnd_484940 : Nat := 147559886572703942945071

theorem tailTrace_484940 : CollatzResearch.WordTrace tailWord_484940 prefixEnd_484940 147559886572703942945071 := by
  unfold tailWord_484940
  simp only [CollatzResearch.WordTrace]
  refine ⟨8843607431576338001690137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11791476575435117335586849 8843607431576338001690137)
  ·
    refine ⟨6632705573682253501267603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8843607431576338001690137 6632705573682253501267603)
    ·
      refine ⟨9949058360523380251901405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6632705573682253501267603 9949058360523380251901405)
      ·
        refine ⟨3730896885196267594463027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9949058360523380251901405 3730896885196267594463027)
        ·
          refine ⟨5596345327794401391694541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3730896885196267594463027 5596345327794401391694541)
          ·
            refine ⟨2098629497922900521885453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5596345327794401391694541 2098629497922900521885453)
            ·
              refine ⟨786986061721087695707045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2098629497922900521885453 786986061721087695707045)
              ·
                refine ⟨147559886572703942945071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 786986061721087695707045 147559886572703942945071)
                ·
                  rfl

theorem cell19_484940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 4].length) (baseStart_484940 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_484940 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_484940 prefixEnd_484940 := by exact prefixLift 484940
  have htrace : WordTrace (prefixWord ++ tailWord_484940) baseStart_484940 baseEnd_484940 := by
    simpa [prefixWord, tailWord_484940, baseEnd_484940] using wordTrace_append hprefix tailTrace_484940
  have hstable : (prefixWord ++ tailWord_484940).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484940).length < 2 ^ (prefixWord ++ tailWord_484940).sum := by decide
  have hdescent : baseEnd_484940 < baseStart_484940 := by decide
  rcases family_descends (prefixWord ++ tailWord_484940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484978 : List Nat := [3, 2, 1, 2, 3, 2, 6]
def baseStart_484978 : Nat := 118140960795 + 484978 * 2 ^ 59
def prefixEnd_484978 : Nat := 4983230072969 + 3 ^ 40 * 484978 * 2
def baseEnd_484978 : Nat := 49190483132110371366841

theorem tailTrace_484978 : CollatzResearch.WordTrace tailWord_484978 prefixEnd_484978 49190483132110371366841 := by
  unfold tailWord_484978
  simp only [CollatzResearch.WordTrace]
  refine ⟨4422150209253752123315897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11792400558010005662175725 4422150209253752123315897)
  ·
    refine ⟨3316612656940314092486923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4422150209253752123315897 3316612656940314092486923)
    ·
      refine ⟨4974918985410471138730385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3316612656940314092486923 4974918985410471138730385)
      ·
        refine ⟨3731189239057853354047789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4974918985410471138730385 3731189239057853354047789)
        ·
          refine ⟨1399195964646695007767921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3731189239057853354047789 1399195964646695007767921)
          ·
            refine ⟨1049396973485021255825941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1399195964646695007767921 1049396973485021255825941)
            ·
              refine ⟨49190483132110371366841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1049396973485021255825941 49190483132110371366841)
              ·
                rfl

theorem cell19_484978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 6].length) (baseStart_484978 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_484978 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_484978 prefixEnd_484978 := by exact prefixLift 484978
  have htrace : WordTrace (prefixWord ++ tailWord_484978) baseStart_484978 baseEnd_484978 := by
    simpa [prefixWord, tailWord_484978, baseEnd_484978] using wordTrace_append hprefix tailTrace_484978
  have hstable : (prefixWord ++ tailWord_484978).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484978).length < 2 ^ (prefixWord ++ tailWord_484978).sum := by decide
  have hdescent : baseEnd_484978 < baseStart_484978 := by decide
  rcases family_descends (prefixWord ++ tailWord_484978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485010 : List Nat := [3, 2, 3, 1, 4, 1, 2, 3]
def baseStart_485010 : Nat := 118140960795 + 485010 * 2 ^ 59
def prefixEnd_485010 : Nat := 4983230072969 + 3 ^ 40 * 485010 * 2
def baseEnd_485010 : Nat := 147581186510964521389325

theorem tailTrace_485010 : CollatzResearch.WordTrace tailWord_485010 prefixEnd_485010 147581186510964521389325 := by
  unfold tailWord_485010
  simp only [CollatzResearch.WordTrace]
  refine ⟨4422441993224769489607121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11793178648599385305618989 4422441993224769489607121)
  ·
    refine ⟨3316831494918577117205341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4422441993224769489607121 3316831494918577117205341)
    ·
      refine ⟨1243811810594466418952003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3316831494918577117205341 1243811810594466418952003)
      ·
        refine ⟨1865717715891699628428005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1243811810594466418952003 1865717715891699628428005)
        ·
          refine ⟨349822071729693680330251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1865717715891699628428005 349822071729693680330251)
          ·
            refine ⟨524733107594540520495377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 349822071729693680330251 524733107594540520495377)
            ·
              refine ⟨393549830695905390371533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 524733107594540520495377 393549830695905390371533)
              ·
                refine ⟨147581186510964521389325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 393549830695905390371533 147581186510964521389325)
                ·
                  rfl

theorem cell19_485010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 2, 3].length) (baseStart_485010 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_485010 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_485010 prefixEnd_485010 := by exact prefixLift 485010
  have htrace : WordTrace (prefixWord ++ tailWord_485010) baseStart_485010 baseEnd_485010 := by
    simpa [prefixWord, tailWord_485010, baseEnd_485010] using wordTrace_append hprefix tailTrace_485010
  have hstable : (prefixWord ++ tailWord_485010).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485010).length < 2 ^ (prefixWord ++ tailWord_485010).sum := by decide
  have hdescent : baseEnd_485010 < baseStart_485010 := by decide
  rcases family_descends (prefixWord ++ tailWord_485010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485016 : List Nat := [2, 1, 2, 4, 1, 3, 1, 5]
def baseStart_485016 : Nat := 118140960795 + 485016 * 2 ^ 59
def prefixEnd_485016 : Nat := 4983230072969 + 3 ^ 40 * 485016 * 2
def baseEnd_485016 : Nat := 147583012219958285255975

theorem tailTrace_485016 : CollatzResearch.WordTrace tailWord_485016 prefixEnd_485016 147583012219958285255975 := by
  unfold tailWord_485016
  simp only [CollatzResearch.WordTrace]
  refine ⟨8844993405438670491573451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11793324540584893988764601 8844993405438670491573451)
  ·
    refine ⟨13267490108158005737360177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8844993405438670491573451 13267490108158005737360177)
    ·
      refine ⟨9950617581118504303020133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13267490108158005737360177 9950617581118504303020133)
      ·
        refine ⟨1865740796459719556816275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9950617581118504303020133 1865740796459719556816275)
        ·
          refine ⟨2798611194689579335224413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1865740796459719556816275 2798611194689579335224413)
          ·
            refine ⟨1049479198008592250709155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2798611194689579335224413 1049479198008592250709155)
            ·
              refine ⟨1574218797012888376063733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1049479198008592250709155 1574218797012888376063733)
              ·
                refine ⟨147583012219958285255975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1574218797012888376063733 147583012219958285255975)
                ·
                  rfl

theorem cell19_485016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 5].length) (baseStart_485016 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_485016 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_485016 prefixEnd_485016 := by exact prefixLift 485016
  have htrace : WordTrace (prefixWord ++ tailWord_485016) baseStart_485016 baseEnd_485016 := by
    simpa [prefixWord, tailWord_485016, baseEnd_485016] using wordTrace_append hprefix tailTrace_485016
  have hstable : (prefixWord ++ tailWord_485016).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485016).length < 2 ^ (prefixWord ++ tailWord_485016).sum := by decide
  have hdescent : baseEnd_485016 < baseStart_485016 := by decide
  rcases family_descends (prefixWord ++ tailWord_485016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485054 : List Nat := [4, 2, 1, 1, 2, 2, 1, 6]
def baseStart_485054 : Nat := 118140960795 + 485054 * 2 ^ 59
def prefixEnd_485054 : Nat := 4983230072969 + 3 ^ 40 * 485054 * 2
def baseEnd_485054 : Nat := 147594575043585456411427

theorem tailTrace_485054 : CollatzResearch.WordTrace tailWord_485054 prefixEnd_485054 147594575043585456411427 := by
  unfold tailWord_485054
  simp only [CollatzResearch.WordTrace]
  refine ⟨2211421598092459184128777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11794248523159782315353477 2211421598092459184128777)
  ·
    refine ⟨1658566198569344388096583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2211421598092459184128777 1658566198569344388096583)
    ·
      refine ⟨2487849297854016582144875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1658566198569344388096583 2487849297854016582144875)
      ·
        refine ⟨3731773946781024873217313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2487849297854016582144875 3731773946781024873217313)
        ·
          refine ⟨2798830460085768654912985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3731773946781024873217313 2798830460085768654912985)
          ·
            refine ⟨2099122845064326491184739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2798830460085768654912985 2099122845064326491184739)
            ·
              refine ⟨3148684267596489736777109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2099122845064326491184739 3148684267596489736777109)
              ·
                refine ⟨147594575043585456411427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3148684267596489736777109 147594575043585456411427)
                ·
                  rfl

theorem cell19_485054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_485054 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_485054 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_485054 prefixEnd_485054 := by exact prefixLift 485054
  have htrace : WordTrace (prefixWord ++ tailWord_485054) baseStart_485054 baseEnd_485054 := by
    simpa [prefixWord, tailWord_485054, baseEnd_485054] using wordTrace_append hprefix tailTrace_485054
  have hstable : (prefixWord ++ tailWord_485054).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485054).length < 2 ^ (prefixWord ++ tailWord_485054).sum := by decide
  have hdescent : baseEnd_485054 < baseStart_485054 := by decide
  rcases family_descends (prefixWord ++ tailWord_485054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485132 : List Nat := [2, 2, 1, 2, 2, 1, 2, 7]
def baseStart_485132 : Nat := 118140960795 + 485132 * 2 ^ 59
def prefixEnd_485132 : Nat := 4983230072969 + 3 ^ 40 * 485132 * 2
def baseEnd_485132 : Nat := 147618309260504386677881

theorem tailTrace_485132 : CollatzResearch.WordTrace tailWord_485132 prefixEnd_485132 147618309260504386677881 := by
  unfold tailWord_485132
  simp only [CollatzResearch.WordTrace]
  refine ⟨8847108839228546397184825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11796145118971395196246433 8847108839228546397184825)
  ·
    refine ⟨6635331629421409797888619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8847108839228546397184825 6635331629421409797888619)
    ·
      refine ⟨9952997444132114696832929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6635331629421409797888619 9952997444132114696832929)
      ·
        refine ⟨7464748083099086022624697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9952997444132114696832929 7464748083099086022624697)
        ·
          refine ⟨5598561062324314516968523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7464748083099086022624697 5598561062324314516968523)
          ·
            refine ⟨8397841593486471775452785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5598561062324314516968523 8397841593486471775452785)
            ·
              refine ⟨6298381195114853831589589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8397841593486471775452785 6298381195114853831589589)
              ·
                refine ⟨147618309260504386677881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6298381195114853831589589 147618309260504386677881)
                ·
                  rfl

theorem cell19_485132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 7].length) (baseStart_485132 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_485132 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_485132 prefixEnd_485132 := by exact prefixLift 485132
  have htrace : WordTrace (prefixWord ++ tailWord_485132) baseStart_485132 baseEnd_485132 := by
    simpa [prefixWord, tailWord_485132, baseEnd_485132] using wordTrace_append hprefix tailTrace_485132
  have hstable : (prefixWord ++ tailWord_485132).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485132).length < 2 ^ (prefixWord ++ tailWord_485132).sum := by decide
  have hdescent : baseEnd_485132 < baseStart_485132 := by decide
  rcases family_descends (prefixWord ++ tailWord_485132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485151 : List Nat := [1, 1, 2, 4, 2, 1, 8]
def baseStart_485151 : Nat := 118140960795 + 485151 * 2 ^ 59
def prefixEnd_485151 : Nat := 4983230072969 + 3 ^ 40 * 485151 * 2
def baseEnd_485151 : Nat := 49208030224105990751869

theorem tailTrace_485151 : CollatzResearch.WordTrace tailWord_485151 prefixEnd_485151 49208030224105990751869 := by
  unfold tailWord_485151
  simp only [CollatzResearch.WordTrace]
  refine ⟨17694910665388259039311307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11796607110258839359540871 17694910665388259039311307)
  ·
    refine ⟨26542365998082388558966961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17694910665388259039311307 26542365998082388558966961)
    ·
      refine ⟨19906774498561791419225221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26542365998082388558966961 19906774498561791419225221)
      ·
        refine ⟨3732520218480335891104729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19906774498561791419225221 3732520218480335891104729)
        ·
          refine ⟨2799390163860251918328547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3732520218480335891104729 2799390163860251918328547)
          ·
            refine ⟨4199085245790377877492821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2799390163860251918328547 4199085245790377877492821)
            ·
              refine ⟨49208030224105990751869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4199085245790377877492821 49208030224105990751869)
              ·
                rfl

theorem cell19_485151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 8].length) (baseStart_485151 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_485151 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_485151 prefixEnd_485151 := by exact prefixLift 485151
  have htrace : WordTrace (prefixWord ++ tailWord_485151) baseStart_485151 baseEnd_485151 := by
    simpa [prefixWord, tailWord_485151, baseEnd_485151] using wordTrace_append hprefix tailTrace_485151
  have hstable : (prefixWord ++ tailWord_485151).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485151).length < 2 ^ (prefixWord ++ tailWord_485151).sum := by decide
  have hdescent : baseEnd_485151 < baseStart_485151 := by decide
  rcases family_descends (prefixWord ++ tailWord_485151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485183 : List Nat := [1, 1, 2, 2, 7, 1, 2, 3]
def baseStart_485183 : Nat := 118140960795 + 485183 * 2 ^ 59
def prefixEnd_485183 : Nat := 4983230072969 + 3 ^ 40 * 485183 * 2
def baseEnd_485183 : Nat := 147633827786951379544409

theorem tailTrace_485183 : CollatzResearch.WordTrace tailWord_485183 prefixEnd_485183 147633827786951379544409 := by
  unfold tailWord_485183
  simp only [CollatzResearch.WordTrace]
  refine ⟨17696077801272328504476203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11797385200848219002984135 17696077801272328504476203)
  ·
    refine ⟨26544116701908492756714305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17696077801272328504476203 26544116701908492756714305)
    ·
      refine ⟨19908087526431369567535729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26544116701908492756714305 19908087526431369567535729)
      ·
        refine ⟨14931065644823527175651797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19908087526431369567535729 14931065644823527175651797)
        ·
          refine ⟨349946851050551418179339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 14931065644823527175651797 349946851050551418179339)
          ·
            refine ⟨524920276575827127269009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 349946851050551418179339 524920276575827127269009)
            ·
              refine ⟨393690207431870345451757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 524920276575827127269009 393690207431870345451757)
              ·
                refine ⟨147633827786951379544409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 393690207431870345451757 147633827786951379544409)
                ·
                  rfl

theorem cell19_485183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 2, 3].length) (baseStart_485183 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_485183 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_485183 prefixEnd_485183 := by exact prefixLift 485183
  have htrace : WordTrace (prefixWord ++ tailWord_485183) baseStart_485183 baseEnd_485183 := by
    simpa [prefixWord, tailWord_485183, baseEnd_485183] using wordTrace_append hprefix tailTrace_485183
  have hstable : (prefixWord ++ tailWord_485183).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485183).length < 2 ^ (prefixWord ++ tailWord_485183).sum := by decide
  have hdescent : baseEnd_485183 < baseStart_485183 := by decide
  rcases family_descends (prefixWord ++ tailWord_485183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485187 : List Nat := [1, 1, 1, 3, 1, 5, 4, 3]
def baseStart_485187 : Nat := 118140960795 + 485187 * 2 ^ 59
def prefixEnd_485187 : Nat := 4983230072969 + 3 ^ 40 * 485187 * 2
def baseEnd_485187 : Nat := 147635044926280555455509

theorem tailTrace_485187 : CollatzResearch.WordTrace tailWord_485187 prefixEnd_485187 147635044926280555455509 := by
  unfold tailWord_485187
  simp only [CollatzResearch.WordTrace]
  refine ⟨17696223693257837187621815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11797482462171891458414543 17696223693257837187621815)
  ·
    refine ⟨26544335539886755781432723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17696223693257837187621815 26544335539886755781432723)
    ·
      refine ⟨39816503309830133672149085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26544335539886755781432723 39816503309830133672149085)
      ·
        refine ⟨14931188741186300127055907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39816503309830133672149085 14931188741186300127055907)
        ·
          refine ⟨22396783111779450190583861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14931188741186300127055907 22396783111779450190583861)
          ·
            refine ⟨2099698416729323455367237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22396783111779450190583861 2099698416729323455367237)
            ·
              refine ⟨393693453136748147881357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2099698416729323455367237 393693453136748147881357)
              ·
                refine ⟨147635044926280555455509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 393693453136748147881357 147635044926280555455509)
                ·
                  rfl

theorem cell19_485187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 4, 3].length) (baseStart_485187 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_485187 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_485187 prefixEnd_485187 := by exact prefixLift 485187
  have htrace : WordTrace (prefixWord ++ tailWord_485187) baseStart_485187 baseEnd_485187 := by
    simpa [prefixWord, tailWord_485187, baseEnd_485187] using wordTrace_append hprefix tailTrace_485187
  have hstable : (prefixWord ++ tailWord_485187).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485187).length < 2 ^ (prefixWord ++ tailWord_485187).sum := by decide
  have hdescent : baseEnd_485187 < baseStart_485187 := by decide
  rcases family_descends (prefixWord ++ tailWord_485187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485189 : List Nat := [1, 3, 1, 1, 1, 2, 5, 5]
def baseStart_485189 : Nat := 118140960795 + 485189 * 2 ^ 59
def prefixEnd_485189 : Nat := 4983230072969 + 3 ^ 40 * 485189 * 2
def baseEnd_485189 : Nat := 147635653495945143411059

theorem tailTrace_485189 : CollatzResearch.WordTrace tailWord_485189 prefixEnd_485189 147635653495945143411059 := by
  unfold tailWord_485189
  simp only [CollatzResearch.WordTrace]
  refine ⟨17696296639250591529194621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11797531092833727686129747 17696296639250591529194621)
  ·
    refine ⟨6636111239718971823447983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17696296639250591529194621 6636111239718971823447983)
    ·
      refine ⟨9954166859578457735171975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6636111239718971823447983 9954166859578457735171975)
      ·
        refine ⟨14931250289367686602757963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9954166859578457735171975 14931250289367686602757963)
        ·
          refine ⟨22396875434051529904136945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14931250289367686602757963 22396875434051529904136945)
          ·
            refine ⟨16797656575538647428102709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22396875434051529904136945 16797656575538647428102709)
            ·
              refine ⟨1574780303956748196384629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16797656575538647428102709 1574780303956748196384629)
              ·
                refine ⟨147635653495945143411059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1574780303956748196384629 147635653495945143411059)
                ·
                  rfl

theorem cell19_485189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 5].length) (baseStart_485189 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_485189 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_485189 prefixEnd_485189 := by exact prefixLift 485189
  have htrace : WordTrace (prefixWord ++ tailWord_485189) baseStart_485189 baseEnd_485189 := by
    simpa [prefixWord, tailWord_485189, baseEnd_485189] using wordTrace_append hprefix tailTrace_485189
  have hstable : (prefixWord ++ tailWord_485189).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485189).length < 2 ^ (prefixWord ++ tailWord_485189).sum := by decide
  have hdescent : baseEnd_485189 < baseStart_485189 := by decide
  rcases family_descends (prefixWord ++ tailWord_485189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485358 : List Nat := [4, 1, 2, 1, 3, 2, 1, 5]
def baseStart_485358 : Nat := 118140960795 + 485358 * 2 ^ 59
def prefixEnd_485358 : Nat := 4983230072969 + 3 ^ 40 * 485358 * 2
def baseEnd_485358 : Nat := 147687077632602825655043

theorem tailTrace_485358 : CollatzResearch.WordTrace tailWord_485358 prefixEnd_485358 147687077632602825655043 := by
  unfold tailWord_485358
  simp only [CollatzResearch.WordTrace]
  refine ⟨2212807571954791674012091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11801640383758888928064485 2212807571954791674012091)
  ·
    refine ⟨3319211357932187511018137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2212807571954791674012091 3319211357932187511018137)
    ·
      refine ⟨2489408518449140633263603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3319211357932187511018137 2489408518449140633263603)
      ·
        refine ⟨3734112777673710949895405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2489408518449140633263603 3734112777673710949895405)
        ·
          refine ⟨1400292291627641606210777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3734112777673710949895405 1400292291627641606210777)
          ·
            refine ⟨1050219218720731204658083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1400292291627641606210777 1050219218720731204658083)
            ·
              refine ⟨1575328828081096806987125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1050219218720731204658083 1575328828081096806987125)
              ·
                refine ⟨147687077632602825655043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1575328828081096806987125 147687077632602825655043)
                ·
                  rfl

theorem cell19_485358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_485358 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_485358 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_485358 prefixEnd_485358 := by exact prefixLift 485358
  have htrace : WordTrace (prefixWord ++ tailWord_485358) baseStart_485358 baseEnd_485358 := by
    simpa [prefixWord, tailWord_485358, baseEnd_485358] using wordTrace_append hprefix tailTrace_485358
  have hstable : (prefixWord ++ tailWord_485358).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485358).length < 2 ^ (prefixWord ++ tailWord_485358).sum := by decide
  have hdescent : baseEnd_485358 < baseStart_485358 := by decide
  rcases family_descends (prefixWord ++ tailWord_485358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485472 : List Nat := [2, 1, 1, 3, 2, 4, 3, 3]
def baseStart_485472 : Nat := 118140960795 + 485472 * 2 ^ 59
def prefixEnd_485472 : Nat := 4983230072969 + 3 ^ 40 * 485472 * 2
def baseEnd_485472 : Nat := 147721766103484339121399

theorem tailTrace_485472 : CollatzResearch.WordTrace tailWord_485472 prefixEnd_485472 147721766103484339121399 := by
  unfold tailWord_485472
  simp only [CollatzResearch.WordTrace]
  refine ⟨8853309248612665430873335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11804412331483553907831113 8853309248612665430873335)
  ·
    refine ⟨13279963872918998146310003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8853309248612665430873335 13279963872918998146310003)
    ·
      refine ⟨19919945809378497219465005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13279963872918998146310003 19919945809378497219465005)
      ·
        refine ⟨7469979678516936457299377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19919945809378497219465005 7469979678516936457299377)
        ·
          refine ⟨5602484758887702342974533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7469979678516936457299377 5602484758887702342974533)
          ·
            refine ⟨1050465892291444189307725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5602484758887702342974533 1050465892291444189307725)
            ·
              refine ⟨393924709609291570990397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1050465892291444189307725 393924709609291570990397)
              ·
                refine ⟨147721766103484339121399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 393924709609291570990397 147721766103484339121399)
                ·
                  rfl

theorem cell19_485472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 3, 3].length) (baseStart_485472 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_485472 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_485472 prefixEnd_485472 := by exact prefixLift 485472
  have htrace : WordTrace (prefixWord ++ tailWord_485472) baseStart_485472 baseEnd_485472 := by
    simpa [prefixWord, tailWord_485472, baseEnd_485472] using wordTrace_append hprefix tailTrace_485472
  have hstable : (prefixWord ++ tailWord_485472).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485472).length < 2 ^ (prefixWord ++ tailWord_485472).sum := by decide
  have hdescent : baseEnd_485472 < baseStart_485472 := by decide
  rcases family_descends (prefixWord ++ tailWord_485472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485527 : List Nat := [1, 1, 3, 3, 4, 2, 2, 3]
def baseStart_485527 : Nat := 118140960795 + 485527 * 2 ^ 59
def prefixEnd_485527 : Nat := 4983230072969 + 3 ^ 40 * 485527 * 2
def baseEnd_485527 : Nat := 147738501769260507899027

theorem tailTrace_485527 : CollatzResearch.WordTrace tailWord_485527 prefixEnd_485527 147738501769260507899027 := by
  unfold tailWord_485527
  simp only [CollatzResearch.WordTrace]
  refine ⟨17708624512026075254998835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11805749674684050169999223 17708624512026075254998835)
  ·
    refine ⟨26562936768039112882498253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17708624512026075254998835 26562936768039112882498253)
    ·
      refine ⟨9961101288014667330936845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26562936768039112882498253 9961101288014667330936845)
      ·
        refine ⟨3735412983005500249101317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9961101288014667330936845 3735412983005500249101317)
        ·
          refine ⟨700389934313531296706497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3735412983005500249101317 700389934313531296706497)
          ·
            refine ⟨525292450735148472529873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 700389934313531296706497 525292450735148472529873)
            ·
              refine ⟨393969338051361354397405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 525292450735148472529873 393969338051361354397405)
              ·
                refine ⟨147738501769260507899027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 393969338051361354397405 147738501769260507899027)
                ·
                  rfl

theorem cell19_485527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 2, 3].length) (baseStart_485527 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_485527 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_485527 prefixEnd_485527 := by exact prefixLift 485527
  have htrace : WordTrace (prefixWord ++ tailWord_485527) baseStart_485527 baseEnd_485527 := by
    simpa [prefixWord, tailWord_485527, baseEnd_485527] using wordTrace_append hprefix tailTrace_485527
  have hstable : (prefixWord ++ tailWord_485527).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485527).length < 2 ^ (prefixWord ++ tailWord_485527).sum := by decide
  have hdescent : baseEnd_485527 < baseStart_485527 := by decide
  rcases family_descends (prefixWord ++ tailWord_485527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485546 : List Nat := [3, 1, 5, 1, 2, 2, 5]
def baseStart_485546 : Nat := 118140960795 + 485546 * 2 ^ 59
def prefixEnd_485546 : Nat := 4983230072969 + 3 ^ 40 * 485546 * 2
def baseEnd_485546 : Nat := 49248094393691364492251

theorem tailTrace_485546 : CollatzResearch.WordTrace tailWord_485546 prefixEnd_485546 49248094393691364492251 := by
  unfold tailWord_485546
  simp only [CollatzResearch.WordTrace]
  refine ⟨4427329374739310374985123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11806211665971494333293661 4427329374739310374985123)
  ·
    refine ⟨6640994062108965562477685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4427329374739310374985123 6640994062108965562477685)
    ·
      refine ⟨622593193322715521482283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6640994062108965562477685 622593193322715521482283)
      ·
        refine ⟨933889789984073282223425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 622593193322715521482283 933889789984073282223425)
        ·
          refine ⟨700417342488054961667569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 933889789984073282223425 700417342488054961667569)
          ·
            refine ⟨525313006866041221250677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 700417342488054961667569 525313006866041221250677)
            ·
              refine ⟨49248094393691364492251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 525313006866041221250677 49248094393691364492251)
              ·
                rfl

theorem cell19_485546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 5].length) (baseStart_485546 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_485546 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_485546 prefixEnd_485546 := by exact prefixLift 485546
  have htrace : WordTrace (prefixWord ++ tailWord_485546) baseStart_485546 baseEnd_485546 := by
    simpa [prefixWord, tailWord_485546, baseEnd_485546] using wordTrace_append hprefix tailTrace_485546
  have hstable : (prefixWord ++ tailWord_485546).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485546).length < 2 ^ (prefixWord ++ tailWord_485546).sum := by decide
  have hdescent : baseEnd_485546 < baseStart_485546 := by decide
  rcases family_descends (prefixWord ++ tailWord_485546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485607 : List Nat := [1, 1, 5, 3, 1, 8]
def baseStart_485607 : Nat := 118140960795 + 485607 * 2 ^ 59
def prefixEnd_485607 : Nat := 4983230072969 + 3 ^ 40 * 485607 * 2
def baseEnd_485607 : Nat := 16418093839538225124559

theorem tailTrace_485607 : CollatzResearch.WordTrace tailWord_485607 prefixEnd_485607 16418093839538225124559 := by
  unfold tailWord_485607
  simp only [CollatzResearch.WordTrace]
  refine ⟨17711542351736248917911075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11807694901157499278607383 17711542351736248917911075)
  ·
    refine ⟨26567313527604373376866613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17711542351736248917911075 26567313527604373376866613)
    ·
      refine ⟨2490685643212910004081245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26567313527604373376866613 2490685643212910004081245)
      ·
        refine ⟨934007116204841251530467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2490685643212910004081245 934007116204841251530467)
        ·
          refine ⟨1401010674307261877295701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 934007116204841251530467 1401010674307261877295701)
          ·
            refine ⟨16418093839538225124559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1401010674307261877295701 16418093839538225124559)
            ·
              rfl

theorem cell19_485607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 8].length) (baseStart_485607 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_485607 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_485607 prefixEnd_485607 := by exact prefixLift 485607
  have htrace : WordTrace (prefixWord ++ tailWord_485607) baseStart_485607 baseEnd_485607 := by
    simpa [prefixWord, tailWord_485607, baseEnd_485607] using wordTrace_append hprefix tailTrace_485607
  have hstable : (prefixWord ++ tailWord_485607).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485607).length < 2 ^ (prefixWord ++ tailWord_485607).sum := by decide
  have hdescent : baseEnd_485607 < baseStart_485607 := by decide
  rcases family_descends (prefixWord ++ tailWord_485607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485626 : List Nat := [3, 1, 1, 1, 1, 5, 3, 4]
def baseStart_485626 : Nat := 118140960795 + 485626 * 2 ^ 59
def prefixEnd_485626 : Nat := 4983230072969 + 3 ^ 40 * 485626 * 2
def baseEnd_485626 : Nat := 147768625967657611698757

theorem tailTrace_485626 : CollatzResearch.WordTrace tailWord_485626 prefixEnd_485626 147768625967657611698757 := by
  unfold tailWord_485626
  simp only [CollatzResearch.WordTrace]
  refine ⟨4428058834666853790713183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11808156892444943441901821 4428058834666853790713183)
  ·
    refine ⟨6642088252000280686069775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4428058834666853790713183 6642088252000280686069775)
    ·
      refine ⟨9963132378000421029104663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6642088252000280686069775 9963132378000421029104663)
      ·
        refine ⟨14944698567000631543656995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9963132378000421029104663 14944698567000631543656995)
        ·
          refine ⟨22417047850500947315485493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14944698567000631543656995 22417047850500947315485493)
          ·
            refine ⟨2101598235984463810826765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22417047850500947315485493 2101598235984463810826765)
            ·
              refine ⟨788099338494173929060037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2101598235984463810826765 788099338494173929060037)
              ·
                refine ⟨147768625967657611698757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 788099338494173929060037 147768625967657611698757)
                ·
                  rfl

theorem cell19_485626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 4].length) (baseStart_485626 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_485626 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_485626 prefixEnd_485626 := by exact prefixLift 485626
  have htrace : WordTrace (prefixWord ++ tailWord_485626) baseStart_485626 baseEnd_485626 := by
    simpa [prefixWord, tailWord_485626, baseEnd_485626] using wordTrace_append hprefix tailTrace_485626
  have hstable : (prefixWord ++ tailWord_485626).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485626).length < 2 ^ (prefixWord ++ tailWord_485626).sum := by decide
  have hdescent : baseEnd_485626 < baseStart_485626 := by decide
  rcases family_descends (prefixWord ++ tailWord_485626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485647 : List Nat := [1, 1, 2, 1, 1, 1, 3, 9]
def baseStart_485647 : Nat := 118140960795 + 485647 * 2 ^ 59
def prefixEnd_485647 : Nat := 4983230072969 + 3 ^ 40 * 485647 * 2
def baseEnd_485647 : Nat := 147775015949135785232033

theorem tailTrace_485647 : CollatzResearch.WordTrace tailWord_485647 prefixEnd_485647 147775015949135785232033 := by
  unfold tailWord_485647
  simp only [CollatzResearch.WordTrace]
  refine ⟨17713001271591335749367195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11808667514394223832911463 17713001271591335749367195)
  ·
    refine ⟨26569501907387003624050793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17713001271591335749367195 26569501907387003624050793)
    ·
      refine ⟨19927126430540252718038095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26569501907387003624050793 19927126430540252718038095)
      ·
        refine ⟨29890689645810379077057143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19927126430540252718038095 29890689645810379077057143)
        ·
          refine ⟨44836034468715568615585715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29890689645810379077057143 44836034468715568615585715)
          ·
            refine ⟨67254051703073352923378573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44836034468715568615585715 67254051703073352923378573)
            ·
              refine ⟨25220269388652507346266965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67254051703073352923378573 25220269388652507346266965)
              ·
                refine ⟨147775015949135785232033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25220269388652507346266965 147775015949135785232033)
                ·
                  rfl

theorem cell19_485647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 9].length) (baseStart_485647 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_485647 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_485647 prefixEnd_485647 := by exact prefixLift 485647
  have htrace : WordTrace (prefixWord ++ tailWord_485647) baseStart_485647 baseEnd_485647 := by
    simpa [prefixWord, tailWord_485647, baseEnd_485647] using wordTrace_append hprefix tailTrace_485647
  have hstable : (prefixWord ++ tailWord_485647).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485647).length < 2 ^ (prefixWord ++ tailWord_485647).sum := by decide
  have hdescent : baseEnd_485647 < baseStart_485647 := by decide
  rcases family_descends (prefixWord ++ tailWord_485647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485664 : List Nat := [2, 1, 1, 5, 2, 2, 6]
def baseStart_485664 : Nat := 118140960795 + 485664 * 2 ^ 59
def prefixEnd_485664 : Nat := 4983230072969 + 3 ^ 40 * 485664 * 2
def baseEnd_485664 : Nat := 49260062930428260951403

theorem tailTrace_485664 : CollatzResearch.WordTrace tailWord_485664 prefixEnd_485664 49260062930428260951403 := by
  unfold tailWord_485664
  simp only [CollatzResearch.WordTrace]
  refine ⟨8856810656264873826368023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11809080875019831768490697 8856810656264873826368023)
  ·
    refine ⟨13285215984397310739552035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8856810656264873826368023 13285215984397310739552035)
    ·
      refine ⟨19927823976595966109328053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13285215984397310739552035 19927823976595966109328053)
      ·
        refine ⟨1868233497805871822749505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19927823976595966109328053 1868233497805871822749505)
        ·
          refine ⟨1401175123354403867062129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1868233497805871822749505 1401175123354403867062129)
          ·
            refine ⟨1050881342515802900296597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1401175123354403867062129 1050881342515802900296597)
            ·
              refine ⟨49260062930428260951403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1050881342515802900296597 49260062930428260951403)
              ·
                rfl

theorem cell19_485664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 6].length) (baseStart_485664 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_485664 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_485664 prefixEnd_485664 := by exact prefixLift 485664
  have htrace : WordTrace (prefixWord ++ tailWord_485664) baseStart_485664 baseEnd_485664 := by
    simpa [prefixWord, tailWord_485664, baseEnd_485664] using wordTrace_append hprefix tailTrace_485664
  have hstable : (prefixWord ++ tailWord_485664).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485664).length < 2 ^ (prefixWord ++ tailWord_485664).sum := by decide
  have hdescent : baseEnd_485664 < baseStart_485664 := by decide
  rcases family_descends (prefixWord ++ tailWord_485664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485738 : List Nat := [3, 1, 3, 3, 1, 2, 2, 4]
def baseStart_485738 : Nat := 118140960795 + 485738 * 2 ^ 59
def prefixEnd_485738 : Nat := 4983230072969 + 3 ^ 40 * 485738 * 2
def baseEnd_485738 : Nat := 147802705868874537209563

theorem tailTrace_485738 : CollatzResearch.WordTrace tailWord_485738 prefixEnd_485738 147802705868874537209563 := by
  unfold tailWord_485738
  simp only [CollatzResearch.WordTrace]
  refine ⟨4429080078565414572732467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11810880209507772193953245 4429080078565414572732467)
  ·
    refine ⟨6643620117848121859098701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4429080078565414572732467 6643620117848121859098701)
    ·
      refine ⟨2491357544193045697162013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6643620117848121859098701 2491357544193045697162013)
      ·
        refine ⟨934259079072392136435755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2491357544193045697162013 934259079072392136435755)
        ·
          refine ⟨1401388618608588204653633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 934259079072392136435755 1401388618608588204653633)
          ·
            refine ⟨1051041463956441153490225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1401388618608588204653633 1051041463956441153490225)
            ·
              refine ⟨788281097967330865117669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1051041463956441153490225 788281097967330865117669)
              ·
                refine ⟨147802705868874537209563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 788281097967330865117669 147802705868874537209563)
                ·
                  rfl

theorem cell19_485738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 4].length) (baseStart_485738 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_485738 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_485738 prefixEnd_485738 := by exact prefixLift 485738
  have htrace : WordTrace (prefixWord ++ tailWord_485738) baseStart_485738 baseEnd_485738 := by
    simpa [prefixWord, tailWord_485738, baseEnd_485738] using wordTrace_append hprefix tailTrace_485738
  have hstable : (prefixWord ++ tailWord_485738).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485738).length < 2 ^ (prefixWord ++ tailWord_485738).sum := by decide
  have hdescent : baseEnd_485738 < baseStart_485738 := by decide
  rcases family_descends (prefixWord ++ tailWord_485738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485793 : List Nat := [1, 2, 3, 5, 1, 2, 1, 4]
def baseStart_485793 : Nat := 118140960795 + 485793 * 2 ^ 59
def prefixEnd_485793 : Nat := 4983230072969 + 3 ^ 40 * 485793 * 2
def baseEnd_485793 : Nat := 147819441534650705987191

theorem tailTrace_485793 : CollatzResearch.WordTrace tailWord_485793 prefixEnd_485793 147819441534650705987191 := by
  unfold tailWord_485793
  simp only [CollatzResearch.WordTrace]
  refine ⟨17718326329062402684182033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11812217552708268456121355 17718326329062402684182033)
  ·
    refine ⟨13288744746796802013136525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17718326329062402684182033 13288744746796802013136525)
    ·
      refine ⟨4983279280048800754926197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13288744746796802013136525 4983279280048800754926197)
      ·
        refine ⟨467182432504575070774331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4983279280048800754926197 467182432504575070774331)
        ·
          refine ⟨700773648756862606161497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 467182432504575070774331 700773648756862606161497)
          ·
            refine ⟨525580236567646954621123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 700773648756862606161497 525580236567646954621123)
            ·
              refine ⟨788370354851470431931685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 525580236567646954621123 788370354851470431931685)
              ·
                refine ⟨147819441534650705987191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 788370354851470431931685 147819441534650705987191)
                ·
                  rfl

theorem cell19_485793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 4].length) (baseStart_485793 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_485793 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_485793 prefixEnd_485793 := by exact prefixLift 485793
  have htrace : WordTrace (prefixWord ++ tailWord_485793) baseStart_485793 baseEnd_485793 := by
    simpa [prefixWord, tailWord_485793, baseEnd_485793] using wordTrace_append hprefix tailTrace_485793
  have hstable : (prefixWord ++ tailWord_485793).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485793).length < 2 ^ (prefixWord ++ tailWord_485793).sum := by decide
  have hdescent : baseEnd_485793 < baseStart_485793 := by decide
  rcases family_descends (prefixWord ++ tailWord_485793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485818 : List Nat := [3, 1, 1, 1, 2, 1, 1, 9]
def baseStart_485818 : Nat := 118140960795 + 485818 * 2 ^ 59
def prefixEnd_485818 : Nat := 4983230072969 + 3 ^ 40 * 485818 * 2
def baseEnd_485818 : Nat := 147827048655458055431567

theorem tailTrace_485818 : CollatzResearch.WordTrace tailWord_485818 prefixEnd_485818 147827048655458055431567 := by
  unfold tailWord_485818
  simp only [CollatzResearch.WordTrace]
  refine ⟨4429809538492957988460527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11812825435981221302561405 4429809538492957988460527)
  ·
    refine ⟨6644714307739436982690791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4429809538492957988460527 6644714307739436982690791)
    ·
      refine ⟨9967071461609155474036187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6644714307739436982690791 9967071461609155474036187)
      ·
        refine ⟨14950607192413733211054281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9967071461609155474036187 14950607192413733211054281)
        ·
          refine ⟨11212955394310299908290711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14950607192413733211054281 11212955394310299908290711)
          ·
            refine ⟨16819433091465449862436067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11212955394310299908290711 16819433091465449862436067)
            ·
              refine ⟨25229149637198174793654101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16819433091465449862436067 25229149637198174793654101)
              ·
                refine ⟨147827048655458055431567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25229149637198174793654101 147827048655458055431567)
                ·
                  rfl

theorem cell19_485818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 9].length) (baseStart_485818 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_485818 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_485818 prefixEnd_485818 := by exact prefixLift 485818
  have htrace : WordTrace (prefixWord ++ tailWord_485818) baseStart_485818 baseEnd_485818 := by
    simpa [prefixWord, tailWord_485818, baseEnd_485818] using wordTrace_append hprefix tailTrace_485818
  have hstable : (prefixWord ++ tailWord_485818).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485818).length < 2 ^ (prefixWord ++ tailWord_485818).sum := by decide
  have hdescent : baseEnd_485818 < baseStart_485818 := by decide
  rcases family_descends (prefixWord ++ tailWord_485818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485856 : List Nat := [2, 1, 1, 3, 1, 1, 4, 6]
def baseStart_485856 : Nat := 118140960795 + 485856 * 2 ^ 59
def prefixEnd_485856 : Nat := 4983230072969 + 3 ^ 40 * 485856 * 2
def baseEnd_485856 : Nat := 147838611479085226587019

theorem tailTrace_485856 : CollatzResearch.WordTrace tailWord_485856 prefixEnd_485856 147838611479085226587019 := by
  unfold tailWord_485856
  simp only [CollatzResearch.WordTrace]
  refine ⟨8860312063917082221862711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11813749418556109629150281 8860312063917082221862711)
  ·
    refine ⟨13290468095875623332794067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8860312063917082221862711 13290468095875623332794067)
    ·
      refine ⟨19935702143813434999191101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13290468095875623332794067 19935702143813434999191101)
      ·
        refine ⟨7475888303930038124696663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19935702143813434999191101 7475888303930038124696663)
        ·
          refine ⟨11213832455895057187044995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7475888303930038124696663 11213832455895057187044995)
          ·
            refine ⟨16820748683842585780567493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11213832455895057187044995 16820748683842585780567493)
            ·
              refine ⟨3153890378220484833856405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16820748683842585780567493 3153890378220484833856405)
              ·
                refine ⟨147838611479085226587019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3153890378220484833856405 147838611479085226587019)
                ·
                  rfl

theorem cell19_485856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 6].length) (baseStart_485856 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_485856 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_485856 prefixEnd_485856 := by exact prefixLift 485856
  have htrace : WordTrace (prefixWord ++ tailWord_485856) baseStart_485856 baseEnd_485856 := by
    simpa [prefixWord, tailWord_485856, baseEnd_485856] using wordTrace_append hprefix tailTrace_485856
  have hstable : (prefixWord ++ tailWord_485856).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485856).length < 2 ^ (prefixWord ++ tailWord_485856).sum := by decide
  have hdescent : baseEnd_485856 < baseStart_485856 := by decide
  rcases family_descends (prefixWord ++ tailWord_485856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485869 : List Nat := [1, 5, 1, 3, 1, 3, 2, 3]
def baseStart_485869 : Nat := 118140960795 + 485869 * 2 ^ 59
def prefixEnd_485869 : Nat := 4983230072969 + 3 ^ 40 * 485869 * 2
def baseEnd_485869 : Nat := 147842567181905048298095

theorem tailTrace_485869 : CollatzResearch.WordTrace tailWord_485869 prefixEnd_485869 147842567181905048298095 := by
  unfold tailWord_485869
  simp only [CollatzResearch.WordTrace]
  refine ⟨17721098276787067663948661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11814065517858045109299107 17721098276787067663948661)
  ·
    refine ⟨1661352963448787593495187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17721098276787067663948661 1661352963448787593495187)
    ·
      refine ⟨2492029445173181390242781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1661352963448787593495187 2492029445173181390242781)
      ·
        refine ⟨934511041939943021341043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2492029445173181390242781 934511041939943021341043)
        ·
          refine ⟨1401766562909914532011565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 934511041939943021341043 1401766562909914532011565)
          ·
            refine ⟨525662461091217949504337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1401766562909914532011565 525662461091217949504337)
            ·
              refine ⟨394246845818413462128253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 525662461091217949504337 394246845818413462128253)
              ·
                refine ⟨147842567181905048298095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 394246845818413462128253 147842567181905048298095)
                ·
                  rfl

theorem cell19_485869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 2, 3].length) (baseStart_485869 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_485869 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_485869 prefixEnd_485869 := by exact prefixLift 485869
  have htrace : WordTrace (prefixWord ++ tailWord_485869) baseStart_485869 baseEnd_485869 := by
    simpa [prefixWord, tailWord_485869, baseEnd_485869] using wordTrace_append hprefix tailTrace_485869
  have hstable : (prefixWord ++ tailWord_485869).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485869).length < 2 ^ (prefixWord ++ tailWord_485869).sum := by decide
  have hdescent : baseEnd_485869 < baseStart_485869 := by decide
  rcases family_descends (prefixWord ++ tailWord_485869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485875 : List Nat := [1, 1, 1, 2, 2, 2, 5, 5]
def baseStart_485875 : Nat := 118140960795 + 485875 * 2 ^ 59
def prefixEnd_485875 : Nat := 4983230072969 + 3 ^ 40 * 485875 * 2
def baseEnd_485875 : Nat := 147844392890898812164745

theorem tailTrace_485875 : CollatzResearch.WordTrace tailWord_485875 prefixEnd_485875 147844392890898812164745 := by
  unfold tailWord_485875
  simp only [CollatzResearch.WordTrace]
  refine ⟨17721317114765330688667079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11814211409843553792444719 17721317114765330688667079)
  ·
    refine ⟨26581975672147996033000619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17721317114765330688667079 26581975672147996033000619)
    ·
      refine ⟨39872963508221994049500929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26581975672147996033000619 39872963508221994049500929)
      ·
        refine ⟨29904722631166495537125697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39872963508221994049500929 29904722631166495537125697)
        ·
          refine ⟨22428541973374871652844273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29904722631166495537125697 22428541973374871652844273)
          ·
            refine ⟨16821406480031153739633205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22428541973374871652844273 16821406480031153739633205)
            ·
              refine ⟨1577006857502920663090613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16821406480031153739633205 1577006857502920663090613)
              ·
                refine ⟨147844392890898812164745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1577006857502920663090613 147844392890898812164745)
                ·
                  rfl

theorem cell19_485875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 5].length) (baseStart_485875 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_485875 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_485875 prefixEnd_485875 := by exact prefixLift 485875
  have htrace : WordTrace (prefixWord ++ tailWord_485875) baseStart_485875 baseEnd_485875 := by
    simpa [prefixWord, tailWord_485875, baseEnd_485875] using wordTrace_append hprefix tailTrace_485875
  have hstable : (prefixWord ++ tailWord_485875).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485875).length < 2 ^ (prefixWord ++ tailWord_485875).sum := by decide
  have hdescent : baseEnd_485875 < baseStart_485875 := by decide
  rcases family_descends (prefixWord ++ tailWord_485875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485892 : List Nat := [2, 3, 2, 3, 1, 1, 7]
def baseStart_485892 : Nat := 118140960795 + 485892 * 2 ^ 59
def prefixEnd_485892 : Nat := 4983230072969 + 3 ^ 40 * 485892 * 2
def baseEnd_485892 : Nat := 49283188577682603262307

theorem tailTrace_485892 : CollatzResearch.WordTrace tailWord_485892 prefixEnd_485892 49283188577682603262307 := by
  unfold tailWord_485892
  simp only [CollatzResearch.WordTrace]
  refine ⟨8860968577851871296017965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11814624770469161728023953 8860968577851871296017965)
  ·
    refine ⟨3322863216694451736006737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8860968577851871296017965 3322863216694451736006737)
    ·
      refine ⟨2492147412520838802005053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3322863216694451736006737 2492147412520838802005053)
      ·
        refine ⟨934555279695314550751895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2492147412520838802005053 934555279695314550751895)
        ·
          refine ⟨1401832919542971826127843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 934555279695314550751895 1401832919542971826127843)
          ·
            refine ⟨2102749379314457739191765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1401832919542971826127843 2102749379314457739191765)
            ·
              refine ⟨49283188577682603262307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2102749379314457739191765 49283188577682603262307)
              ·
                rfl

theorem cell19_485892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 7].length) (baseStart_485892 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_485892 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_485892 prefixEnd_485892 := by exact prefixLift 485892
  have htrace : WordTrace (prefixWord ++ tailWord_485892) baseStart_485892 baseEnd_485892 := by
    simpa [prefixWord, tailWord_485892, baseEnd_485892] using wordTrace_append hprefix tailTrace_485892
  have hstable : (prefixWord ++ tailWord_485892).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485892).length < 2 ^ (prefixWord ++ tailWord_485892).sum := by decide
  have hdescent : baseEnd_485892 < baseStart_485892 := by decide
  rcases family_descends (prefixWord ++ tailWord_485892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485930 : List Nat := [3, 1, 4, 1, 1, 2, 2, 5]
def baseStart_485930 : Nat := 118140960795 + 485930 * 2 ^ 59
def prefixEnd_485930 : Nat := 4983230072969 + 3 ^ 40 * 485930 * 2
def baseEnd_485930 : Nat := 147861128556674980942373

theorem tailTrace_485930 : CollatzResearch.WordTrace tailWord_485930 prefixEnd_485930 147861128556674980942373 := by
  unfold tailWord_485930
  simp only [CollatzResearch.WordTrace]
  refine ⟨4430830782391518770479811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11815548753044050054612829 4430830782391518770479811)
  ·
    refine ⟨6646246173587278155719717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4430830782391518770479811 6646246173587278155719717)
    ·
      refine ⟨1246171157547614654197447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6646246173587278155719717 1246171157547614654197447)
      ·
        refine ⟨1869256736321421981296171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1246171157547614654197447 1869256736321421981296171)
        ·
          refine ⟨2803885104482132971944257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1869256736321421981296171 2803885104482132971944257)
          ·
            refine ⟨2102913828361599728958193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2803885104482132971944257 2102913828361599728958193)
            ·
              refine ⟨1577185371271199796718645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2102913828361599728958193 1577185371271199796718645)
              ·
                refine ⟨147861128556674980942373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1577185371271199796718645 147861128556674980942373)
                ·
                  rfl

theorem cell19_485930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 5].length) (baseStart_485930 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_485930 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_485930 prefixEnd_485930 := by exact prefixLift 485930
  have htrace : WordTrace (prefixWord ++ tailWord_485930) baseStart_485930 baseEnd_485930 := by
    simpa [prefixWord, tailWord_485930, baseEnd_485930] using wordTrace_append hprefix tailTrace_485930
  have hstable : (prefixWord ++ tailWord_485930).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485930).length < 2 ^ (prefixWord ++ tailWord_485930).sum := by decide
  have hdescent : baseEnd_485930 < baseStart_485930 := by decide
  rcases family_descends (prefixWord ++ tailWord_485930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485987 : List Nat := [1, 1, 1, 5, 1, 2, 5, 3]
def baseStart_485987 : Nat := 118140960795 + 485987 * 2 ^ 59
def prefixEnd_485987 : Nat := 4983230072969 + 3 ^ 40 * 485987 * 2
def baseEnd_485987 : Nat := 147878472792115737675551

theorem tailTrace_485987 : CollatzResearch.WordTrace tailWord_485987 prefixEnd_485987 147878472792115737675551 := by
  unfold tailWord_485987
  simp only [CollatzResearch.WordTrace]
  refine ⟨17725402090359573816744215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11816934726906382544496143 17725402090359573816744215)
  ·
    refine ⟨26588103135539360725116323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17725402090359573816744215 26588103135539360725116323)
    ·
      refine ⟨39882154703309041087674485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26588103135539360725116323 39882154703309041087674485)
      ·
        refine ⟨3738952003435222601969483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39882154703309041087674485 3738952003435222601969483)
        ·
          refine ⟨5608428005152833902954225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3738952003435222601969483 5608428005152833902954225)
          ·
            refine ⟨4206321003864625427215669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5608428005152833902954225 4206321003864625427215669)
            ·
              refine ⟨394342594112308633801469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4206321003864625427215669 394342594112308633801469)
              ·
                refine ⟨147878472792115737675551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 394342594112308633801469 147878472792115737675551)
                ·
                  rfl

theorem cell19_485987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 5, 3].length) (baseStart_485987 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_485987 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_485987 prefixEnd_485987 := by exact prefixLift 485987
  have htrace : WordTrace (prefixWord ++ tailWord_485987) baseStart_485987 baseEnd_485987 := by
    simpa [prefixWord, tailWord_485987, baseEnd_485987] using wordTrace_append hprefix tailTrace_485987
  have hstable : (prefixWord ++ tailWord_485987).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485987).length < 2 ^ (prefixWord ++ tailWord_485987).sum := by decide
  have hdescent : baseEnd_485987 < baseStart_485987 := by decide
  rcases family_descends (prefixWord ++ tailWord_485987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486042 : List Nat := [3, 1, 1, 6, 1, 1, 1, 5]
def baseStart_486042 : Nat := 118140960795 + 486042 * 2 ^ 59
def prefixEnd_486042 : Nat := 4983230072969 + 3 ^ 40 * 486042 * 2
def baseEnd_486042 : Nat := 147895208457891906453179

theorem tailTrace_486042 : CollatzResearch.WordTrace tailWord_486042 prefixEnd_486042 147895208457891906453179 := by
  unfold tailWord_486042
  simp only [CollatzResearch.WordTrace]
  refine ⟨4431852026290079552499095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11818272070106878806664253 4431852026290079552499095)
  ·
    refine ⟨6647778039435119328748643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4431852026290079552499095 6647778039435119328748643)
    ·
      refine ⟨9971667059152678993122965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6647778039435119328748643 9971667059152678993122965)
      ·
        refine ⟨467421893397781827802639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 9971667059152678993122965 467421893397781827802639)
        ·
          refine ⟨701132840096672741703959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 467421893397781827802639 701132840096672741703959)
          ·
            refine ⟨1051699260145009112555939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 701132840096672741703959 1051699260145009112555939)
            ·
              refine ⟨1577548890217513668833909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1051699260145009112555939 1577548890217513668833909)
              ·
                refine ⟨147895208457891906453179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1577548890217513668833909 147895208457891906453179)
                ·
                  rfl

theorem cell19_486042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 5].length) (baseStart_486042 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_486042 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_486042 prefixEnd_486042 := by exact prefixLift 486042
  have htrace : WordTrace (prefixWord ++ tailWord_486042) baseStart_486042 baseEnd_486042 := by
    simpa [prefixWord, tailWord_486042, baseEnd_486042] using wordTrace_append hprefix tailTrace_486042
  have hstable : (prefixWord ++ tailWord_486042).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486042).length < 2 ^ (prefixWord ++ tailWord_486042).sum := by decide
  have hdescent : baseEnd_486042 < baseStart_486042 := by decide
  rcases family_descends (prefixWord ++ tailWord_486042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486044 : List Nat := [2, 2, 3, 2, 2, 2, 1, 5]
def baseStart_486044 : Nat := 118140960795 + 486044 * 2 ^ 59
def prefixEnd_486044 : Nat := 4983230072969 + 3 ^ 40 * 486044 * 2
def baseEnd_486044 : Nat := 147895817027556494408729

theorem tailTrace_486044 : CollatzResearch.WordTrace tailWord_486044 prefixEnd_486044 147895817027556494408729 := by
  unfold tailWord_486044
  simp only [CollatzResearch.WordTrace]
  refine ⟨8863740525576536275784593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11818320700768715034379457 8863740525576536275784593)
  ·
    refine ⟨6647805394182402206838445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8863740525576536275784593 6647805394182402206838445)
    ·
      refine ⟨2492927022818400827564417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6647805394182402206838445 2492927022818400827564417)
      ·
        refine ⟨1869695267113800620673313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2492927022818400827564417 1869695267113800620673313)
        ·
          refine ⟨1402271450335350465504985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1869695267113800620673313 1402271450335350465504985)
          ·
            refine ⟨1051703587751512849128739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1402271450335350465504985 1051703587751512849128739)
            ·
              refine ⟨1577555381627269273693109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1051703587751512849128739 1577555381627269273693109)
              ·
                refine ⟨147895817027556494408729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1577555381627269273693109 147895817027556494408729)
                ·
                  rfl

theorem cell19_486044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 5].length) (baseStart_486044 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_486044 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_486044 prefixEnd_486044 := by exact prefixLift 486044
  have htrace : WordTrace (prefixWord ++ tailWord_486044) baseStart_486044 baseEnd_486044 := by
    simpa [prefixWord, tailWord_486044, baseEnd_486044] using wordTrace_append hprefix tailTrace_486044
  have hstable : (prefixWord ++ tailWord_486044).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486044).length < 2 ^ (prefixWord ++ tailWord_486044).sum := by decide
  have hdescent : baseEnd_486044 < baseStart_486044 := by decide
  rcases family_descends (prefixWord ++ tailWord_486044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486103 : List Nat := [1, 1, 3, 2, 1, 4, 2, 5]
def baseStart_486103 : Nat := 118140960795 + 486103 * 2 ^ 59
def prefixEnd_486103 : Nat := 4983230072969 + 3 ^ 40 * 486103 * 2
def baseEnd_486103 : Nat := 147913769832661839097457

theorem tailTrace_486103 : CollatzResearch.WordTrace tailWord_486103 prefixEnd_486103 147913769832661839097457 := by
  unfold tailWord_486103
  simp only [CollatzResearch.WordTrace]
  refine ⟨17729632957939325627966963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11819755305292883751977975 17729632957939325627966963)
  ·
    refine ⟨26594449436908988441950445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17729632957939325627966963 26594449436908988441950445)
    ·
      refine ⟨9972918538840870665731417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26594449436908988441950445 9972918538840870665731417)
      ·
        refine ⟨7479688904130652999298563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9972918538840870665731417 7479688904130652999298563)
        ·
          refine ⟨11219533356195979498947845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7479688904130652999298563 11219533356195979498947845)
          ·
            refine ⟨2103662504286746156052721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11219533356195979498947845 2103662504286746156052721)
            ·
              refine ⟨1577746878215059617039541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2103662504286746156052721 1577746878215059617039541)
              ·
                refine ⟨147913769832661839097457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1577746878215059617039541 147913769832661839097457)
                ·
                  rfl

theorem cell19_486103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 5].length) (baseStart_486103 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_486103 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_486103 prefixEnd_486103 := by exact prefixLift 486103
  have htrace : WordTrace (prefixWord ++ tailWord_486103) baseStart_486103 baseEnd_486103 := by
    simpa [prefixWord, tailWord_486103, baseEnd_486103] using wordTrace_append hprefix tailTrace_486103
  have hstable : (prefixWord ++ tailWord_486103).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486103).length < 2 ^ (prefixWord ++ tailWord_486103).sum := by decide
  have hdescent : baseEnd_486103 < baseStart_486103 := by decide
  rcases family_descends (prefixWord ++ tailWord_486103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486120 : List Nat := [2, 1, 4, 1, 5, 6]
def baseStart_486120 : Nat := 118140960795 + 486120 * 2 ^ 59
def prefixEnd_486120 : Nat := 4983230072969 + 3 ^ 40 * 486120 * 2
def baseEnd_486120 : Nat := 16435438074978981857737

theorem tailTrace_486120 : CollatzResearch.WordTrace tailWord_486120 prefixEnd_486120 16435438074978981857737 := by
  unfold tailWord_486120
  simp only [CollatzResearch.WordTrace]
  refine ⟨8865126499438868765667907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11820168665918491687557209 8865126499438868765667907)
  ·
    refine ⟨13297689749158303148501861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8865126499438868765667907 13297689749158303148501861)
    ·
      refine ⟨2493316827967181840344099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13297689749158303148501861 2493316827967181840344099)
      ·
        refine ⟨3739975241950772760516149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2493316827967181840344099 3739975241950772760516149)
        ·
          refine ⟨350622678932884946298389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3739975241950772760516149 350622678932884946298389)
          ·
            refine ⟨16435438074978981857737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 350622678932884946298389 16435438074978981857737)
            ·
              rfl

theorem cell19_486120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 6].length) (baseStart_486120 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_486120 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_486120 prefixEnd_486120 := by exact prefixLift 486120
  have htrace : WordTrace (prefixWord ++ tailWord_486120) baseStart_486120 baseEnd_486120 := by
    simpa [prefixWord, tailWord_486120, baseEnd_486120] using wordTrace_append hprefix tailTrace_486120
  have hstable : (prefixWord ++ tailWord_486120).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486120).length < 2 ^ (prefixWord ++ tailWord_486120).sum := by decide
  have hdescent : baseEnd_486120 < baseStart_486120 := by decide
  rcases family_descends (prefixWord ++ tailWord_486120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486133 : List Nat := [1, 3, 6, 1, 1, 2, 1, 4]
def baseStart_486133 : Nat := 118140960795 + 486133 * 2 ^ 59
def prefixEnd_486133 : Nat := 4983230072969 + 3 ^ 40 * 486133 * 2
def baseEnd_486133 : Nat := 147922898377630658430709

theorem tailTrace_486133 : CollatzResearch.WordTrace tailWord_486133 prefixEnd_486133 147922898377630658430709 := by
  unfold tailWord_486133
  simp only [CollatzResearch.WordTrace]
  refine ⟨17730727147830640751559053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11820484765220427167706035 17730727147830640751559053)
  ·
    refine ⟨6649022680436490281834645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17730727147830640751559053 6649022680436490281834645)
    ·
      refine ⟨311672938145460481960999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 6649022680436490281834645 311672938145460481960999)
      ·
        refine ⟨467509407218190722941499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311672938145460481960999 467509407218190722941499)
        ·
          refine ⟨701264110827286084412249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 467509407218190722941499 701264110827286084412249)
          ·
            refine ⟨525948083120464563309187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 701264110827286084412249 525948083120464563309187)
            ·
              refine ⟨788922124680696844963781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 525948083120464563309187 788922124680696844963781)
              ·
                refine ⟨147922898377630658430709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 788922124680696844963781 147922898377630658430709)
                ·
                  rfl

theorem cell19_486133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 4].length) (baseStart_486133 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_486133 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_486133 prefixEnd_486133 := by exact prefixLift 486133
  have htrace : WordTrace (prefixWord ++ tailWord_486133) baseStart_486133 baseEnd_486133 := by
    simpa [prefixWord, tailWord_486133, baseEnd_486133] using wordTrace_append hprefix tailTrace_486133
  have hstable : (prefixWord ++ tailWord_486133).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486133).length < 2 ^ (prefixWord ++ tailWord_486133).sum := by decide
  have hdescent : baseEnd_486133 < baseStart_486133 := by decide
  rcases family_descends (prefixWord ++ tailWord_486133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486209 : List Nat := [1, 2, 5, 3, 2, 1, 2, 3]
def baseStart_486209 : Nat := 118140960795 + 486209 * 2 ^ 59
def prefixEnd_486209 : Nat := 4983230072969 + 3 ^ 40 * 486209 * 2
def baseEnd_486209 : Nat := 147946024024885000741613

theorem tailTrace_486209 : CollatzResearch.WordTrace tailWord_486209 prefixEnd_486209 147946024024885000741613 := by
  unfold tailWord_486209
  simp only [CollatzResearch.WordTrace]
  refine ⟨17733499095555305731325681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11822332730370203820883787 17733499095555305731325681)
  ·
    refine ⟨13300124321666479298494261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17733499095555305731325681 13300124321666479298494261)
    ·
      refine ⟨1246886655156232434233837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13300124321666479298494261 1246886655156232434233837)
      ·
        refine ⟨467582495683587162837689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1246886655156232434233837 467582495683587162837689)
        ·
          refine ⟨350686871762690372128267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 467582495683587162837689 350686871762690372128267)
          ·
            refine ⟨526030307644035558192401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 350686871762690372128267 526030307644035558192401)
            ·
              refine ⟨394522730733026668644301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 526030307644035558192401 394522730733026668644301)
              ·
                refine ⟨147946024024885000741613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 394522730733026668644301 147946024024885000741613)
                ·
                  rfl

theorem cell19_486209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 2, 3].length) (baseStart_486209 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_486209 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_486209 prefixEnd_486209 := by exact prefixLift 486209
  have htrace : WordTrace (prefixWord ++ tailWord_486209) baseStart_486209 baseEnd_486209 := by
    simpa [prefixWord, tailWord_486209, baseEnd_486209] using wordTrace_append hprefix tailTrace_486209
  have hstable : (prefixWord ++ tailWord_486209).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486209).length < 2 ^ (prefixWord ++ tailWord_486209).sum := by decide
  have hdescent : baseEnd_486209 < baseStart_486209 := by decide
  rcases family_descends (prefixWord ++ tailWord_486209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486217 : List Nat := [1, 2, 1, 1, 2, 6, 1, 5]
def baseStart_486217 : Nat := 118140960795 + 486217 * 2 ^ 59
def prefixEnd_486217 : Nat := 4983230072969 + 3 ^ 40 * 486217 * 2
def baseEnd_486217 : Nat := 147948458303543352563813

theorem tailTrace_486217 : CollatzResearch.WordTrace tailWord_486217 prefixEnd_486217 147948458303543352563813 := by
  unfold tailWord_486217
  simp only [CollatzResearch.WordTrace]
  refine ⟨17733790879526323097616905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11822527253017548731744603 17733790879526323097616905)
  ·
    refine ⟨13300343159644742323212679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17733790879526323097616905 13300343159644742323212679)
    ·
      refine ⟨19950514739467113484819019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13300343159644742323212679 19950514739467113484819019)
      ·
        refine ⟨29925772109200670227228529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19950514739467113484819019 29925772109200670227228529)
        ·
          refine ⟨22444329081900502670421397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29925772109200670227228529 22444329081900502670421397)
          ·
            refine ⟨1052077925714086062676003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 22444329081900502670421397 1052077925714086062676003)
            ·
              refine ⟨1578116888571129094014005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1052077925714086062676003 1578116888571129094014005)
              ·
                refine ⟨147948458303543352563813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1578116888571129094014005 147948458303543352563813)
                ·
                  rfl

theorem cell19_486217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 5].length) (baseStart_486217 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_486217 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_486217 prefixEnd_486217 := by exact prefixLift 486217
  have htrace : WordTrace (prefixWord ++ tailWord_486217) baseStart_486217 baseEnd_486217 := by
    simpa [prefixWord, tailWord_486217, baseEnd_486217] using wordTrace_append hprefix tailTrace_486217
  have hstable : (prefixWord ++ tailWord_486217).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486217).length < 2 ^ (prefixWord ++ tailWord_486217).sum := by decide
  have hdescent : baseEnd_486217 < baseStart_486217 := by decide
  rcases family_descends (prefixWord ++ tailWord_486217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486329 : List Nat := [1, 2, 1, 4, 2, 3, 3, 3]
def baseStart_486329 : Nat := 118140960795 + 486329 * 2 ^ 59
def prefixEnd_486329 : Nat := 4983230072969 + 3 ^ 40 * 486329 * 2
def baseEnd_486329 : Nat := 147982538204760278074619

theorem tailTrace_486329 : CollatzResearch.WordTrace tailWord_486329 prefixEnd_486329 147982538204760278074619 := by
  unfold tailWord_486329
  simp only [CollatzResearch.WordTrace]
  refine ⟨17737875855120566225694041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11825250570080377483796027 17737875855120566225694041)
  ·
    refine ⟨13303406891340424669270531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17737875855120566225694041 13303406891340424669270531)
    ·
      refine ⟨19955110337010637003905797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13303406891340424669270531 19955110337010637003905797)
      ·
        refine ⟨3741583188189494438232337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19955110337010637003905797 3741583188189494438232337)
        ·
          refine ⟨2806187391142120828674253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3741583188189494438232337 2806187391142120828674253)
          ·
            refine ⟨1052320271678295310752845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2806187391142120828674253 1052320271678295310752845)
            ·
              refine ⟨394620101879360741532317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1052320271678295310752845 394620101879360741532317)
              ·
                refine ⟨147982538204760278074619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 394620101879360741532317 147982538204760278074619)
                ·
                  rfl

theorem cell19_486329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 3, 3].length) (baseStart_486329 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_486329 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_486329 prefixEnd_486329 := by exact prefixLift 486329
  have htrace : WordTrace (prefixWord ++ tailWord_486329) baseStart_486329 baseEnd_486329 := by
    simpa [prefixWord, tailWord_486329, baseEnd_486329] using wordTrace_append hprefix tailTrace_486329
  have hstable : (prefixWord ++ tailWord_486329).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486329).length < 2 ^ (prefixWord ++ tailWord_486329).sum := by decide
  have hdescent : baseEnd_486329 < baseStart_486329 := by decide
  rcases family_descends (prefixWord ++ tailWord_486329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486342 : List Nat := [6, 1, 3, 1, 1, 1, 6]
def baseStart_486342 : Nat := 118140960795 + 486342 * 2 ^ 59
def prefixEnd_486342 : Nat := 4983230072969 + 3 ^ 40 * 486342 * 2
def baseEnd_486342 : Nat := 49328831302526699928565

theorem tailTrace_486342 : CollatzResearch.WordTrace tailWord_486342 prefixEnd_486342 49328831302526699928565 := by
  unfold tailWord_486342
  simp only [CollatzResearch.WordTrace]
  refine ⟨554323437627295920184915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 11825566669382312963944853 554323437627295920184915)
  ·
    refine ⟨831485156440943880277373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 554323437627295920184915 831485156440943880277373)
    ·
      refine ⟨311806933665353955104015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 831485156440943880277373 311806933665353955104015)
      ·
        refine ⟨467710400498030932656023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311806933665353955104015 467710400498030932656023)
        ·
          refine ⟨701565600747046398984035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 467710400498030932656023 701565600747046398984035)
          ·
            refine ⟨1052348401120569598476053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 701565600747046398984035 1052348401120569598476053)
            ·
              refine ⟨49328831302526699928565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1052348401120569598476053 49328831302526699928565)
              ·
                rfl

theorem cell19_486342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 6].length) (baseStart_486342 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_486342 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_486342 prefixEnd_486342 := by exact prefixLift 486342
  have htrace : WordTrace (prefixWord ++ tailWord_486342) baseStart_486342 baseEnd_486342 := by
    simpa [prefixWord, tailWord_486342, baseEnd_486342] using wordTrace_append hprefix tailTrace_486342
  have hstable : (prefixWord ++ tailWord_486342).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486342).length < 2 ^ (prefixWord ++ tailWord_486342).sum := by decide
  have hdescent : baseEnd_486342 < baseStart_486342 := by decide
  rcases family_descends (prefixWord ++ tailWord_486342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486350 : List Nat := [4, 1, 1, 1, 2, 4, 6]
def baseStart_486350 : Nat := 118140960795 + 486350 * 2 ^ 59
def prefixEnd_486350 : Nat := 4983230072969 + 3 ^ 40 * 486350 * 2
def baseEnd_486350 : Nat := 49329642728746150535965

theorem tailTrace_486350 : CollatzResearch.WordTrace tailWord_486350 prefixEnd_486350 49329642728746150535965 := by
  unfold tailWord_486350
  simp only [CollatzResearch.WordTrace]
  refine ⟨2217330223505560851526063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11825761192029657874805669 2217330223505560851526063)
  ·
    refine ⟨3325995335258341277289095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2217330223505560851526063 3325995335258341277289095)
    ·
      refine ⟨4988993002887511915933643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3325995335258341277289095 4988993002887511915933643)
      ·
        refine ⟨7483489504331267873900465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4988993002887511915933643 7483489504331267873900465)
        ·
          refine ⟨5612617128248450905425349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7483489504331267873900465 5612617128248450905425349)
          ·
            refine ⟨1052365711546584544767253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5612617128248450905425349 1052365711546584544767253)
            ·
              refine ⟨49329642728746150535965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1052365711546584544767253 49329642728746150535965)
              ·
                rfl

theorem cell19_486350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 6].length) (baseStart_486350 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_486350 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_486350 prefixEnd_486350 := by exact prefixLift 486350
  have htrace : WordTrace (prefixWord ++ tailWord_486350) baseStart_486350 baseEnd_486350 := by
    simpa [prefixWord, tailWord_486350, baseEnd_486350] using wordTrace_append hprefix tailTrace_486350
  have hstable : (prefixWord ++ tailWord_486350).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486350).length < 2 ^ (prefixWord ++ tailWord_486350).sum := by decide
  have hdescent : baseEnd_486350 < baseStart_486350 := by decide
  rcases family_descends (prefixWord ++ tailWord_486350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486382 : List Nat := [4, 1, 2, 1, 5, 1, 2, 3]
def baseStart_486382 : Nat := 118140960795 + 486382 * 2 ^ 59
def prefixEnd_486382 : Nat := 4983230072969 + 3 ^ 40 * 486382 * 2
def baseEnd_486382 : Nat := 147998665300871858896697

theorem tailTrace_486382 : CollatzResearch.WordTrace tailWord_486382 prefixEnd_486382 147998665300871858896697 := by
  unfold tailWord_486382
  simp only [CollatzResearch.WordTrace]
  refine ⟨2217476115491069534671675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11826539282619037518248933 2217476115491069534671675)
  ·
    refine ⟨3326214173236604302007513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2217476115491069534671675 3326214173236604302007513)
    ·
      refine ⟨2494660629927453226505635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3326214173236604302007513 2494660629927453226505635)
      ·
        refine ⟨3741990944891179839758453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2494660629927453226505635 3741990944891179839758453)
        ·
          refine ⟨350811651083548109977355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3741990944891179839758453 350811651083548109977355)
          ·
            refine ⟨526217476625322164966033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 350811651083548109977355 526217476625322164966033)
            ·
              refine ⟨394663107468991623724525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 526217476625322164966033 394663107468991623724525)
              ·
                refine ⟨147998665300871858896697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 394663107468991623724525 147998665300871858896697)
                ·
                  rfl

theorem cell19_486382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 2, 3].length) (baseStart_486382 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_486382 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_486382 prefixEnd_486382 := by exact prefixLift 486382
  have htrace : WordTrace (prefixWord ++ tailWord_486382) baseStart_486382 baseEnd_486382 := by
    simpa [prefixWord, tailWord_486382, baseEnd_486382] using wordTrace_append hprefix tailTrace_486382
  have hstable : (prefixWord ++ tailWord_486382).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486382).length < 2 ^ (prefixWord ++ tailWord_486382).sum := by decide
  have hdescent : baseEnd_486382 < baseStart_486382 := by decide
  rcases family_descends (prefixWord ++ tailWord_486382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486426 : List Nat := [3, 1, 1, 3, 1, 2, 4, 4]
def baseStart_486426 : Nat := 118140960795 + 486426 * 2 ^ 59
def prefixEnd_486426 : Nat := 4983230072969 + 3 ^ 40 * 486426 * 2
def baseEnd_486426 : Nat := 148012053833492793918799

theorem tailTrace_486426 : CollatzResearch.WordTrace tailWord_486426 prefixEnd_486426 148012053833492793918799 := by
  unfold tailWord_486426
  simp only [CollatzResearch.WordTrace]
  refine ⟨4435353433942287947993783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11827609157179434527983421 4435353433942287947993783)
  ·
    refine ⟨6653030150913431921990675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4435353433942287947993783 6653030150913431921990675)
    ·
      refine ⟨9979545226370147882986013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6653030150913431921990675 9979545226370147882986013)
      ·
        refine ⟨3742329459888805456119755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9979545226370147882986013 3742329459888805456119755)
        ·
          refine ⟨5613494189833208184179633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3742329459888805456119755 5613494189833208184179633)
          ·
            refine ⟨4210120642374906138134725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5613494189833208184179633 4210120642374906138134725)
            ·
              refine ⟨789397620445294900900261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4210120642374906138134725 789397620445294900900261)
              ·
                refine ⟨148012053833492793918799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 789397620445294900900261 148012053833492793918799)
                ·
                  rfl

theorem cell19_486426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 4].length) (baseStart_486426 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_486426 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_486426 prefixEnd_486426 := by exact prefixLift 486426
  have htrace : WordTrace (prefixWord ++ tailWord_486426) baseStart_486426 baseEnd_486426 := by
    simpa [prefixWord, tailWord_486426, baseEnd_486426] using wordTrace_append hprefix tailTrace_486426
  have hstable : (prefixWord ++ tailWord_486426).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486426).length < 2 ^ (prefixWord ++ tailWord_486426).sum := by decide
  have hdescent : baseEnd_486426 < baseStart_486426 := by decide
  rcases family_descends (prefixWord ++ tailWord_486426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486498 : List Nat := [3, 3, 2, 2, 1, 2, 3, 3]
def baseStart_486498 : Nat := 118140960795 + 486498 * 2 ^ 59
def prefixEnd_486498 : Nat := 4983230072969 + 3 ^ 40 * 486498 * 2
def baseEnd_486498 : Nat := 148033962341417960318603

theorem tailTrace_486498 : CollatzResearch.WordTrace tailWord_486498 prefixEnd_486498 148033962341417960318603 := by
  unfold tailWord_486498
  simp only [CollatzResearch.WordTrace]
  refine ⟨4436009947877077022149037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11829359861005538725730765 4436009947877077022149037)
  ·
    refine ⟨1663503730453903883305889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4436009947877077022149037 1663503730453903883305889)
    ·
      refine ⟨1247627797840427912479417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1663503730453903883305889 1247627797840427912479417)
      ·
        refine ⟨935720848380320934359563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1247627797840427912479417 935720848380320934359563)
        ·
          refine ⟨1403581272570481401539345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 935720848380320934359563 1403581272570481401539345)
          ·
            refine ⟨1052685954427861051154509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1403581272570481401539345 1052685954427861051154509)
            ·
              refine ⟨394757232910447894182941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1052685954427861051154509 394757232910447894182941)
              ·
                refine ⟨148033962341417960318603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 394757232910447894182941 148033962341417960318603)
                ·
                  rfl

theorem cell19_486498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 3, 3].length) (baseStart_486498 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_486498 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_486498 prefixEnd_486498 := by exact prefixLift 486498
  have htrace : WordTrace (prefixWord ++ tailWord_486498) baseStart_486498 baseEnd_486498 := by
    simpa [prefixWord, tailWord_486498, baseEnd_486498] using wordTrace_append hprefix tailTrace_486498
  have hstable : (prefixWord ++ tailWord_486498).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486498).length < 2 ^ (prefixWord ++ tailWord_486498).sum := by decide
  have hdescent : baseEnd_486498 < baseStart_486498 := by decide
  rcases family_descends (prefixWord ++ tailWord_486498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486521 : List Nat := [1, 2, 1, 3, 5, 1, 6]
def baseStart_486521 : Nat := 118140960795 + 486521 * 2 ^ 59
def prefixEnd_486521 : Nat := 4983230072969 + 3 ^ 40 * 486521 * 2
def baseEnd_486521 : Nat := 49346986964186907269143

theorem tailTrace_486521 : CollatzResearch.WordTrace tailWord_486521 prefixEnd_486521 49346986964186907269143 := by
  unfold tailWord_486521
  simp only [CollatzResearch.WordTrace]
  refine ⟨17744878670424983016683417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11829919113616655344455611 17744878670424983016683417)
  ·
    refine ⟨13308659002818737262512563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17744878670424983016683417 13308659002818737262512563)
    ·
      refine ⟨19962988504228105893768845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13308659002818737262512563 19962988504228105893768845)
      ·
        refine ⟨7486120689085539710163317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19962988504228105893768845 7486120689085539710163317)
        ·
          refine ⟨701823814601769347827811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7486120689085539710163317 701823814601769347827811)
          ·
            refine ⟨1052735721902654021741717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 701823814601769347827811 1052735721902654021741717)
            ·
              refine ⟨49346986964186907269143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1052735721902654021741717 49346986964186907269143)
              ·
                rfl

theorem cell19_486521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 6].length) (baseStart_486521 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_486521 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_486521 prefixEnd_486521 := by exact prefixLift 486521
  have htrace : WordTrace (prefixWord ++ tailWord_486521) baseStart_486521 baseEnd_486521 := by
    simpa [prefixWord, tailWord_486521, baseEnd_486521] using wordTrace_append hprefix tailTrace_486521
  have hstable : (prefixWord ++ tailWord_486521).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486521).length < 2 ^ (prefixWord ++ tailWord_486521).sum := by decide
  have hdescent : baseEnd_486521 < baseStart_486521 := by decide
  rcases family_descends (prefixWord ++ tailWord_486521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486578 : List Nat := [3, 2, 1, 1, 1, 6, 5]
def baseStart_486578 : Nat := 118140960795 + 486578 * 2 ^ 59
def prefixEnd_486578 : Nat := 4983230072969 + 3 ^ 40 * 486578 * 2
def baseEnd_486578 : Nat := 49352768376000492846869

theorem tailTrace_486578 : CollatzResearch.WordTrace tailWord_486578 prefixEnd_486578 49352768376000492846869 := by
  unfold tailWord_486578
  simp only [CollatzResearch.WordTrace]
  refine ⟨4436739407804620437877097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11831305087478987834338925 4436739407804620437877097)
  ·
    refine ⟨3327554555853465328407823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4436739407804620437877097 3327554555853465328407823)
    ·
      refine ⟨4991331833780197992611735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3327554555853465328407823 4991331833780197992611735)
      ·
        refine ⟨7486997750670296988917603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4991331833780197992611735 7486997750670296988917603)
        ·
          refine ⟨11230496626005445483376405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7486997750670296988917603 11230496626005445483376405)
          ·
            refine ⟨526429529344005257033269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 11230496626005445483376405 526429529344005257033269)
            ·
              refine ⟨49352768376000492846869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 526429529344005257033269 49352768376000492846869)
              ·
                rfl

theorem cell19_486578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 5].length) (baseStart_486578 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_486578 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_486578 prefixEnd_486578 := by exact prefixLift 486578
  have htrace : WordTrace (prefixWord ++ tailWord_486578) baseStart_486578 baseEnd_486578 := by
    simpa [prefixWord, tailWord_486578, baseEnd_486578] using wordTrace_append hprefix tailTrace_486578
  have hstable : (prefixWord ++ tailWord_486578).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486578).length < 2 ^ (prefixWord ++ tailWord_486578).sum := by decide
  have hdescent : baseEnd_486578 < baseStart_486578 := by decide
  rcases family_descends (prefixWord ++ tailWord_486578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486652 : List Nat := [2, 2, 2, 1, 5, 2, 1, 4]
def baseStart_486652 : Nat := 118140960795 + 486652 * 2 ^ 59
def prefixEnd_486652 : Nat := 4983230072969 + 3 ^ 40 * 486652 * 2
def baseEnd_486652 : Nat := 148080822205591232895961

theorem tailTrace_486652 : CollatzResearch.WordTrace tailWord_486652 prefixEnd_486652 148080822205591232895961 := by
  unfold tailWord_486652
  simp only [CollatzResearch.WordTrace]
  refine ⟨8874828316475196194851105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11833104421966928259801473 8874828316475196194851105)
  ·
    refine ⟨6656121237356397146138329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8874828316475196194851105 6656121237356397146138329)
    ·
      refine ⟨4992090928017297859603747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6656121237356397146138329 4992090928017297859603747)
      ·
        refine ⟨7488136392025946789405621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4992090928017297859603747 7488136392025946789405621)
        ·
          refine ⟨702012786752432511506777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7488136392025946789405621 702012786752432511506777)
          ·
            refine ⟨526509590064324383630083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 702012786752432511506777 526509590064324383630083)
            ·
              refine ⟨789764385096486575445125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 526509590064324383630083 789764385096486575445125)
              ·
                refine ⟨148080822205591232895961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 789764385096486575445125 148080822205591232895961)
                ·
                  rfl

theorem cell19_486652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 4].length) (baseStart_486652 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_486652 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_486652 prefixEnd_486652 := by exact prefixLift 486652
  have htrace : WordTrace (prefixWord ++ tailWord_486652) baseStart_486652 baseEnd_486652 := by
    simpa [prefixWord, tailWord_486652, baseEnd_486652] using wordTrace_append hprefix tailTrace_486652
  have hstable : (prefixWord ++ tailWord_486652).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486652).length < 2 ^ (prefixWord ++ tailWord_486652).sum := by decide
  have hdescent : baseEnd_486652 < baseStart_486652 := by decide
  rcases family_descends (prefixWord ++ tailWord_486652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486673 : List Nat := [1, 2, 2, 1, 1, 4, 5, 3]
def baseStart_486673 : Nat := 118140960795 + 486673 * 2 ^ 59
def prefixEnd_486673 : Nat := 4983230072969 + 3 ^ 40 * 486673 * 2
def baseEnd_486673 : Nat := 148087212187069406429237

theorem tailTrace_486673 : CollatzResearch.WordTrace tailWord_486673 prefixEnd_486673 148087212187069406429237 := by
  unfold tailWord_486673
  simp only [CollatzResearch.WordTrace]
  refine ⟨17750422565874312976216673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11833615043916208650811115 17750422565874312976216673)
  ·
    refine ⟨13312816924405734732162505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17750422565874312976216673 13312816924405734732162505)
    ·
      refine ⟨9984612693304301049121879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13312816924405734732162505 9984612693304301049121879)
      ·
        refine ⟨14976919039956451573682819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9984612693304301049121879 14976919039956451573682819)
        ·
          refine ⟨22465378559934677360524229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14976919039956451573682819 22465378559934677360524229)
          ·
            refine ⟨4212258479987752005098293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22465378559934677360524229 4212258479987752005098293)
            ·
              refine ⟨394899232498851750477965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4212258479987752005098293 394899232498851750477965)
              ·
                refine ⟨148087212187069406429237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 394899232498851750477965 148087212187069406429237)
                ·
                  rfl

theorem cell19_486673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 5, 3].length) (baseStart_486673 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_486673 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_486673 prefixEnd_486673 := by exact prefixLift 486673
  have htrace : WordTrace (prefixWord ++ tailWord_486673) baseStart_486673 baseEnd_486673 := by
    simpa [prefixWord, tailWord_486673, baseEnd_486673] using wordTrace_append hprefix tailTrace_486673
  have hstable : (prefixWord ++ tailWord_486673).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486673).length < 2 ^ (prefixWord ++ tailWord_486673).sum := by decide
  have hdescent : baseEnd_486673 < baseStart_486673 := by decide
  rcases family_descends (prefixWord ++ tailWord_486673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486789 : List Nat := [1, 3, 1, 1, 3, 1, 4, 5]
def baseStart_486789 : Nat := 118140960795 + 486789 * 2 ^ 59
def prefixEnd_486789 : Nat := 4983230072969 + 3 ^ 40 * 486789 * 2
def baseEnd_486789 : Nat := 148122509227615507851143

theorem tailTrace_486789 : CollatzResearch.WordTrace tailWord_486789 prefixEnd_486789 148122509227615507851143 := by
  unfold tailWord_486789
  simp only [CollatzResearch.WordTrace]
  refine ⟨17754653433454064787439421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11836435622302709858292947 17754653433454064787439421)
  ·
    refine ⟨6657995037545274295289783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17754653433454064787439421 6657995037545274295289783)
    ·
      refine ⟨9986992556317911442934675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6657995037545274295289783 9986992556317911442934675)
      ·
        refine ⟨14980488834476867164402013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9986992556317911442934675 14980488834476867164402013)
        ·
          refine ⟨5617683312928825186650755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14980488834476867164402013 5617683312928825186650755)
          ·
            refine ⟨8426524969393237779976133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5617683312928825186650755 8426524969393237779976133)
            ·
              refine ⟨1579973431761232083745525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8426524969393237779976133 1579973431761232083745525)
              ·
                refine ⟨148122509227615507851143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1579973431761232083745525 148122509227615507851143)
                ·
                  rfl

theorem cell19_486789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 5].length) (baseStart_486789 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_486789 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_486789 prefixEnd_486789 := by exact prefixLift 486789
  have htrace : WordTrace (prefixWord ++ tailWord_486789) baseStart_486789 baseEnd_486789 := by
    simpa [prefixWord, tailWord_486789, baseEnd_486789] using wordTrace_append hprefix tailTrace_486789
  have hstable : (prefixWord ++ tailWord_486789).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486789).length < 2 ^ (prefixWord ++ tailWord_486789).sum := by decide
  have hdescent : baseEnd_486789 < baseStart_486789 := by decide
  rcases family_descends (prefixWord ++ tailWord_486789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486808 : List Nat := [2, 1, 2, 5, 9]
def baseStart_486808 : Nat := 118140960795 + 486808 * 2 ^ 59
def prefixEnd_486808 : Nat := 4983230072969 + 3 ^ 40 * 486808 * 2
def baseEnd_486808 : Nat := 5486232986645521978847

theorem tailTrace_486808 : CollatzResearch.WordTrace tailWord_486808 prefixEnd_486808 5486232986645521978847 := by
  unfold tailWord_486808
  simp only [CollatzResearch.WordTrace]
  refine ⟨8877673210192615516190539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11836897613590154021587385 8877673210192615516190539)
  ·
    refine ⟨13316509815288923274285809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8877673210192615516190539 13316509815288923274285809)
    ·
      refine ⟨9987382361466692455714357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13316509815288923274285809 9987382361466692455714357)
      ·
        refine ⟨936317096387502417723221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9987382361466692455714357 936317096387502417723221)
        ·
          refine ⟨5486232986645521978847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 936317096387502417723221 5486232986645521978847)
          ·
            rfl

theorem cell19_486808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 9].length) (baseStart_486808 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_486808 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_486808 prefixEnd_486808 := by exact prefixLift 486808
  have htrace : WordTrace (prefixWord ++ tailWord_486808) baseStart_486808 baseEnd_486808 := by
    simpa [prefixWord, tailWord_486808, baseEnd_486808] using wordTrace_append hprefix tailTrace_486808
  have hstable : (prefixWord ++ tailWord_486808).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486808).length < 2 ^ (prefixWord ++ tailWord_486808).sum := by decide
  have hdescent : baseEnd_486808 < baseStart_486808 := by decide
  rcases family_descends (prefixWord ++ tailWord_486808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486922 : List Nat := [3, 1, 2, 2, 2, 2, 7]
def baseStart_486922 : Nat := 118140960795 + 486922 * 2 ^ 59
def prefixEnd_486922 : Nat := 4983230072969 + 3 ^ 40 * 486922 * 2
def baseEnd_486922 : Nat := 49387659703436868965075

theorem tailTrace_486922 : CollatzResearch.WordTrace tailWord_486922 prefixEnd_486922 49387659703436868965075 := by
  unfold tailWord_486922
  simp only [CollatzResearch.WordTrace]
  refine ⟨4439876085493057125507755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11839669561314819001354013 4439876085493057125507755)
  ·
    refine ⟨6659814128239585688261633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4439876085493057125507755 6659814128239585688261633)
    ·
      refine ⟨4994860596179689266196225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6659814128239585688261633 4994860596179689266196225)
      ·
        refine ⟨3746145447134766949647169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4994860596179689266196225 3746145447134766949647169)
        ·
          refine ⟨2809609085351075212235377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3746145447134766949647169 2809609085351075212235377)
          ·
            refine ⟨2107206814013306409176533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2809609085351075212235377 2107206814013306409176533)
            ·
              refine ⟨49387659703436868965075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2107206814013306409176533 49387659703436868965075)
              ·
                rfl

theorem cell19_486922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 7].length) (baseStart_486922 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_486922 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_486922 prefixEnd_486922 := by exact prefixLift 486922
  have htrace : WordTrace (prefixWord ++ tailWord_486922) baseStart_486922 baseEnd_486922 := by
    simpa [prefixWord, tailWord_486922, baseEnd_486922] using wordTrace_append hprefix tailTrace_486922
  have hstable : (prefixWord ++ tailWord_486922).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486922).length < 2 ^ (prefixWord ++ tailWord_486922).sum := by decide
  have hdescent : baseEnd_486922 < baseStart_486922 := by decide
  rcases family_descends (prefixWord ++ tailWord_486922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486958 : List Nat := [4, 1, 3, 1, 2, 1, 2, 5]
def baseStart_486958 : Nat := 118140960795 + 486958 * 2 ^ 59
def prefixEnd_486958 : Nat := 4983230072969 + 3 ^ 40 * 486958 * 2
def baseEnd_486958 : Nat := 148173933364273190095127

theorem tailTrace_486958 : CollatzResearch.WordTrace tailWord_486958 prefixEnd_486958 148173933364273190095127 := by
  unfold tailWord_486958
  simp only [CollatzResearch.WordTrace]
  refine ⟨2220102171230225831292691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11840544913227871100227685 2220102171230225831292691)
  ·
    refine ⟨3330153256845338746939037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2220102171230225831292691 3330153256845338746939037)
    ·
      refine ⟨1248807471317002030102139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3330153256845338746939037 1248807471317002030102139)
      ·
        refine ⟨1873211206975503045153209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1248807471317002030102139 1873211206975503045153209)
        ·
          refine ⟨1404908405231627283864907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1873211206975503045153209 1404908405231627283864907)
          ·
            refine ⟨2107362607847440925797361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1404908405231627283864907 2107362607847440925797361)
            ·
              refine ⟨1580521955885580694348021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2107362607847440925797361 1580521955885580694348021)
              ·
                refine ⟨148173933364273190095127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1580521955885580694348021 148173933364273190095127)
                ·
                  rfl

theorem cell19_486958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_486958 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_486958 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_486958 prefixEnd_486958 := by exact prefixLift 486958
  have htrace : WordTrace (prefixWord ++ tailWord_486958) baseStart_486958 baseEnd_486958 := by
    simpa [prefixWord, tailWord_486958, baseEnd_486958] using wordTrace_append hprefix tailTrace_486958
  have hstable : (prefixWord ++ tailWord_486958).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486958).length < 2 ^ (prefixWord ++ tailWord_486958).sum := by decide
  have hdescent : baseEnd_486958 < baseStart_486958 := by decide
  rcases family_descends (prefixWord ++ tailWord_486958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487068 : List Nat := [2, 2, 3, 2, 4, 1, 2, 3]
def baseStart_487068 : Nat := 118140960795 + 487068 * 2 ^ 59
def prefixEnd_487068 : Nat := 4983230072969 + 3 ^ 40 * 487068 * 2
def baseEnd_487068 : Nat := 148207404695825527650383

theorem tailTrace_487068 : CollatzResearch.WordTrace tailWord_487068 prefixEnd_487068 148207404695825527650383 := by
  unfold tailWord_487068
  simp only [CollatzResearch.WordTrace]
  refine ⟨8882414699721647718422929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11843219599628863624563905 8882414699721647718422929)
  ·
    refine ⟨6661811024791235788817197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8882414699721647718422929 6661811024791235788817197)
    ·
      refine ⟨2498179134296713420806449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6661811024791235788817197 2498179134296713420806449)
      ·
        refine ⟨1873634350722535065604837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2498179134296713420806449 1873634350722535065604837)
        ·
          refine ⟨351306440760475324800907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1873634350722535065604837 351306440760475324800907)
          ·
            refine ⟨526959661140712987201361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 351306440760475324800907 526959661140712987201361)
            ·
              refine ⟨395219745855534740401021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 526959661140712987201361 395219745855534740401021)
              ·
                refine ⟨148207404695825527650383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 395219745855534740401021 148207404695825527650383)
                ·
                  rfl

theorem cell19_487068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 2, 3].length) (baseStart_487068 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_487068 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_487068 prefixEnd_487068 := by exact prefixLift 487068
  have htrace : WordTrace (prefixWord ++ tailWord_487068) baseStart_487068 baseEnd_487068 := by
    simpa [prefixWord, tailWord_487068, baseEnd_487068] using wordTrace_append hprefix tailTrace_487068
  have hstable : (prefixWord ++ tailWord_487068).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487068).length < 2 ^ (prefixWord ++ tailWord_487068).sum := by decide
  have hdescent : baseEnd_487068 < baseStart_487068 := by decide
  rcases family_descends (prefixWord ++ tailWord_487068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487070 : List Nat := [4, 3, 1, 1, 1, 2, 4, 3]
def baseStart_487070 : Nat := 118140960795 + 487070 * 2 ^ 59
def prefixEnd_487070 : Nat := 4983230072969 + 3 ^ 40 * 487070 * 2
def baseEnd_487070 : Nat := 148208013265490115605933

theorem tailTrace_487070 : CollatzResearch.WordTrace tailWord_487070 prefixEnd_487070 148208013265490115605933 := by
  unfold tailWord_487070
  simp only [CollatzResearch.WordTrace]
  refine ⟨2220612793179506222302333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11843268230290699852279109 2220612793179506222302333)
  ·
    refine ⟨832729797442314833363375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2220612793179506222302333 832729797442314833363375)
    ·
      refine ⟨1249094696163472250045063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 832729797442314833363375 1249094696163472250045063)
      ·
        refine ⟨1873642044245208375067595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1249094696163472250045063 1873642044245208375067595)
        ·
          refine ⟨2810463066367812562601393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1873642044245208375067595 2810463066367812562601393)
          ·
            refine ⟨2107847299775859421951045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2810463066367812562601393 2107847299775859421951045)
            ·
              refine ⟨395221368707973641615821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2107847299775859421951045 395221368707973641615821)
              ·
                refine ⟨148208013265490115605933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 395221368707973641615821 148208013265490115605933)
                ·
                  rfl

theorem cell19_487070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 4, 3].length) (baseStart_487070 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_487070 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_487070 prefixEnd_487070 := by exact prefixLift 487070
  have htrace : WordTrace (prefixWord ++ tailWord_487070) baseStart_487070 baseEnd_487070 := by
    simpa [prefixWord, tailWord_487070, baseEnd_487070] using wordTrace_append hprefix tailTrace_487070
  have hstable : (prefixWord ++ tailWord_487070).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487070).length < 2 ^ (prefixWord ++ tailWord_487070).sum := by decide
  have hdescent : baseEnd_487070 < baseStart_487070 := by decide
  rcases family_descends (prefixWord ++ tailWord_487070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487072 : List Nat := [2, 1, 1, 4, 3, 1, 4, 3]
def baseStart_487072 : Nat := 118140960795 + 487072 * 2 ^ 59
def prefixEnd_487072 : Nat := 4983230072969 + 3 ^ 40 * 487072 * 2
def baseEnd_487072 : Nat := 148208621835154703561483

theorem tailTrace_487072 : CollatzResearch.WordTrace tailWord_487072 prefixEnd_487072 148208621835154703561483 := by
  unfold tailWord_487072
  simp only [CollatzResearch.WordTrace]
  refine ⟨8882487645714402059995735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11843316860952536079994313 8882487645714402059995735)
  ·
    refine ⟨13323731468571603089993603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8882487645714402059995735 13323731468571603089993603)
    ·
      refine ⟨19985597202857404634990405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13323731468571603089993603 19985597202857404634990405)
      ·
        refine ⟨3747299475535763369060701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19985597202857404634990405 3747299475535763369060701)
        ·
          refine ⟨1405237303325911263397763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3747299475535763369060701 1405237303325911263397763)
          ·
            refine ⟨2107855954988866895096645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1405237303325911263397763 2107855954988866895096645)
            ·
              refine ⟨395222991560412542830621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2107855954988866895096645 395222991560412542830621)
              ·
                refine ⟨148208621835154703561483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 395222991560412542830621 148208621835154703561483)
                ·
                  rfl

theorem cell19_487072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 4, 3].length) (baseStart_487072 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_487072 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_487072 prefixEnd_487072 := by exact prefixLift 487072
  have htrace : WordTrace (prefixWord ++ tailWord_487072) baseStart_487072 baseEnd_487072 := by
    simpa [prefixWord, tailWord_487072, baseEnd_487072] using wordTrace_append hprefix tailTrace_487072
  have hstable : (prefixWord ++ tailWord_487072).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487072).length < 2 ^ (prefixWord ++ tailWord_487072).sum := by decide
  have hdescent : baseEnd_487072 < baseStart_487072 := by decide
  rcases family_descends (prefixWord ++ tailWord_487072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487112 : List Nat := [2, 1, 3, 1, 2, 2, 4, 4]
def baseStart_487112 : Nat := 118140960795 + 487112 * 2 ^ 59
def prefixEnd_487112 : Nat := 4983230072969 + 3 ^ 40 * 487112 * 2
def baseEnd_487112 : Nat := 148220793228446462672485

theorem tailTrace_487112 : CollatzResearch.WordTrace tailWord_487112 prefixEnd_487112 148220793228446462672485 := by
  unfold tailWord_487112
  simp only [CollatzResearch.WordTrace]
  refine ⟨8883217105641945475723795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11844289474189260634298393 8883217105641945475723795)
  ·
    refine ⟨13324825658462918213585693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8883217105641945475723795 13324825658462918213585693)
    ·
      refine ⟨4996809621923594330094635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13324825658462918213585693 4996809621923594330094635)
      ·
        refine ⟨7495214432885391495141953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4996809621923594330094635 7495214432885391495141953)
        ·
          refine ⟨5621410824664043621356465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7495214432885391495141953 5621410824664043621356465)
          ·
            refine ⟨4216058118498032716017349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5621410824664043621356465 4216058118498032716017349)
            ·
              refine ⟨790510897218381134253253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4216058118498032716017349 790510897218381134253253)
              ·
                refine ⟨148220793228446462672485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 790510897218381134253253 148220793228446462672485)
                ·
                  rfl

theorem cell19_487112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 4].length) (baseStart_487112 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_487112 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_487112 prefixEnd_487112 := by exact prefixLift 487112
  have htrace : WordTrace (prefixWord ++ tailWord_487112) baseStart_487112 baseEnd_487112 := by
    simpa [prefixWord, tailWord_487112, baseEnd_487112] using wordTrace_append hprefix tailTrace_487112
  have hstable : (prefixWord ++ tailWord_487112).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487112).length < 2 ^ (prefixWord ++ tailWord_487112).sum := by decide
  have hdescent : baseEnd_487112 < baseStart_487112 := by decide
  rcases family_descends (prefixWord ++ tailWord_487112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487169 : List Nat := [1, 2, 4, 1, 1, 1, 5, 4]
def baseStart_487169 : Nat := 118140960795 + 487169 * 2 ^ 59
def prefixEnd_487169 : Nat := 4983230072969 + 3 ^ 40 * 487169 * 2
def baseEnd_487169 : Nat := 148238137463887219405663

theorem tailTrace_487169 : CollatzResearch.WordTrace tailWord_487169 prefixEnd_487169 148238137463887219405663 := by
  unfold tailWord_487169
  simp only [CollatzResearch.WordTrace]
  refine ⟨17768513172077389686272561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11845675448051593124181707 17768513172077389686272561)
  ·
    refine ⟨13326384879058042264704421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17768513172077389686272561 13326384879058042264704421)
    ·
      refine ⟨2498697164823382924632079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13326384879058042264704421 2498697164823382924632079)
      ·
        refine ⟨3748045747235074386948119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2498697164823382924632079 3748045747235074386948119)
        ·
          refine ⟨5622068620852611580422179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3748045747235074386948119 5622068620852611580422179)
          ·
            refine ⟨8433102931278917370633269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5622068620852611580422179 8433102931278917370633269)
            ·
              refine ⟨790603399807398503496869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8433102931278917370633269 790603399807398503496869)
              ·
                refine ⟨148238137463887219405663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 790603399807398503496869 148238137463887219405663)
                ·
                  rfl

theorem cell19_487169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 4].length) (baseStart_487169 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_487169 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_487169 prefixEnd_487169 := by exact prefixLift 487169
  have htrace : WordTrace (prefixWord ++ tailWord_487169) baseStart_487169 baseEnd_487169 := by
    simpa [prefixWord, tailWord_487169, baseEnd_487169] using wordTrace_append hprefix tailTrace_487169
  have hstable : (prefixWord ++ tailWord_487169).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487169).length < 2 ^ (prefixWord ++ tailWord_487169).sum := by decide
  have hdescent : baseEnd_487169 < baseStart_487169 := by decide
  rcases family_descends (prefixWord ++ tailWord_487169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487260 : List Nat := [2, 2, 4, 2, 3, 1, 5]
def baseStart_487260 : Nat := 118140960795 + 487260 * 2 ^ 59
def prefixEnd_487260 : Nat := 4983230072969 + 3 ^ 40 * 487260 * 2
def baseEnd_487260 : Nat := 49421942461208657127731

theorem tailTrace_487260 : CollatzResearch.WordTrace tailWord_487260 prefixEnd_487260 49421942461208657127731 := by
  unfold tailWord_487260
  simp only [CollatzResearch.WordTrace]
  refine ⟨8885916107373856113917617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11847888143165141485223489 8885916107373856113917617)
  ·
    refine ⟨6664437080530392085438213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8885916107373856113917617 6664437080530392085438213)
    ·
      refine ⟨1249581952599448516019665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6664437080530392085438213 1249581952599448516019665)
      ·
        refine ⟨937186464449586387014749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1249581952599448516019665 937186464449586387014749)
        ·
          refine ⟨351444924168594895130531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 937186464449586387014749 351444924168594895130531)
          ·
            refine ⟨527167386252892342695797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 351444924168594895130531 527167386252892342695797)
            ·
              refine ⟨49421942461208657127731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 527167386252892342695797 49421942461208657127731)
              ·
                rfl

theorem cell19_487260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 5].length) (baseStart_487260 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_487260 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_487260 prefixEnd_487260 := by exact prefixLift 487260
  have htrace : WordTrace (prefixWord ++ tailWord_487260) baseStart_487260 baseEnd_487260 := by
    simpa [prefixWord, tailWord_487260, baseEnd_487260] using wordTrace_append hprefix tailTrace_487260
  have hstable : (prefixWord ++ tailWord_487260).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487260).length < 2 ^ (prefixWord ++ tailWord_487260).sum := by decide
  have hdescent : baseEnd_487260 < baseStart_487260 := by decide
  rcases family_descends (prefixWord ++ tailWord_487260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487264 : List Nat := [2, 1, 1, 3, 3, 4, 5]
def baseStart_487264 : Nat := 118140960795 + 487264 * 2 ^ 59
def prefixEnd_487264 : Nat := 4983230072969 + 3 ^ 40 * 487264 * 2
def baseEnd_487264 : Nat := 49422348174318382431431

theorem tailTrace_487264 : CollatzResearch.WordTrace tailWord_487264 prefixEnd_487264 49422348174318382431431 := by
  unfold tailWord_487264
  simp only [CollatzResearch.WordTrace]
  refine ⟨8885989053366610455490423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11847985404488813940653897 8885989053366610455490423)
  ·
    refine ⟨13328983580049915683235635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8885989053366610455490423 13328983580049915683235635)
    ·
      refine ⟨19993475370074873524853453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13328983580049915683235635 19993475370074873524853453)
      ·
        refine ⟨7497553263778077571820045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19993475370074873524853453 7497553263778077571820045)
        ·
          refine ⟨2811582473916779089432517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7497553263778077571820045 2811582473916779089432517)
          ·
            refine ⟨527171713859396079268597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2811582473916779089432517 527171713859396079268597)
            ·
              refine ⟨49422348174318382431431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 527171713859396079268597 49422348174318382431431)
              ·
                rfl

theorem cell19_487264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 5].length) (baseStart_487264 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_487264 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_487264 prefixEnd_487264 := by exact prefixLift 487264
  have htrace : WordTrace (prefixWord ++ tailWord_487264) baseStart_487264 baseEnd_487264 := by
    simpa [prefixWord, tailWord_487264, baseEnd_487264] using wordTrace_append hprefix tailTrace_487264
  have hstable : (prefixWord ++ tailWord_487264).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487264).length < 2 ^ (prefixWord ++ tailWord_487264).sum := by decide
  have hdescent : baseEnd_487264 < baseStart_487264 := by decide
  rcases family_descends (prefixWord ++ tailWord_487264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487357 : List Nat := [1, 4, 1, 2, 3, 2, 3, 3]
def baseStart_487357 : Nat := 118140960795 + 487357 * 2 ^ 59
def prefixEnd_487357 : Nat := 4983230072969 + 3 ^ 40 * 487357 * 2
def baseEnd_487357 : Nat := 148295343012358487227373

theorem tailTrace_487357 : CollatzResearch.WordTrace tailWord_487357 prefixEnd_487357 148295343012358487227373 := by
  unfold tailWord_487357
  simp only [CollatzResearch.WordTrace]
  refine ⟨17775370095396297794116325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11850246730264198529410883 17775370095396297794116325)
  ·
    refine ⟨3332881892886805836396811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17775370095396297794116325 3332881892886805836396811)
    ·
      refine ⟨4999322839330208754595217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3332881892886805836396811 4999322839330208754595217)
      ·
        refine ⟨3749492129497656565946413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4999322839330208754595217 3749492129497656565946413)
        ·
          refine ⟨1406059548561621212229905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3749492129497656565946413 1406059548561621212229905)
          ·
            refine ⟨1054544661421215909172429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1406059548561621212229905 1054544661421215909172429)
            ·
              refine ⟨395454248032955965939661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1054544661421215909172429 395454248032955965939661)
              ·
                refine ⟨148295343012358487227373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 395454248032955965939661 148295343012358487227373)
                ·
                  rfl

theorem cell19_487357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 3, 3].length) (baseStart_487357 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_487357 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_487357 prefixEnd_487357 := by exact prefixLift 487357
  have htrace : WordTrace (prefixWord ++ tailWord_487357) baseStart_487357 baseEnd_487357 := by
    simpa [prefixWord, tailWord_487357, baseEnd_487357] using wordTrace_append hprefix tailTrace_487357
  have hstable : (prefixWord ++ tailWord_487357).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487357).length < 2 ^ (prefixWord ++ tailWord_487357).sum := by decide
  have hdescent : baseEnd_487357 < baseStart_487357 := by decide
  rcases family_descends (prefixWord ++ tailWord_487357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487359 : List Nat := [1, 1, 2, 2, 2, 1, 7, 3]
def baseStart_487359 : Nat := 118140960795 + 487359 * 2 ^ 59
def prefixEnd_487359 : Nat := 4983230072969 + 3 ^ 40 * 487359 * 2
def baseEnd_487359 : Nat := 148295951582023075182923

theorem tailTrace_487359 : CollatzResearch.WordTrace tailWord_487359 prefixEnd_487359 148295951582023075182923 := by
  unfold tailWord_487359
  simp only [CollatzResearch.WordTrace]
  refine ⟨17775443041389052135689131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11850295360926034757126087 17775443041389052135689131)
  ·
    refine ⟨26663164562083578203533697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17775443041389052135689131 26663164562083578203533697)
    ·
      refine ⟨19997373421562683652650273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26663164562083578203533697 19997373421562683652650273)
      ·
        refine ⟨14998030066172012739487705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19997373421562683652650273 14998030066172012739487705)
        ·
          refine ⟨11248522549629009554615779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14998030066172012739487705 11248522549629009554615779)
          ·
            refine ⟨16872783824443514331923669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11248522549629009554615779 16872783824443514331923669)
            ·
              refine ⟨395455870885394867154461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 16872783824443514331923669 395455870885394867154461)
              ·
                refine ⟨148295951582023075182923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 395455870885394867154461 148295951582023075182923)
                ·
                  rfl

theorem cell19_487359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 7, 3].length) (baseStart_487359 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_487359 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_487359 prefixEnd_487359 := by exact prefixLift 487359
  have htrace : WordTrace (prefixWord ++ tailWord_487359) baseStart_487359 baseEnd_487359 := by
    simpa [prefixWord, tailWord_487359, baseEnd_487359] using wordTrace_append hprefix tailTrace_487359
  have hstable : (prefixWord ++ tailWord_487359).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487359).length < 2 ^ (prefixWord ++ tailWord_487359).sum := by decide
  have hdescent : baseEnd_487359 < baseStart_487359 := by decide
  rcases family_descends (prefixWord ++ tailWord_487359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487414 : List Nat := [5, 1, 1, 1, 4, 1, 1, 5]
def baseStart_487414 : Nat := 118140960795 + 487414 * 2 ^ 59
def prefixEnd_487414 : Nat := 4983230072969 + 3 ^ 40 * 487414 * 2
def baseEnd_487414 : Nat := 148312687247799243960551

theorem tailTrace_487414 : CollatzResearch.WordTrace tailWord_487414 prefixEnd_487414 148312687247799243960551 := by
  unfold tailWord_487414
  simp only [CollatzResearch.WordTrace]
  refine ⟨1111090566011862283058831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11851632704126531019294197 1111090566011862283058831)
  ·
    refine ⟨1666635849017793424588247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1111090566011862283058831 1666635849017793424588247)
    ·
      refine ⟨2499953773526690136882371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1666635849017793424588247 2499953773526690136882371)
      ·
        refine ⟨3749930660290035205323557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2499953773526690136882371 3749930660290035205323557)
        ·
          refine ⟨703111998804381600998167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3749930660290035205323557 703111998804381600998167)
          ·
            refine ⟨1054667998206572401497251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 703111998804381600998167 1054667998206572401497251)
            ·
              refine ⟨1582001997309858602245877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1054667998206572401497251 1582001997309858602245877)
              ·
                refine ⟨148312687247799243960551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1582001997309858602245877 148312687247799243960551)
                ·
                  rfl

theorem cell19_487414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_487414 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_487414 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_487414 prefixEnd_487414 := by exact prefixLift 487414
  have htrace : WordTrace (prefixWord ++ tailWord_487414) baseStart_487414 baseEnd_487414 := by
    simpa [prefixWord, tailWord_487414, baseEnd_487414] using wordTrace_append hprefix tailTrace_487414
  have hstable : (prefixWord ++ tailWord_487414).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487414).length < 2 ^ (prefixWord ++ tailWord_487414).sum := by decide
  have hdescent : baseEnd_487414 < baseStart_487414 := by decide
  rcases family_descends (prefixWord ++ tailWord_487414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487416 : List Nat := [2, 1, 2, 1, 1, 3, 6, 3]
def baseStart_487416 : Nat := 118140960795 + 487416 * 2 ^ 59
def prefixEnd_487416 : Nat := 4983230072969 + 3 ^ 40 * 487416 * 2
def baseEnd_487416 : Nat := 148313295817463831916101

theorem tailTrace_487416 : CollatzResearch.WordTrace tailWord_487416 prefixEnd_487416 148313295817463831916101 := by
  unfold tailWord_487416
  simp only [CollatzResearch.WordTrace]
  refine ⟨8888761001091275435257051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11851681334788367247009401 8888761001091275435257051)
  ·
    refine ⟨13333141501636913152885577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8888761001091275435257051 13333141501636913152885577)
    ·
      refine ⟨9999856126227684864664183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13333141501636913152885577 9999856126227684864664183)
      ·
        refine ⟨14999784189341527296996275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9999856126227684864664183 14999784189341527296996275)
        ·
          refine ⟨22499676284012290945494413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14999784189341527296996275 22499676284012290945494413)
          ·
            refine ⟨8437378606504609104560405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22499676284012290945494413 8437378606504609104560405)
            ·
              refine ⟨395502122179903551776269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8437378606504609104560405 395502122179903551776269)
              ·
                refine ⟨148313295817463831916101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 395502122179903551776269 148313295817463831916101)
                ·
                  rfl

theorem cell19_487416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 6, 3].length) (baseStart_487416 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_487416 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_487416 prefixEnd_487416 := by exact prefixLift 487416
  have htrace : WordTrace (prefixWord ++ tailWord_487416) baseStart_487416 baseEnd_487416 := by
    simpa [prefixWord, tailWord_487416, baseEnd_487416] using wordTrace_append hprefix tailTrace_487416
  have hstable : (prefixWord ++ tailWord_487416).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487416).length < 2 ^ (prefixWord ++ tailWord_487416).sum := by decide
  have hdescent : baseEnd_487416 < baseStart_487416 := by decide
  rcases family_descends (prefixWord ++ tailWord_487416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487475 : List Nat := [1, 1, 1, 2, 4, 1, 4, 5]
def baseStart_487475 : Nat := 118140960795 + 487475 * 2 ^ 59
def prefixEnd_487475 : Nat := 4983230072969 + 3 ^ 40 * 487475 * 2
def baseEnd_487475 : Nat := 148331248622569176604829

theorem tailTrace_487475 : CollatzResearch.WordTrace tailWord_487475 prefixEnd_487475 148331248622569176604829 := by
  unfold tailWord_487475
  simp only [CollatzResearch.WordTrace]
  refine ⟨17779673908968803946911879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11853115939312535964607919 17779673908968803946911879)
  ·
    refine ⟨26669510863453205920367819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17779673908968803946911879 26669510863453205920367819)
    ·
      refine ⟨40004266295179808880551729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26669510863453205920367819 40004266295179808880551729)
      ·
        refine ⟨30003199721384856660413797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40004266295179808880551729 30003199721384856660413797)
        ·
          refine ⟨5625599947759660623827587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30003199721384856660413797 5625599947759660623827587)
          ·
            refine ⟨8438399921639490935741381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5625599947759660623827587 8438399921639490935741381)
            ·
              refine ⟨1582199985307404550451509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8438399921639490935741381 1582199985307404550451509)
              ·
                refine ⟨148331248622569176604829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1582199985307404550451509 148331248622569176604829)
                ·
                  rfl

theorem cell19_487475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 5].length) (baseStart_487475 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_487475 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_487475 prefixEnd_487475 := by exact prefixLift 487475
  have htrace : WordTrace (prefixWord ++ tailWord_487475) baseStart_487475 baseEnd_487475 := by
    simpa [prefixWord, tailWord_487475, baseEnd_487475] using wordTrace_append hprefix tailTrace_487475
  have hstable : (prefixWord ++ tailWord_487475).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487475).length < 2 ^ (prefixWord ++ tailWord_487475).sum := by decide
  have hdescent : baseEnd_487475 < baseStart_487475 := by decide
  rcases family_descends (prefixWord ++ tailWord_487475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487585 : List Nat := [1, 2, 3, 3, 1, 4, 2, 3]
def baseStart_487585 : Nat := 118140960795 + 487585 * 2 ^ 59
def prefixEnd_487585 : Nat := 4983230072969 + 3 ^ 40 * 487585 * 2
def baseEnd_487585 : Nat := 148364719954121514160085

theorem tailTrace_487585 : CollatzResearch.WordTrace tailWord_487585 prefixEnd_487585 148364719954121514160085 := by
  unfold tailWord_487585
  simp only [CollatzResearch.WordTrace]
  refine ⟨17783685938570292733416209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11855790625713528488944139 17783685938570292733416209)
  ·
    refine ⟨13337764453927719550062157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17783685938570292733416209 13337764453927719550062157)
    ·
      refine ⟨5001661670222894831273309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13337764453927719550062157 5001661670222894831273309)
      ·
        refine ⟨1875623126333585561727491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5001661670222894831273309 1875623126333585561727491)
        ·
          refine ⟨2813434689500378342591237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1875623126333585561727491 2813434689500378342591237)
          ·
            refine ⟨527519004281320939235857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2813434689500378342591237 527519004281320939235857)
            ·
              refine ⟨395639253210990704426893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 527519004281320939235857 395639253210990704426893)
              ·
                refine ⟨148364719954121514160085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 395639253210990704426893 148364719954121514160085)
                ·
                  rfl

theorem cell19_487585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 2, 3].length) (baseStart_487585 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_487585 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_487585 prefixEnd_487585 := by exact prefixLift 487585
  have htrace : WordTrace (prefixWord ++ tailWord_487585) baseStart_487585 baseEnd_487585 := by
    simpa [prefixWord, tailWord_487585, baseEnd_487585] using wordTrace_append hprefix tailTrace_487585
  have hstable : (prefixWord ++ tailWord_487585).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487585).length < 2 ^ (prefixWord ++ tailWord_487585).sum := by decide
  have hdescent : baseEnd_487585 < baseStart_487585 := by decide
  rcases family_descends (prefixWord ++ tailWord_487585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487589 : List Nat := [1, 3, 1, 2, 1, 3, 3, 5]
def baseStart_487589 : Nat := 118140960795 + 487589 * 2 ^ 59
def prefixEnd_487589 : Nat := 4983230072969 + 3 ^ 40 * 487589 * 2
def baseEnd_487589 : Nat := 148365937093450690071185

theorem tailTrace_487589 : CollatzResearch.WordTrace tailWord_487589 prefixEnd_487589 148365937093450690071185 := by
  unfold tailWord_487589
  simp only [CollatzResearch.WordTrace]
  refine ⟨17783831830555801416561821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11855887887037200944374547 17783831830555801416561821)
  ·
    refine ⟨6668936936458425531210683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17783831830555801416561821 6668936936458425531210683)
    ·
      refine ⟨10003405404687638296816025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6668936936458425531210683 10003405404687638296816025)
      ·
        refine ⟨7502554053515728722612019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10003405404687638296816025 7502554053515728722612019)
        ·
          refine ⟨11253831080273593083918029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7502554053515728722612019 11253831080273593083918029)
          ·
            refine ⟨4220186655102597406469261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11253831080273593083918029 4220186655102597406469261)
            ·
              refine ⟨1582569995663474027425973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4220186655102597406469261 1582569995663474027425973)
              ·
                refine ⟨148365937093450690071185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1582569995663474027425973 148365937093450690071185)
                ·
                  rfl

theorem cell19_487589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 5].length) (baseStart_487589 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_487589 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_487589 prefixEnd_487589 := by exact prefixLift 487589
  have htrace : WordTrace (prefixWord ++ tailWord_487589) baseStart_487589 baseEnd_487589 := by
    simpa [prefixWord, tailWord_487589, baseEnd_487589] using wordTrace_append hprefix tailTrace_487589
  have hstable : (prefixWord ++ tailWord_487589).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487589).length < 2 ^ (prefixWord ++ tailWord_487589).sum := by decide
  have hdescent : baseEnd_487589 < baseStart_487589 := by decide
  rcases family_descends (prefixWord ++ tailWord_487589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487627 : List Nat := [1, 1, 1, 1, 3, 2, 6, 4]
def baseStart_487627 : Nat := 118140960795 + 487627 * 2 ^ 59
def prefixEnd_487627 : Nat := 4983230072969 + 3 ^ 40 * 487627 * 2
def baseEnd_487627 : Nat := 148377499917077861226637

theorem tailTrace_487627 : CollatzResearch.WordTrace tailWord_487627 prefixEnd_487627 148377499917077861226637 := by
  unfold tailWord_487627
  simp only [CollatzResearch.WordTrace]
  refine ⟨17785217804418133906445135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11856811869612089270963423 17785217804418133906445135)
  ·
    refine ⟨26677826706627200859667703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17785217804418133906445135 26677826706627200859667703)
    ·
      refine ⟨40016740059940801289501555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26677826706627200859667703 40016740059940801289501555)
      ·
        refine ⟨60025110089911201934252333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40016740059940801289501555 60025110089911201934252333)
        ·
          refine ⟨22509416283716700725344625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60025110089911201934252333 22509416283716700725344625)
          ·
            refine ⟨16882062212787525544008469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22509416283716700725344625 16882062212787525544008469)
            ·
              refine ⟨791346666224415259875397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16882062212787525544008469 791346666224415259875397)
              ·
                refine ⟨148377499917077861226637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 791346666224415259875397 148377499917077861226637)
                ·
                  rfl

theorem cell19_487627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 4].length) (baseStart_487627 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_487627 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_487627 prefixEnd_487627 := by exact prefixLift 487627
  have htrace : WordTrace (prefixWord ++ tailWord_487627) baseStart_487627 baseEnd_487627 := by
    simpa [prefixWord, tailWord_487627, baseEnd_487627] using wordTrace_append hprefix tailTrace_487627
  have hstable : (prefixWord ++ tailWord_487627).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487627).length < 2 ^ (prefixWord ++ tailWord_487627).sum := by decide
  have hdescent : baseEnd_487627 < baseStart_487627 := by decide
  rcases family_descends (prefixWord ++ tailWord_487627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487720 : List Nat := [2, 1, 5, 1, 3, 1, 6]
def baseStart_487720 : Nat := 118140960795 + 487720 * 2 ^ 59
def prefixEnd_487720 : Nat := 4983230072969 + 3 ^ 40 * 487720 * 2
def baseEnd_487720 : Nat := 49468599468827067053239

theorem tailTrace_487720 : CollatzResearch.WordTrace tailWord_487720 prefixEnd_487720 49468599468827067053239 := by
  unfold tailWord_487720
  simp only [CollatzResearch.WordTrace]
  refine ⟨8894304896540605394790307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11859073195387473859720409 8894304896540605394790307)
  ·
    refine ⟨13341457344810908092185461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8894304896540605394790307 13341457344810908092185461)
    ·
      refine ⟨1250761626076022633642387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13341457344810908092185461 1250761626076022633642387)
      ·
        refine ⟨1876142439114033950463581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1250761626076022633642387 1876142439114033950463581)
        ·
          refine ⟨703553414667762731423843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1876142439114033950463581 703553414667762731423843)
          ·
            refine ⟨1055330122001644097135765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 703553414667762731423843 1055330122001644097135765)
            ·
              refine ⟨49468599468827067053239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1055330122001644097135765 49468599468827067053239)
              ·
                rfl

theorem cell19_487720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 6].length) (baseStart_487720 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_487720 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_487720 prefixEnd_487720 := by exact prefixLift 487720
  have htrace : WordTrace (prefixWord ++ tailWord_487720) baseStart_487720 baseEnd_487720 := by
    simpa [prefixWord, tailWord_487720, baseEnd_487720] using wordTrace_append hprefix tailTrace_487720
  have hstable : (prefixWord ++ tailWord_487720).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487720).length < 2 ^ (prefixWord ++ tailWord_487720).sum := by decide
  have hdescent : baseEnd_487720 < baseStart_487720 := by decide
  rcases family_descends (prefixWord ++ tailWord_487720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487760 : List Nat := [2, 1, 1, 1, 1, 7, 1, 5]
def baseStart_487760 : Nat := 118140960795 + 487760 * 2 ^ 59
def prefixEnd_487760 : Nat := 4983230072969 + 3 ^ 40 * 487760 * 2
def baseEnd_487760 : Nat := 148417969799772960270719

theorem tailTrace_487760 : CollatzResearch.WordTrace tailWord_487760 prefixEnd_487760 148417969799772960270719 := by
  unfold tailWord_487760
  simp only [CollatzResearch.WordTrace]
  refine ⟨8895034356468148810518367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11860045808624198414024489 8895034356468148810518367)
  ·
    refine ⟨13342551534702223215777551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8895034356468148810518367 13342551534702223215777551)
    ·
      refine ⟨20013827302053334823666327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13342551534702223215777551 20013827302053334823666327)
      ·
        refine ⟨30020740953080002235499491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20013827302053334823666327 30020740953080002235499491)
        ·
          refine ⟨45031111429620003353249237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30020740953080002235499491 45031111429620003353249237)
          ·
            refine ⟨1055416674131718828591779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 45031111429620003353249237 1055416674131718828591779)
            ·
              refine ⟨1583125011197578242887669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1055416674131718828591779 1583125011197578242887669)
              ·
                refine ⟨148417969799772960270719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1583125011197578242887669 148417969799772960270719)
                ·
                  rfl

theorem cell19_487760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 5].length) (baseStart_487760 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_487760 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_487760 prefixEnd_487760 := by exact prefixLift 487760
  have htrace : WordTrace (prefixWord ++ tailWord_487760) baseStart_487760 baseEnd_487760 := by
    simpa [prefixWord, tailWord_487760, baseEnd_487760] using wordTrace_append hprefix tailTrace_487760
  have hstable : (prefixWord ++ tailWord_487760).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487760).length < 2 ^ (prefixWord ++ tailWord_487760).sum := by decide
  have hdescent : baseEnd_487760 < baseStart_487760 := by decide
  rcases family_descends (prefixWord ++ tailWord_487760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487817 : List Nat := [1, 2, 1, 1, 6, 1, 2, 5]
def baseStart_487817 : Nat := 118140960795 + 487817 * 2 ^ 59
def prefixEnd_487817 : Nat := 4983230072969 + 3 ^ 40 * 487817 * 2
def baseEnd_487817 : Nat := 148435314035213717003897

theorem tailTrace_487817 : CollatzResearch.WordTrace tailWord_487817 prefixEnd_487817 148435314035213717003897 := by
  unfold tailWord_487817
  simp only [CollatzResearch.WordTrace]
  refine ⟨17792147673729796355861705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11861431782486530903907803 17792147673729796355861705)
  ·
    refine ⟨13344110755297347266896279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17792147673729796355861705 13344110755297347266896279)
    ·
      refine ⟨20016166132946020900344419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13344110755297347266896279 20016166132946020900344419)
      ·
        refine ⟨30024249199419031350516629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20016166132946020900344419 30024249199419031350516629)
        ·
          refine ⟨1407386681222767094555467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 30024249199419031350516629 1407386681222767094555467)
          ·
            refine ⟨2111080021834150641833201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1407386681222767094555467 2111080021834150641833201)
            ·
              refine ⟨1583310016375612981374901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2111080021834150641833201 1583310016375612981374901)
              ·
                refine ⟨148435314035213717003897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1583310016375612981374901 148435314035213717003897)
                ·
                  rfl

theorem cell19_487817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 5].length) (baseStart_487817 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_487817 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_487817 prefixEnd_487817 := by exact prefixLift 487817
  have htrace : WordTrace (prefixWord ++ tailWord_487817) baseStart_487817 baseEnd_487817 := by
    simpa [prefixWord, tailWord_487817, baseEnd_487817] using wordTrace_append hprefix tailTrace_487817
  have hstable : (prefixWord ++ tailWord_487817).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487817).length < 2 ^ (prefixWord ++ tailWord_487817).sum := by decide
  have hdescent : baseEnd_487817 < baseStart_487817 := by decide
  rcases family_descends (prefixWord ++ tailWord_487817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487830 : List Nat := [5, 3, 1, 2, 1, 7]
def baseStart_487830 : Nat := 118140960795 + 487830 * 2 ^ 59
def prefixEnd_487830 : Nat := 4983230072969 + 3 ^ 40 * 487830 * 2
def baseEnd_487830 : Nat := 16493252193114837634997

theorem tailTrace_487830 : CollatzResearch.WordTrace tailWord_487830 prefixEnd_487830 16493252193114837634997 := by
  unfold tailWord_487830
  simp only [CollatzResearch.WordTrace]
  refine ⟨1112038863917668723505309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11861747881788466384056629 1112038863917668723505309)
  ·
    refine ⟨417014573969125771314491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1112038863917668723505309 417014573969125771314491)
    ·
      refine ⟨625521860953688656971737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417014573969125771314491 625521860953688656971737)
      ·
        refine ⟨469141395715266492728803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 625521860953688656971737 469141395715266492728803)
        ·
          refine ⟨703712093572899739093205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 469141395715266492728803 703712093572899739093205)
          ·
            refine ⟨16493252193114837634997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 703712093572899739093205 16493252193114837634997)
            ·
              rfl

theorem cell19_487830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 7].length) (baseStart_487830 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_487830 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_487830 prefixEnd_487830 := by exact prefixLift 487830
  have htrace : WordTrace (prefixWord ++ tailWord_487830) baseStart_487830 baseEnd_487830 := by
    simpa [prefixWord, tailWord_487830, baseEnd_487830] using wordTrace_append hprefix tailTrace_487830
  have hstable : (prefixWord ++ tailWord_487830).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487830).length < 2 ^ (prefixWord ++ tailWord_487830).sum := by decide
  have hdescent : baseEnd_487830 < baseStart_487830 := by decide
  rcases family_descends (prefixWord ++ tailWord_487830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487893 : List Nat := [1, 3, 2, 3, 1, 3, 6]
def baseStart_487893 : Nat := 118140960795 + 487893 * 2 ^ 59
def prefixEnd_487893 : Nat := 4983230072969 + 3 ^ 40 * 487893 * 2
def baseEnd_487893 : Nat := 49486146560822686438267

theorem tailTrace_487893 : CollatzResearch.WordTrace tailWord_487893 prefixEnd_487893 49486146560822686438267 := by
  unfold tailWord_487893
  simp only [CollatzResearch.WordTrace]
  refine ⟨17794919621454461335628333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11863279747636307557085555 17794919621454461335628333)
  ·
    refine ⟨6673094858045423000860625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17794919621454461335628333 6673094858045423000860625)
    ·
      refine ⟨5004821143534067250645469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6673094858045423000860625 5004821143534067250645469)
      ·
        refine ⟨1876807928825275218992051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5004821143534067250645469 1876807928825275218992051)
        ·
          refine ⟨2815211893237912828488077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1876807928825275218992051 2815211893237912828488077)
          ·
            refine ⟨1055704459964217310683029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2815211893237912828488077 1055704459964217310683029)
            ·
              refine ⟨49486146560822686438267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1055704459964217310683029 49486146560822686438267)
              ·
                rfl

theorem cell19_487893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 6].length) (baseStart_487893 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_487893 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_487893 prefixEnd_487893 := by exact prefixLift 487893
  have htrace : WordTrace (prefixWord ++ tailWord_487893) baseStart_487893 baseEnd_487893 := by
    simpa [prefixWord, tailWord_487893, baseEnd_487893] using wordTrace_append hprefix tailTrace_487893
  have hstable : (prefixWord ++ tailWord_487893).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487893).length < 2 ^ (prefixWord ++ tailWord_487893).sum := by decide
  have hdescent : baseEnd_487893 < baseStart_487893 := by decide
  rcases family_descends (prefixWord ++ tailWord_487893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487925 : List Nat := [1, 3, 5, 1, 2, 2, 2, 3]
def baseStart_487925 : Nat := 118140960795 + 487925 * 2 ^ 59
def prefixEnd_487925 : Nat := 4983230072969 + 3 ^ 40 * 487925 * 2
def baseEnd_487925 : Nat := 148468176797101466603603

theorem tailTrace_487925 : CollatzResearch.WordTrace tailWord_487925 prefixEnd_487925 148468176797101466603603 := by
  unfold tailWord_487925
  simp only [CollatzResearch.WordTrace]
  refine ⟨17796086757338530800793229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11864057838225687200528819 17796086757338530800793229)
  ·
    refine ⟨6673532534001949050297461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17796086757338530800793229 6673532534001949050297461)
    ·
      refine ⟨625643675062682723465387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6673532534001949050297461 625643675062682723465387)
      ·
        refine ⟨938465512594024085198081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 625643675062682723465387 938465512594024085198081)
        ·
          refine ⟨703849134445518063898561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 938465512594024085198081 703849134445518063898561)
          ·
            refine ⟨527886850834138547923921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 703849134445518063898561 527886850834138547923921)
            ·
              refine ⟨395915138125603910942941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 527886850834138547923921 395915138125603910942941)
              ·
                refine ⟨148468176797101466603603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 395915138125603910942941 148468176797101466603603)
                ·
                  rfl

theorem cell19_487925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 2, 3].length) (baseStart_487925 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_487925 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_487925 prefixEnd_487925 := by exact prefixLift 487925
  have htrace : WordTrace (prefixWord ++ tailWord_487925) baseStart_487925 baseEnd_487925 := by
    simpa [prefixWord, tailWord_487925, baseEnd_487925] using wordTrace_append hprefix tailTrace_487925
  have hstable : (prefixWord ++ tailWord_487925).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487925).length < 2 ^ (prefixWord ++ tailWord_487925).sum := by decide
  have hdescent : baseEnd_487925 < baseStart_487925 := by decide
  rcases family_descends (prefixWord ++ tailWord_487925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487950 : List Nat := [4, 1, 1, 2, 3, 1, 7]
def baseStart_487950 : Nat := 118140960795 + 487950 * 2 ^ 59
def prefixEnd_487950 : Nat := 4983230072969 + 3 ^ 40 * 487950 * 2
def baseEnd_487950 : Nat := 49491927972636272015993

theorem tailTrace_487950 : CollatzResearch.WordTrace tailWord_487950 prefixEnd_487950 49491927972636272015993 := by
  unfold tailWord_487950
  simp only [CollatzResearch.WordTrace]
  refine ⟨2224624822780995008806663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11864665721498640046968869 2224624822780995008806663)
  ·
    refine ⟨3336937234171492513209995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2224624822780995008806663 3336937234171492513209995)
    ·
      refine ⟨5005405851257238769814993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3336937234171492513209995 5005405851257238769814993)
      ·
        refine ⟨3754054388442929077361245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5005405851257238769814993 3754054388442929077361245)
        ·
          refine ⟨1407770395666098404010467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3754054388442929077361245 1407770395666098404010467)
          ·
            refine ⟨2111655593499147606015701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1407770395666098404010467 2111655593499147606015701)
            ·
              refine ⟨49491927972636272015993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2111655593499147606015701 49491927972636272015993)
              ·
                rfl

theorem cell19_487950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 7].length) (baseStart_487950 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_487950 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_487950 prefixEnd_487950 := by exact prefixLift 487950
  have htrace : WordTrace (prefixWord ++ tailWord_487950) baseStart_487950 baseEnd_487950 := by
    simpa [prefixWord, tailWord_487950, baseEnd_487950] using wordTrace_append hprefix tailTrace_487950
  have hstable : (prefixWord ++ tailWord_487950).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487950).length < 2 ^ (prefixWord ++ tailWord_487950).sum := by decide
  have hdescent : baseEnd_487950 < baseStart_487950 := by decide
  rcases family_descends (prefixWord ++ tailWord_487950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487969 : List Nat := [1, 2, 3, 2, 2, 1, 4, 4]
def baseStart_487969 : Nat := 118140960795 + 487969 * 2 ^ 59
def prefixEnd_487969 : Nat := 4983230072969 + 3 ^ 40 * 487969 * 2
def baseEnd_487969 : Nat := 148481565329722401625705

theorem tailTrace_487969 : CollatzResearch.WordTrace tailWord_487969 prefixEnd_487969 148481565329722401625705 := by
  unfold tailWord_487969
  simp only [CollatzResearch.WordTrace]
  refine ⟨17797691569179126315394961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11865127712786084210263307 17797691569179126315394961)
  ·
    refine ⟨13348268676884344736546221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17797691569179126315394961 13348268676884344736546221)
    ·
      refine ⟨5005600753831629276204833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13348268676884344736546221 5005600753831629276204833)
      ·
        refine ⟨3754200565373721957153625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5005600753831629276204833 3754200565373721957153625)
        ·
          refine ⟨2815650424030291467865219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3754200565373721957153625 2815650424030291467865219)
          ·
            refine ⟨4223475636045437201797829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2815650424030291467865219 4223475636045437201797829)
            ·
              refine ⟨791901681758519475337093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4223475636045437201797829 791901681758519475337093)
              ·
                refine ⟨148481565329722401625705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 791901681758519475337093 148481565329722401625705)
                ·
                  rfl

theorem cell19_487969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 4].length) (baseStart_487969 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_487969 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_487969 prefixEnd_487969 := by exact prefixLift 487969
  have htrace : WordTrace (prefixWord ++ tailWord_487969) baseStart_487969 baseEnd_487969 := by
    simpa [prefixWord, tailWord_487969, baseEnd_487969] using wordTrace_append hprefix tailTrace_487969
  have hstable : (prefixWord ++ tailWord_487969).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487969).length < 2 ^ (prefixWord ++ tailWord_487969).sum := by decide
  have hdescent : baseEnd_487969 < baseStart_487969 := by decide
  rcases family_descends (prefixWord ++ tailWord_487969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488047 : List Nat := [1, 1, 2, 1, 3, 2, 2, 7]
def baseStart_488047 : Nat := 118140960795 + 488047 * 2 ^ 59
def prefixEnd_488047 : Nat := 4983230072969 + 3 ^ 40 * 488047 * 2
def baseEnd_488047 : Nat := 148505299546641331892159

theorem tailTrace_488047 : CollatzResearch.WordTrace tailWord_488047 prefixEnd_488047 148505299546641331892159 := by
  unfold tailWord_488047
  simp only [CollatzResearch.WordTrace]
  refine ⟨17800536462896545636734395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11867024308597697091156263 17800536462896545636734395)
  ·
    refine ⟨26700804694344818455101593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17800536462896545636734395 26700804694344818455101593)
    ·
      refine ⟨20025603520758613841326195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26700804694344818455101593 20025603520758613841326195)
      ·
        refine ⟨30038405281137920761989293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20025603520758613841326195 30038405281137920761989293)
        ·
          refine ⟨11264401980426720285745985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30038405281137920761989293 11264401980426720285745985)
          ·
            refine ⟨8448301485320040214309489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11264401980426720285745985 8448301485320040214309489)
            ·
              refine ⟨6336226113990030160732117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8448301485320040214309489 6336226113990030160732117)
              ·
                refine ⟨148505299546641331892159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6336226113990030160732117 148505299546641331892159)
                ·
                  rfl

theorem cell19_488047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 7].length) (baseStart_488047 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_488047 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_488047 prefixEnd_488047 := by exact prefixLift 488047
  have htrace : WordTrace (prefixWord ++ tailWord_488047) baseStart_488047 baseEnd_488047 := by
    simpa [prefixWord, tailWord_488047, baseEnd_488047] using wordTrace_append hprefix tailTrace_488047
  have hstable : (prefixWord ++ tailWord_488047).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488047).length < 2 ^ (prefixWord ++ tailWord_488047).sum := by decide
  have hdescent : baseEnd_488047 < baseStart_488047 := by decide
  rcases family_descends (prefixWord ++ tailWord_488047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488119 : List Nat := [1, 1, 3, 1, 7, 1, 5]
def baseStart_488119 : Nat := 118140960795 + 488119 * 2 ^ 59
def prefixEnd_488119 : Nat := 4983230072969 + 3 ^ 40 * 488119 * 2
def baseEnd_488119 : Nat := 49509069351522166097321

theorem tailTrace_488119 : CollatzResearch.WordTrace tailWord_488119 prefixEnd_488119 49509069351522166097321 := by
  unfold tailWord_488119
  simp only [CollatzResearch.WordTrace]
  refine ⟨17803162518635701933355411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11868775012423801288903607 17803162518635701933355411)
  ·
    refine ⟨26704743777953552900033117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17803162518635701933355411 26704743777953552900033117)
    ·
      refine ⟨10014278916732582337512419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26704743777953552900033117 10014278916732582337512419)
      ·
        refine ⟨15021418375098873506268629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10014278916732582337512419 15021418375098873506268629)
        ·
          refine ⟨352064493166379847803171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 15021418375098873506268629 352064493166379847803171)
          ·
            refine ⟨528096739749569771704757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 352064493166379847803171 528096739749569771704757)
            ·
              refine ⟨49509069351522166097321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 528096739749569771704757 49509069351522166097321)
              ·
                rfl

theorem cell19_488119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 5].length) (baseStart_488119 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_488119 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_488119 prefixEnd_488119 := by exact prefixLift 488119
  have htrace : WordTrace (prefixWord ++ tailWord_488119) baseStart_488119 baseEnd_488119 := by
    simpa [prefixWord, tailWord_488119, baseEnd_488119] using wordTrace_append hprefix tailTrace_488119
  have hstable : (prefixWord ++ tailWord_488119).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488119).length < 2 ^ (prefixWord ++ tailWord_488119).sum := by decide
  have hdescent : baseEnd_488119 < baseStart_488119 := by decide
  rcases family_descends (prefixWord ++ tailWord_488119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488134 : List Nat := [6, 1, 2, 1, 2, 1, 2, 4]
def baseStart_488134 : Nat := 118140960795 + 488134 * 2 ^ 59
def prefixEnd_488134 : Nat := 4983230072969 + 3 ^ 40 * 488134 * 2
def baseEnd_488134 : Nat := 148531772327050907958589

theorem tailTrace_488134 : CollatzResearch.WordTrace tailWord_488134 prefixEnd_488134 148531772327050907958589 := by
  unfold tailWord_488134
  simp only [CollatzResearch.WordTrace]
  refine ⟨556365925424417484223483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 11869139742387572996767637 556365925424417484223483)
  ·
    refine ⟨834548888136626226335225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 556365925424417484223483 834548888136626226335225)
    ·
      refine ⟨625911666102469669751419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 834548888136626226335225 625911666102469669751419)
      ·
        refine ⟨938867499153704504627129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 625911666102469669751419 938867499153704504627129)
        ·
          refine ⟨704150624365278378470347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 938867499153704504627129 704150624365278378470347)
          ·
            refine ⟨1056225936547917567705521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 704150624365278378470347 1056225936547917567705521)
            ·
              refine ⟨792169452410938175779141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1056225936547917567705521 792169452410938175779141)
              ·
                refine ⟨148531772327050907958589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 792169452410938175779141 148531772327050907958589)
                ·
                  rfl

theorem cell19_488134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_488134 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_488134 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_488134 prefixEnd_488134 := by exact prefixLift 488134
  have htrace : WordTrace (prefixWord ++ tailWord_488134) baseStart_488134 baseEnd_488134 := by
    simpa [prefixWord, tailWord_488134, baseEnd_488134] using wordTrace_append hprefix tailTrace_488134
  have hstable : (prefixWord ++ tailWord_488134).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488134).length < 2 ^ (prefixWord ++ tailWord_488134).sum := by decide
  have hdescent : baseEnd_488134 < baseStart_488134 := by decide
  rcases family_descends (prefixWord ++ tailWord_488134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488140 : List Nat := [2, 2, 1, 5, 1, 1, 1, 6]
def baseStart_488140 : Nat := 118140960795 + 488140 * 2 ^ 59
def prefixEnd_488140 : Nat := 4983230072969 + 3 ^ 40 * 488140 * 2
def baseEnd_488140 : Nat := 148533598036044671825239

theorem tailTrace_488140 : CollatzResearch.WordTrace tailWord_488140 prefixEnd_488140 148533598036044671825239 := by
  unfold tailWord_488140
  simp only [CollatzResearch.WordTrace]
  refine ⟨8901964225779811259934937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11869285634373081679913249 8901964225779811259934937)
  ·
    refine ⟨6676473169334858444951203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8901964225779811259934937 6676473169334858444951203)
    ·
      refine ⟨10014709754002287667426805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6676473169334858444951203 10014709754002287667426805)
      ·
        refine ⟨938879039437714468821263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10014709754002287667426805 938879039437714468821263)
        ·
          refine ⟨1408318559156571703231895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 938879039437714468821263 1408318559156571703231895)
          ·
            refine ⟨2112477838734857554847843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1408318559156571703231895 2112477838734857554847843)
            ·
              refine ⟨3168716758102286332271765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2112477838734857554847843 3168716758102286332271765)
              ·
                refine ⟨148533598036044671825239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3168716758102286332271765 148533598036044671825239)
                ·
                  rfl

theorem cell19_488140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 6].length) (baseStart_488140 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_488140 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_488140 prefixEnd_488140 := by exact prefixLift 488140
  have htrace : WordTrace (prefixWord ++ tailWord_488140) baseStart_488140 baseEnd_488140 := by
    simpa [prefixWord, tailWord_488140, baseEnd_488140] using wordTrace_append hprefix tailTrace_488140
  have hstable : (prefixWord ++ tailWord_488140).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488140).length < 2 ^ (prefixWord ++ tailWord_488140).sum := by decide
  have hdescent : baseEnd_488140 < baseStart_488140 := by decide
  rcases family_descends (prefixWord ++ tailWord_488140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488273 : List Nat := [1, 2, 2, 1, 6, 1, 1, 5]
def baseStart_488273 : Nat := 118140960795 + 488273 * 2 ^ 59
def prefixEnd_488273 : Nat := 4983230072969 + 3 ^ 40 * 488273 * 2
def baseEnd_488273 : Nat := 148574067918739770869321

theorem tailTrace_488273 : CollatzResearch.WordTrace tailWord_488273 prefixEnd_488273 148574067918739770869321 := by
  unfold tailWord_488273
  simp only [CollatzResearch.WordTrace]
  refine ⟨17808779360077786234461473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11872519573385190822974315 17808779360077786234461473)
  ·
    refine ⟨13356584520058339675846105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17808779360077786234461473 13356584520058339675846105)
    ·
      refine ⟨10017438390043754756884579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13356584520058339675846105 10017438390043754756884579)
      ·
        refine ⟨15026157585065632135326869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10017438390043754756884579 15026157585065632135326869)
        ·
          refine ⟨704351136799951506343447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 15026157585065632135326869 704351136799951506343447)
          ·
            refine ⟨1056526705199927259515171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 704351136799951506343447 1056526705199927259515171)
            ·
              refine ⟨1584790057799890889272757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1056526705199927259515171 1584790057799890889272757)
              ·
                refine ⟨148574067918739770869321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1584790057799890889272757 148574067918739770869321)
                ·
                  rfl

theorem cell19_488273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 5].length) (baseStart_488273 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_488273 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_488273 prefixEnd_488273 := by exact prefixLift 488273
  have htrace : WordTrace (prefixWord ++ tailWord_488273) baseStart_488273 baseEnd_488273 := by
    simpa [prefixWord, tailWord_488273, baseEnd_488273] using wordTrace_append hprefix tailTrace_488273
  have hstable : (prefixWord ++ tailWord_488273).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488273).length < 2 ^ (prefixWord ++ tailWord_488273).sum := by decide
  have hdescent : baseEnd_488273 < baseStart_488273 := by decide
  rcases family_descends (prefixWord ++ tailWord_488273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488290 : List Nat := [3, 3, 2, 1, 3, 2, 5]
def baseStart_488290 : Nat := 118140960795 + 488290 * 2 ^ 59
def prefixEnd_488290 : Nat := 4983230072969 + 3 ^ 40 * 488290 * 2
def baseEnd_488290 : Nat := 49526413586962922830499

theorem tailTrace_488290 : CollatzResearch.WordTrace tailWord_488290 prefixEnd_488290 49526413586962922830499 := by
  unfold tailWord_488290
  simp only [CollatzResearch.WordTrace]
  refine ⟨4452349850254049534457581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11872932934010798758553549 4452349850254049534457581)
  ·
    refine ⟨1669631193845268575421593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4452349850254049534457581 1669631193845268575421593)
    ·
      refine ⟨1252223395383951431566195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1669631193845268575421593 1252223395383951431566195)
      ·
        refine ⟨1878335093075927147349293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1252223395383951431566195 1878335093075927147349293)
        ·
          refine ⟨704375659903472680255985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1878335093075927147349293 704375659903472680255985)
          ·
            refine ⟨528281744927604510191989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 704375659903472680255985 528281744927604510191989)
            ·
              refine ⟨49526413586962922830499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 528281744927604510191989 49526413586962922830499)
              ·
                rfl

theorem cell19_488290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 5].length) (baseStart_488290 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_488290 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_488290 prefixEnd_488290 := by exact prefixLift 488290
  have htrace : WordTrace (prefixWord ++ tailWord_488290) baseStart_488290 baseEnd_488290 := by
    simpa [prefixWord, tailWord_488290, baseEnd_488290] using wordTrace_append hprefix tailTrace_488290
  have hstable : (prefixWord ++ tailWord_488290).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488290).length < 2 ^ (prefixWord ++ tailWord_488290).sum := by decide
  have hdescent : baseEnd_488290 < baseStart_488290 := by decide
  rcases family_descends (prefixWord ++ tailWord_488290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488292 : List Nat := [2, 3, 1, 1, 4, 3, 5]
def baseStart_488292 : Nat := 118140960795 + 488292 * 2 ^ 59
def prefixEnd_488292 : Nat := 4983230072969 + 3 ^ 40 * 488292 * 2
def baseEnd_488292 : Nat := 49526616443517785482349

theorem tailTrace_488292 : CollatzResearch.WordTrace tailWord_488292 prefixEnd_488292 49526616443517785482349 := by
  unfold tailWord_488292
  simp only [CollatzResearch.WordTrace]
  refine ⟨8904736173504476239701565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11872981564672634986268753 8904736173504476239701565)
  ·
    refine ⟨3339276065064178589888087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8904736173504476239701565 3339276065064178589888087)
    ·
      refine ⟨5008914097596267884832131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3339276065064178589888087 5008914097596267884832131)
      ·
        refine ⟨7513371146394401827248197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5008914097596267884832131 7513371146394401827248197)
        ·
          refine ⟨1408757089948950342609037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7513371146394401827248197 1408757089948950342609037)
          ·
            refine ⟨528283908730856378478389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1408757089948950342609037 528283908730856378478389)
            ·
              refine ⟨49526616443517785482349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 528283908730856378478389 49526616443517785482349)
              ·
                rfl

theorem cell19_488292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 5].length) (baseStart_488292 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_488292 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_488292 prefixEnd_488292 := by exact prefixLift 488292
  have htrace : WordTrace (prefixWord ++ tailWord_488292) baseStart_488292 baseEnd_488292 := by
    simpa [prefixWord, tailWord_488292, baseEnd_488292] using wordTrace_append hprefix tailTrace_488292
  have hstable : (prefixWord ++ tailWord_488292).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488292).length < 2 ^ (prefixWord ++ tailWord_488292).sum := by decide
  have hdescent : baseEnd_488292 < baseStart_488292 := by decide
  rcases family_descends (prefixWord ++ tailWord_488292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488313 : List Nat := [1, 2, 1, 3, 2, 3, 1, 6]
def baseStart_488313 : Nat := 118140960795 + 488313 * 2 ^ 59
def prefixEnd_488313 : Nat := 4983230072969 + 3 ^ 40 * 488313 * 2
def baseEnd_488313 : Nat := 148586239312031529980323

theorem tailTrace_488313 : CollatzResearch.WordTrace tailWord_488313 prefixEnd_488313 148586239312031529980323 := by
  unfold tailWord_488313
  simp only [CollatzResearch.WordTrace]
  refine ⟨17810238279932873065917593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11873492186621915377278395 17810238279932873065917593)
  ·
    refine ⟨13357678709949654799438195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17810238279932873065917593 13357678709949654799438195)
    ·
      refine ⟨20036518064924482199157293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13357678709949654799438195 20036518064924482199157293)
      ·
        refine ⟨7513694274346680824683985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20036518064924482199157293 7513694274346680824683985)
        ·
          refine ⟨5635270705760010618512989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7513694274346680824683985 5635270705760010618512989)
          ·
            refine ⟨2113226514660003981942371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5635270705760010618512989 2113226514660003981942371)
            ·
              refine ⟨3169839771990005972913557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2113226514660003981942371 3169839771990005972913557)
              ·
                refine ⟨148586239312031529980323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3169839771990005972913557 148586239312031529980323)
                ·
                  rfl

theorem cell19_488313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 6].length) (baseStart_488313 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_488313 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_488313 prefixEnd_488313 := by exact prefixLift 488313
  have htrace : WordTrace (prefixWord ++ tailWord_488313) baseStart_488313 baseEnd_488313 := by
    simpa [prefixWord, tailWord_488313, baseEnd_488313] using wordTrace_append hprefix tailTrace_488313
  have hstable : (prefixWord ++ tailWord_488313).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488313).length < 2 ^ (prefixWord ++ tailWord_488313).sum := by decide
  have hdescent : baseEnd_488313 < baseStart_488313 := by decide
  rcases family_descends (prefixWord ++ tailWord_488313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488330 : List Nat := [3, 1, 2, 4, 1, 1, 2, 5]
def baseStart_488330 : Nat := 118140960795 + 488330 * 2 ^ 59
def prefixEnd_488330 : Nat := 4983230072969 + 3 ^ 40 * 488330 * 2
def baseEnd_488330 : Nat := 148591412154180527602499

theorem tailTrace_488330 : CollatzResearch.WordTrace tailWord_488330 prefixEnd_488330 148591412154180527602499 := by
  unfold tailWord_488330
  simp only [CollatzResearch.WordTrace]
  refine ⟨4452714580217821242321611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11873905547247523312857629 4452714580217821242321611)
  ·
    refine ⟨6679071870326731863482417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4452714580217821242321611 6679071870326731863482417)
    ·
      refine ⟨5009303902745048897611813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6679071870326731863482417 5009303902745048897611813)
      ·
        refine ⟨939244481764696668302215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5009303902745048897611813 939244481764696668302215)
        ·
          refine ⟨1408866722647045002453323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 939244481764696668302215 1408866722647045002453323)
          ·
            refine ⟨2113300083970567503679985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1408866722647045002453323 2113300083970567503679985)
            ·
              refine ⟨1584975062977925627759989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2113300083970567503679985 1584975062977925627759989)
              ·
                refine ⟨148591412154180527602499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1584975062977925627759989 148591412154180527602499)
                ·
                  rfl

theorem cell19_488330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 5].length) (baseStart_488330 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_488330 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_488330 prefixEnd_488330 := by exact prefixLift 488330
  have htrace : WordTrace (prefixWord ++ tailWord_488330) baseStart_488330 baseEnd_488330 := by
    simpa [prefixWord, tailWord_488330, baseEnd_488330] using wordTrace_append hprefix tailTrace_488330
  have hstable : (prefixWord ++ tailWord_488330).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488330).length < 2 ^ (prefixWord ++ tailWord_488330).sum := by decide
  have hdescent : baseEnd_488330 < baseStart_488330 := by decide
  rcases family_descends (prefixWord ++ tailWord_488330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488332 : List Nat := [2, 2, 1, 2, 1, 2, 4, 5]
def baseStart_488332 : Nat := 118140960795 + 488332 * 2 ^ 59
def prefixEnd_488332 : Nat := 4983230072969 + 3 ^ 40 * 488332 * 2
def baseEnd_488332 : Nat := 148592020723845115558049

theorem tailTrace_488332 : CollatzResearch.WordTrace tailWord_488332 prefixEnd_488332 148592020723845115558049 := by
  unfold tailWord_488332
  simp only [CollatzResearch.WordTrace]
  refine ⟨8905465633432019655429625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11873954177909359540572833 8905465633432019655429625)
  ·
    refine ⟨6679099225074014741572219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8905465633432019655429625 6679099225074014741572219)
    ·
      refine ⟨10018648837611022112358329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6679099225074014741572219 10018648837611022112358329)
      ·
        refine ⟨7513986628208266584268747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10018648837611022112358329 7513986628208266584268747)
        ·
          refine ⟨11270979942312399876403121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7513986628208266584268747 11270979942312399876403121)
          ·
            refine ⟨8453234956734299907302341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11270979942312399876403121 8453234956734299907302341)
            ·
              refine ⟨1584981554387681232619189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8453234956734299907302341 1584981554387681232619189)
              ·
                refine ⟨148592020723845115558049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1584981554387681232619189 148592020723845115558049)
                ·
                  rfl

theorem cell19_488332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 5].length) (baseStart_488332 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_488332 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_488332 prefixEnd_488332 := by exact prefixLift 488332
  have htrace : WordTrace (prefixWord ++ tailWord_488332) baseStart_488332 baseEnd_488332 := by
    simpa [prefixWord, tailWord_488332, baseEnd_488332] using wordTrace_append hprefix tailTrace_488332
  have hstable : (prefixWord ++ tailWord_488332).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488332).length < 2 ^ (prefixWord ++ tailWord_488332).sum := by decide
  have hdescent : baseEnd_488332 < baseStart_488332 := by decide
  rcases family_descends (prefixWord ++ tailWord_488332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488351 : List Nat := [1, 1, 2, 5, 2, 8]
def baseStart_488351 : Nat := 118140960795 + 488351 * 2 ^ 59
def prefixEnd_488351 : Nat := 4983230072969 + 3 ^ 40 * 488351 * 2
def baseEnd_488351 : Nat := 16510866903962077903975

theorem tailTrace_488351 : CollatzResearch.WordTrace tailWord_488351 prefixEnd_488351 16510866903962077903975 := by
  unfold tailWord_488351
  simp only [CollatzResearch.WordTrace]
  refine ⟨17811624253795205555800907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11874416169196803703867271 17811624253795205555800907)
  ·
    refine ⟨26717436380692808333701361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17811624253795205555800907 26717436380692808333701361)
    ·
      refine ⟨20038077285519606250276021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26717436380692808333701361 20038077285519606250276021)
      ·
        refine ⟨1878569745517463085963377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20038077285519606250276021 1878569745517463085963377)
        ·
          refine ⟨1408927309138097314472533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1878569745517463085963377 1408927309138097314472533)
          ·
            refine ⟨16510866903962077903975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1408927309138097314472533 16510866903962077903975)
            ·
              rfl

theorem cell19_488351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 8].length) (baseStart_488351 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_488351 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_488351 prefixEnd_488351 := by exact prefixLift 488351
  have htrace : WordTrace (prefixWord ++ tailWord_488351) baseStart_488351 baseEnd_488351 := by
    simpa [prefixWord, tailWord_488351, baseEnd_488351] using wordTrace_append hprefix tailTrace_488351
  have hstable : (prefixWord ++ tailWord_488351).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488351).length < 2 ^ (prefixWord ++ tailWord_488351).sum := by decide
  have hdescent : baseEnd_488351 < baseStart_488351 := by decide
  rcases family_descends (prefixWord ++ tailWord_488351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488408 : List Nat := [2, 1, 2, 2, 2, 4, 6]
def baseStart_488408 : Nat := 118140960795 + 488408 * 2 ^ 59
def prefixEnd_488408 : Nat := 4983230072969 + 3 ^ 40 * 488408 * 2
def baseEnd_488408 : Nat := 49538382123699819289651

theorem tailTrace_488408 : CollatzResearch.WordTrace tailWord_488408 prefixEnd_488408 49538382123699819289651 := by
  unfold tailWord_488408
  simp only [CollatzResearch.WordTrace]
  refine ⟨8906851607294352145312939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11875802143059136193750585 8906851607294352145312939)
  ·
    refine ⟨13360277410941528217969409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8906851607294352145312939 13360277410941528217969409)
    ·
      refine ⟨10020208058206146163477057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13360277410941528217969409 10020208058206146163477057)
      ·
        refine ⟨7515156043654609622607793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10020208058206146163477057 7515156043654609622607793)
        ·
          refine ⟨5636367032740957216955845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7515156043654609622607793 5636367032740957216955845)
          ·
            refine ⟨1056818818638929478179221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5636367032740957216955845 1056818818638929478179221)
            ·
              refine ⟨49538382123699819289651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1056818818638929478179221 49538382123699819289651)
              ·
                rfl

theorem cell19_488408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 6].length) (baseStart_488408 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_488408 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_488408 prefixEnd_488408 := by exact prefixLift 488408
  have htrace : WordTrace (prefixWord ++ tailWord_488408) baseStart_488408 baseEnd_488408 := by
    simpa [prefixWord, tailWord_488408, baseEnd_488408] using wordTrace_append hprefix tailTrace_488408
  have hstable : (prefixWord ++ tailWord_488408).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488408).length < 2 ^ (prefixWord ++ tailWord_488408).sum := by decide
  have hdescent : baseEnd_488408 < baseStart_488408 := by decide
  rcases family_descends (prefixWord ++ tailWord_488408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488444 : List Nat := [2, 2, 2, 1, 2, 3, 4, 3]
def baseStart_488444 : Nat := 118140960795 + 488444 * 2 ^ 59
def prefixEnd_488444 : Nat := 4983230072969 + 3 ^ 40 * 488444 * 2
def baseEnd_488444 : Nat := 148626100625062041068855

theorem tailTrace_488444 : CollatzResearch.WordTrace tailWord_488444 prefixEnd_488444 148626100625062041068855 := by
  unfold tailWord_488444
  simp only [CollatzResearch.WordTrace]
  refine ⟨8907508121229141219468193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11876677494972188292624257 8907508121229141219468193)
  ·
    refine ⟨6680631090921855914601145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8907508121229141219468193 6680631090921855914601145)
    ·
      refine ⟨5010473318191391935950859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6680631090921855914601145 5010473318191391935950859)
      ·
        refine ⟨7515709977287087903926289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5010473318191391935950859 7515709977287087903926289)
        ·
          refine ⟨5636782482965315927944717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7515709977287087903926289 5636782482965315927944717)
          ·
            refine ⟨2113793431111993472979269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5636782482965315927944717 2113793431111993472979269)
            ·
              refine ⟨396336268333498776183613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2113793431111993472979269 396336268333498776183613)
              ·
                refine ⟨148626100625062041068855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 396336268333498776183613 148626100625062041068855)
                ·
                  rfl

theorem cell19_488444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 4, 3].length) (baseStart_488444 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_488444 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_488444 prefixEnd_488444 := by exact prefixLift 488444
  have htrace : WordTrace (prefixWord ++ tailWord_488444) baseStart_488444 baseEnd_488444 := by
    simpa [prefixWord, tailWord_488444, baseEnd_488444] using wordTrace_append hprefix tailTrace_488444
  have hstable : (prefixWord ++ tailWord_488444).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488444).length < 2 ^ (prefixWord ++ tailWord_488444).sum := by decide
  have hdescent : baseEnd_488444 < baseStart_488444 := by decide
  rcases family_descends (prefixWord ++ tailWord_488444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488480 : List Nat := [2, 1, 1, 7, 1, 1, 2, 4]
def baseStart_488480 : Nat := 118140960795 + 488480 * 2 ^ 59
def prefixEnd_488480 : Nat := 4983230072969 + 3 ^ 40 * 488480 * 2
def baseEnd_488480 : Nat := 148637054879024624268757

theorem tailTrace_488480 : CollatzResearch.WordTrace tailWord_488480 prefixEnd_488480 148637054879024624268757 := by
  unfold tailWord_488480
  simp only [CollatzResearch.WordTrace]
  refine ⟨8908164635163930293623447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11877552846885240391497929 8908164635163930293623447)
  ·
    refine ⟨13362246952745895440435171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8908164635163930293623447 13362246952745895440435171)
    ·
      refine ⟨20043370429118843160652757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13362246952745895440435171 20043370429118843160652757)
      ·
        refine ⟨469766494432472886577799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 20043370429118843160652757 469766494432472886577799)
        ·
          refine ⟨704649741648709329866699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 469766494432472886577799 704649741648709329866699)
          ·
            refine ⟨1056974612473063994800049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 704649741648709329866699 1056974612473063994800049)
            ·
              refine ⟨792730959354797996100037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1056974612473063994800049 792730959354797996100037)
              ·
                refine ⟨148637054879024624268757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 792730959354797996100037 148637054879024624268757)
                ·
                  rfl

theorem cell19_488480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 4].length) (baseStart_488480 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_488480 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_488480 prefixEnd_488480 := by exact prefixLift 488480
  have htrace : WordTrace (prefixWord ++ tailWord_488480) baseStart_488480 baseEnd_488480 := by
    simpa [prefixWord, tailWord_488480, baseEnd_488480] using wordTrace_append hprefix tailTrace_488480
  have hstable : (prefixWord ++ tailWord_488480).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488480).length < 2 ^ (prefixWord ++ tailWord_488480).sum := by decide
  have hdescent : baseEnd_488480 < baseStart_488480 := by decide
  rcases family_descends (prefixWord ++ tailWord_488480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488482 : List Nat := [3, 3, 1, 1, 1, 4, 2, 4]
def baseStart_488482 : Nat := 118140960795 + 488482 * 2 ^ 59
def prefixEnd_488482 : Nat := 4983230072969 + 3 ^ 40 * 488482 * 2
def baseEnd_488482 : Nat := 148637663448689212224307

theorem tailTrace_488482 : CollatzResearch.WordTrace tailWord_488482 prefixEnd_488482 148637663448689212224307 := by
  unfold tailWord_488482
  simp only [CollatzResearch.WordTrace]
  refine ⟨4454100554080153732204925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11877601477547076619213133 4454100554080153732204925)
  ·
    refine ⟨1670287707780057649576847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4454100554080153732204925 1670287707780057649576847)
    ·
      refine ⟨2505431561670086474365271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1670287707780057649576847 2505431561670086474365271)
      ·
        refine ⟨3758147342505129711547907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2505431561670086474365271 3758147342505129711547907)
        ·
          refine ⟨5637221013757694567321861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3758147342505129711547907 5637221013757694567321861)
          ·
            refine ⟨1056978940079567731372849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5637221013757694567321861 1056978940079567731372849)
            ·
              refine ⟨792734205059675798529637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1056978940079567731372849 792734205059675798529637)
              ·
                refine ⟨148637663448689212224307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 792734205059675798529637 148637663448689212224307)
                ·
                  rfl

theorem cell19_488482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 4].length) (baseStart_488482 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_488482 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_488482 prefixEnd_488482 := by exact prefixLift 488482
  have htrace : WordTrace (prefixWord ++ tailWord_488482) baseStart_488482 baseEnd_488482 := by
    simpa [prefixWord, tailWord_488482, baseEnd_488482] using wordTrace_append hprefix tailTrace_488482
  have hstable : (prefixWord ++ tailWord_488482).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488482).length < 2 ^ (prefixWord ++ tailWord_488482).sum := by decide
  have hdescent : baseEnd_488482 < baseStart_488482 := by decide
  rcases family_descends (prefixWord ++ tailWord_488482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488615 : List Nat := [1, 1, 6, 2, 1, 2, 1, 5]
def baseStart_488615 : Nat := 118140960795 + 488615 * 2 ^ 59
def prefixEnd_488615 : Nat := 4983230072969 + 3 ^ 40 * 488615 * 2
def baseEnd_488615 : Nat := 148678133331384311268389

theorem tailTrace_488615 : CollatzResearch.WordTrace tailWord_488615 prefixEnd_488615 148678133331384311268389 := by
  unfold tailWord_488615
  simp only [CollatzResearch.WordTrace]
  refine ⟨17821253124838778643411299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11880835416559185762274199 17821253124838778643411299)
  ·
    refine ⟨26731879687258167965116949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17821253124838778643411299 26731879687258167965116949)
    ·
      refine ⟨1253056860340226623364857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 26731879687258167965116949 1253056860340226623364857)
      ·
        refine ⟨939792645255169967523643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1253056860340226623364857 939792645255169967523643)
        ·
          refine ⟨1409688967882754951285465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 939792645255169967523643 1409688967882754951285465)
          ·
            refine ⟨1057266725912066213464099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1409688967882754951285465 1057266725912066213464099)
            ·
              refine ⟨1585900088868099320196149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1057266725912066213464099 1585900088868099320196149)
              ·
                refine ⟨148678133331384311268389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1585900088868099320196149 148678133331384311268389)
                ·
                  rfl

theorem cell19_488615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 5].length) (baseStart_488615 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_488615 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_488615 prefixEnd_488615 := by exact prefixLift 488615
  have htrace : WordTrace (prefixWord ++ tailWord_488615) baseStart_488615 baseEnd_488615 := by
    simpa [prefixWord, tailWord_488615, baseEnd_488615] using wordTrace_append hprefix tailTrace_488615
  have hstable : (prefixWord ++ tailWord_488615).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488615).length < 2 ^ (prefixWord ++ tailWord_488615).sum := by decide
  have hdescent : baseEnd_488615 < baseStart_488615 := by decide
  rcases family_descends (prefixWord ++ tailWord_488615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488630 : List Nat := [5, 1, 3, 2, 1, 2, 5]
def baseStart_488630 : Nat := 118140960795 + 488630 * 2 ^ 59
def prefixEnd_488630 : Nat := 4983230072969 + 3 ^ 40 * 488630 * 2
def baseEnd_488630 : Nat := 49560899201289573645005

theorem tailTrace_488630 : CollatzResearch.WordTrace tailWord_488630 prefixEnd_488630 49560899201289573645005 := by
  unfold tailWord_488630
  simp only [CollatzResearch.WordTrace]
  refine ⟨1113862513736527262825459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11881200146522957470138229 1113862513736527262825459)
  ·
    refine ⟨1670793770604790894238189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1113862513736527262825459 1670793770604790894238189)
    ·
      refine ⟨626547663976796585339321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1670793770604790894238189 626547663976796585339321)
      ·
        refine ⟨469910747982597439004491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 626547663976796585339321 469910747982597439004491)
        ·
          refine ⟨704866121973896158506737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 469910747982597439004491 704866121973896158506737)
          ·
            refine ⟨528649591480422118880053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 704866121973896158506737 528649591480422118880053)
            ·
              refine ⟨49560899201289573645005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 528649591480422118880053 49560899201289573645005)
              ·
                rfl

theorem cell19_488630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 5].length) (baseStart_488630 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_488630 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_488630 prefixEnd_488630 := by exact prefixLift 488630
  have htrace : WordTrace (prefixWord ++ tailWord_488630) baseStart_488630 baseEnd_488630 := by
    simpa [prefixWord, tailWord_488630, baseEnd_488630] using wordTrace_append hprefix tailTrace_488630
  have hstable : (prefixWord ++ tailWord_488630).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488630).length < 2 ^ (prefixWord ++ tailWord_488630).sum := by decide
  have hdescent : baseEnd_488630 < baseStart_488630 := by decide
  rcases family_descends (prefixWord ++ tailWord_488630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488636 : List Nat := [2, 2, 2, 3, 2, 1, 7]
def baseStart_488636 : Nat := 118140960795 + 488636 * 2 ^ 59
def prefixEnd_488636 : Nat := 4983230072969 + 3 ^ 40 * 488636 * 2
def baseEnd_488636 : Nat := 49561507770954161600555

theorem tailTrace_488636 : CollatzResearch.WordTrace tailWord_488636 prefixEnd_488636 49561507770954161600555 := by
  unfold tailWord_488636
  simp only [CollatzResearch.WordTrace]
  refine ⟨8911009528881349614962881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11881346038508466153283841 8911009528881349614962881)
  ·
    refine ⟨6683257146661012211222161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8911009528881349614962881 6683257146661012211222161)
    ·
      refine ⟨5012442859995759158416621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6683257146661012211222161 5012442859995759158416621)
      ·
        refine ⟨1879666072498409684406233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5012442859995759158416621 1879666072498409684406233)
        ·
          refine ⟨1409749554373807263304675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1879666072498409684406233 1409749554373807263304675)
          ·
            refine ⟨2114624331560710894957013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1409749554373807263304675 2114624331560710894957013)
            ·
              refine ⟨49561507770954161600555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2114624331560710894957013 49561507770954161600555)
              ·
                rfl

theorem cell19_488636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 7].length) (baseStart_488636 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_488636 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_488636 prefixEnd_488636 := by exact prefixLift 488636
  have htrace : WordTrace (prefixWord ++ tailWord_488636) baseStart_488636 baseEnd_488636 := by
    simpa [prefixWord, tailWord_488636, baseEnd_488636] using wordTrace_append hprefix tailTrace_488636
  have hstable : (prefixWord ++ tailWord_488636).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488636).length < 2 ^ (prefixWord ++ tailWord_488636).sum := by decide
  have hdescent : baseEnd_488636 < baseStart_488636 := by decide
  rcases family_descends (prefixWord ++ tailWord_488636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488706 : List Nat := [3, 4, 1, 1, 4, 1, 1, 4]
def baseStart_488706 : Nat := 118140960795 + 488706 * 2 ^ 59
def prefixEnd_488706 : Nat := 4983230072969 + 3 ^ 40 * 488706 * 2
def baseEnd_488706 : Nat := 148705823251123063245919

theorem tailTrace_488706 : CollatzResearch.WordTrace tailWord_488706 prefixEnd_488706 148705823251123063245919 := by
  unfold tailWord_488706
  simp only [CollatzResearch.WordTrace]
  refine ⟨4456143041877275296243493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11883048111672734123315981 4456143041877275296243493)
  ·
    refine ⟨835526820351989118045655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4456143041877275296243493 835526820351989118045655)
    ·
      refine ⟨1253290230527983677068483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 835526820351989118045655 1253290230527983677068483)
      ·
        refine ⟨1879935345791975515602725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1253290230527983677068483 1879935345791975515602725)
        ·
          refine ⟨352487877335995409175511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1879935345791975515602725 352487877335995409175511)
          ·
            refine ⟨528731816003993113763267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 352487877335995409175511 528731816003993113763267)
            ·
              refine ⟨793097724005989670644901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 528731816003993113763267 793097724005989670644901)
              ·
                refine ⟨148705823251123063245919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 793097724005989670644901 148705823251123063245919)
                ·
                  rfl

theorem cell19_488706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 4].length) (baseStart_488706 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_488706 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_488706 prefixEnd_488706 := by exact prefixLift 488706
  have htrace : WordTrace (prefixWord ++ tailWord_488706) baseStart_488706 baseEnd_488706 := by
    simpa [prefixWord, tailWord_488706, baseEnd_488706] using wordTrace_append hprefix tailTrace_488706
  have hstable : (prefixWord ++ tailWord_488706).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488706).length < 2 ^ (prefixWord ++ tailWord_488706).sum := by decide
  have hdescent : baseEnd_488706 < baseStart_488706 := by decide
  rcases family_descends (prefixWord ++ tailWord_488706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488752 : List Nat := [2, 1, 1, 1, 2, 2, 10]
def baseStart_488752 : Nat := 118140960795 + 488752 * 2 ^ 59
def prefixEnd_488752 : Nat := 4983230072969 + 3 ^ 40 * 488752 * 2
def baseEnd_488752 : Nat := 49573273451136195407857

theorem tailTrace_488752 : CollatzResearch.WordTrace tailWord_488752 prefixEnd_488752 49573273451136195407857 := by
  unfold tailWord_488752
  simp only [CollatzResearch.WordTrace]
  refine ⟨8913124962671225520574255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11884166616894967360765673 8913124962671225520574255)
  ·
    refine ⟨13369687444006838280861383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8913124962671225520574255 13369687444006838280861383)
    ·
      refine ⟨20054531166010257421292075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13369687444006838280861383 20054531166010257421292075)
      ·
        refine ⟨30081796749015386131938113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20054531166010257421292075 30081796749015386131938113)
        ·
          refine ⟨22561347561761539598953585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30081796749015386131938113 22561347561761539598953585)
          ·
            refine ⟨16921010671321154699215189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22561347561761539598953585 16921010671321154699215189)
            ·
              refine ⟨49573273451136195407857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16921010671321154699215189 49573273451136195407857)
              ·
                rfl

theorem cell19_488752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 10].length) (baseStart_488752 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_488752 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_488752 prefixEnd_488752 := by exact prefixLift 488752
  have htrace : WordTrace (prefixWord ++ tailWord_488752) baseStart_488752 baseEnd_488752 := by
    simpa [prefixWord, tailWord_488752, baseEnd_488752] using wordTrace_append hprefix tailTrace_488752
  have hstable : (prefixWord ++ tailWord_488752).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488752).length < 2 ^ (prefixWord ++ tailWord_488752).sum := by decide
  have hdescent : baseEnd_488752 < baseStart_488752 := by decide
  rcases family_descends (prefixWord ++ tailWord_488752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488771 : List Nat := [1, 1, 1, 3, 1, 3, 1, 8]
def baseStart_488771 : Nat := 118140960795 + 488771 * 2 ^ 59
def prefixEnd_488771 : Nat := 4983230072969 + 3 ^ 40 * 488771 * 2
def baseEnd_488771 : Nat := 148725601765222171801297

theorem tailTrace_488771 : CollatzResearch.WordTrace tailWord_488771 prefixEnd_488771 148725601765222171801297 := by
  unfold tailWord_488771
  simp only [CollatzResearch.WordTrace]
  refine ⟨17826942912273617286090167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11884628608182411524060111 17826942912273617286090167)
  ·
    refine ⟨26740414368410425929135251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17826942912273617286090167 26740414368410425929135251)
    ·
      refine ⟨40110621552615638893702877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26740414368410425929135251 40110621552615638893702877)
      ·
        refine ⟨15041483082230864585138579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40110621552615638893702877 15041483082230864585138579)
        ·
          refine ⟨22562224623346296877707869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15041483082230864585138579 22562224623346296877707869)
          ·
            refine ⟨8460834233754861329140451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22562224623346296877707869 8460834233754861329140451)
            ·
              refine ⟨12691251350632291993710677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8460834233754861329140451 12691251350632291993710677)
              ·
                refine ⟨148725601765222171801297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12691251350632291993710677 148725601765222171801297)
                ·
                  rfl

theorem cell19_488771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 8].length) (baseStart_488771 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_488771 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_488771 prefixEnd_488771 := by exact prefixLift 488771
  have htrace : WordTrace (prefixWord ++ tailWord_488771) baseStart_488771 baseEnd_488771 := by
    simpa [prefixWord, tailWord_488771, baseEnd_488771] using wordTrace_append hprefix tailTrace_488771
  have hstable : (prefixWord ++ tailWord_488771).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488771).length < 2 ^ (prefixWord ++ tailWord_488771).sum := by decide
  have hdescent : baseEnd_488771 < baseStart_488771 := by decide
  rcases family_descends (prefixWord ++ tailWord_488771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488788 : List Nat := [2, 4, 1, 1, 2, 1, 3, 5]
def baseStart_488788 : Nat := 118140960795 + 488788 * 2 ^ 59
def prefixEnd_488788 : Nat := 4983230072969 + 3 ^ 40 * 488788 * 2
def baseEnd_488788 : Nat := 148730774607371169423473

theorem tailTrace_488788 : CollatzResearch.WordTrace tailWord_488788 prefixEnd_488788 148730774607371169423473 := by
  unfold tailWord_488788
  simp only [CollatzResearch.WordTrace]
  refine ⟨8913781476606014594729509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11885041968808019459639345 8913781476606014594729509)
  ·
    refine ⟨1671334026863627736511783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8913781476606014594729509 1671334026863627736511783)
    ·
      refine ⟨2507001040295441604767675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1671334026863627736511783 2507001040295441604767675)
      ·
        refine ⟨3760501560443162407151513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2507001040295441604767675 3760501560443162407151513)
        ·
          refine ⟨2820376170332371805363635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3760501560443162407151513 2820376170332371805363635)
          ·
            refine ⟨4230564255498557708045453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2820376170332371805363635 4230564255498557708045453)
            ·
              refine ⟨1586461595811959140517045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4230564255498557708045453 1586461595811959140517045)
              ·
                refine ⟨148730774607371169423473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1586461595811959140517045 148730774607371169423473)
                ·
                  rfl

theorem cell19_488788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 5].length) (baseStart_488788 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_488788 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_488788 prefixEnd_488788 := by exact prefixLift 488788
  have htrace : WordTrace (prefixWord ++ tailWord_488788) baseStart_488788 baseEnd_488788 := by
    simpa [prefixWord, tailWord_488788, baseEnd_488788] using wordTrace_append hprefix tailTrace_488788
  have hstable : (prefixWord ++ tailWord_488788).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488788).length < 2 ^ (prefixWord ++ tailWord_488788).sum := by decide
  have hdescent : baseEnd_488788 < baseStart_488788 := by decide
  rcases family_descends (prefixWord ++ tailWord_488788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488862 : List Nat := [4, 3, 1, 2, 2, 7]
def baseStart_488862 : Nat := 118140960795 + 488862 * 2 ^ 59
def prefixEnd_488862 : Nat := 4983230072969 + 3 ^ 40 * 488862 * 2
def baseEnd_488862 : Nat := 16528143520551213753203

theorem tailTrace_488862 : CollatzResearch.WordTrace tailWord_488862 prefixEnd_488862 16528143520551213753203 := by
  unfold tailWord_488862
  simp only [CollatzResearch.WordTrace]
  refine ⟨2228782744367992478456605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11886841303295959885101893 2228782744367992478456605)
  ·
    refine ⟨835793529137997179421227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2228782744367992478456605 835793529137997179421227)
    ·
      refine ⟨1253690293706995769131841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 835793529137997179421227 1253690293706995769131841)
      ·
        refine ⟨940267720280246826848881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1253690293706995769131841 940267720280246826848881)
        ·
          refine ⟨705200790210185120136661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 940267720280246826848881 705200790210185120136661)
          ·
            refine ⟨16528143520551213753203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 705200790210185120136661 16528143520551213753203)
            ·
              rfl

theorem cell19_488862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 7].length) (baseStart_488862 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_488862 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_488862 prefixEnd_488862 := by exact prefixLift 488862
  have htrace : WordTrace (prefixWord ++ tailWord_488862) baseStart_488862 baseEnd_488862 := by
    simpa [prefixWord, tailWord_488862, baseEnd_488862] using wordTrace_append hprefix tailTrace_488862
  have hstable : (prefixWord ++ tailWord_488862).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488862).length < 2 ^ (prefixWord ++ tailWord_488862).sum := by decide
  have hdescent : baseEnd_488862 < baseStart_488862 := by decide
  rcases family_descends (prefixWord ++ tailWord_488862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488957 : List Nat := [1, 4, 1, 1, 1, 6, 2, 3]
def baseStart_488957 : Nat := 118140960795 + 488957 * 2 ^ 59
def prefixEnd_488957 : Nat := 4983230072969 + 3 ^ 40 * 488957 * 2
def baseEnd_488957 : Nat := 148782198744028851667457

theorem tailTrace_488957 : CollatzResearch.WordTrace tailWord_488957 prefixEnd_488957 148782198744028851667457 := by
  unfold tailWord_488957
  simp only [CollatzResearch.WordTrace]
  refine ⟨17833726889599771052361125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11889151259733180701574083 17833726889599771052361125)
  ·
    refine ⟨3343823791799957072317711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17833726889599771052361125 3343823791799957072317711)
    ·
      refine ⟨5015735687699935608476567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3343823791799957072317711 5015735687699935608476567)
      ·
        refine ⟨7523603531549903412714851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5015735687699935608476567 7523603531549903412714851)
        ·
          refine ⟨11285405297324855119072277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7523603531549903412714851 11285405297324855119072277)
          ·
            refine ⟨529003373312102583706513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 11285405297324855119072277 529003373312102583706513)
            ·
              refine ⟨396752529984076937779885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 529003373312102583706513 396752529984076937779885)
              ·
                refine ⟨148782198744028851667457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 396752529984076937779885 148782198744028851667457)
                ·
                  rfl

theorem cell19_488957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 2, 3].length) (baseStart_488957 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_488957 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_488957 prefixEnd_488957 := by exact prefixLift 488957
  have htrace : WordTrace (prefixWord ++ tailWord_488957) baseStart_488957 baseEnd_488957 := by
    simpa [prefixWord, tailWord_488957, baseEnd_488957] using wordTrace_append hprefix tailTrace_488957
  have hstable : (prefixWord ++ tailWord_488957).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488957).length < 2 ^ (prefixWord ++ tailWord_488957).sum := by decide
  have hdescent : baseEnd_488957 < baseStart_488957 := by decide
  rcases family_descends (prefixWord ++ tailWord_488957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489018 : List Nat := [3, 1, 1, 1, 3, 2, 1, 7]
def baseStart_489018 : Nat := 118140960795 + 489018 * 2 ^ 59
def prefixEnd_489018 : Nat := 4983230072969 + 3 ^ 40 * 489018 * 2
def baseEnd_489018 : Nat := 148800760118798784311735

theorem tailTrace_489018 : CollatzResearch.WordTrace tailWord_489018 prefixEnd_489018 148800760118798784311735 := by
  unfold tailWord_489018
  simp only [CollatzResearch.WordTrace]
  refine ⟨4458987935594694617582927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11890634494919185646887805 4458987935594694617582927)
  ·
    refine ⟨6688481903392041926374391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4458987935594694617582927 6688481903392041926374391)
    ·
      refine ⟨10032722855088062889561587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6688481903392041926374391 10032722855088062889561587)
      ·
        refine ⟨15049084282632094334342381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10032722855088062889561587 15049084282632094334342381)
        ·
          refine ⟨5643406605987035375378393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15049084282632094334342381 5643406605987035375378393)
          ·
            refine ⟨4232554954490276531533795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5643406605987035375378393 4232554954490276531533795)
            ·
              refine ⟨6348832431735414797300693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4232554954490276531533795 6348832431735414797300693)
              ·
                refine ⟨148800760118798784311735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6348832431735414797300693 148800760118798784311735)
                ·
                  rfl

theorem cell19_489018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 7].length) (baseStart_489018 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_489018 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_489018 prefixEnd_489018 := by exact prefixLift 489018
  have htrace : WordTrace (prefixWord ++ tailWord_489018) baseStart_489018 baseEnd_489018 := by
    simpa [prefixWord, tailWord_489018, baseEnd_489018] using wordTrace_append hprefix tailTrace_489018
  have hstable : (prefixWord ++ tailWord_489018).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489018).length < 2 ^ (prefixWord ++ tailWord_489018).sum := by decide
  have hdescent : baseEnd_489018 < baseStart_489018 := by decide
  rcases family_descends (prefixWord ++ tailWord_489018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489046 : List Nat := [5, 2, 2, 2, 2, 1, 1, 4]
def baseStart_489046 : Nat := 118140960795 + 489046 * 2 ^ 59
def prefixEnd_489046 : Nat := 4983230072969 + 3 ^ 40 * 489046 * 2
def baseEnd_489046 : Nat := 148809280094103015689437

theorem tailTrace_489046 : CollatzResearch.WordTrace tailWord_489046 prefixEnd_489046 148809280094103015689437 := by
  unfold tailWord_489046
  simp only [CollatzResearch.WordTrace]
  refine ⟨1114810811642333703271937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11891315324184892834900661 1114810811642333703271937)
  ·
    refine ⟨836108108731750277453953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1114810811642333703271937 836108108731750277453953)
    ·
      refine ⟨627081081548812708090465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 836108108731750277453953 627081081548812708090465)
      ·
        refine ⟨470310811161609531067849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 627081081548812708090465 470310811161609531067849)
        ·
          refine ⟨352733108371207148300887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 470310811161609531067849 352733108371207148300887)
          ·
            refine ⟨529099662556810722451331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 352733108371207148300887 529099662556810722451331)
            ·
              refine ⟨793649493835216083676997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 529099662556810722451331 793649493835216083676997)
              ·
                refine ⟨148809280094103015689437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 793649493835216083676997 148809280094103015689437)
                ·
                  rfl

theorem cell19_489046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 4].length) (baseStart_489046 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_489046 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_489046 prefixEnd_489046 := by exact prefixLift 489046
  have htrace : WordTrace (prefixWord ++ tailWord_489046) baseStart_489046 baseEnd_489046 := by
    simpa [prefixWord, tailWord_489046, baseEnd_489046] using wordTrace_append hprefix tailTrace_489046
  have hstable : (prefixWord ++ tailWord_489046).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489046).length < 2 ^ (prefixWord ++ tailWord_489046).sum := by decide
  have hdescent : baseEnd_489046 < baseStart_489046 := by decide
  rcases family_descends (prefixWord ++ tailWord_489046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489052 : List Nat := [2, 2, 4, 1, 2, 3, 1, 4]
def baseStart_489052 : Nat := 118140960795 + 489052 * 2 ^ 59
def prefixEnd_489052 : Nat := 4983230072969 + 3 ^ 40 * 489052 * 2
def baseEnd_489052 : Nat := 148811105803096779556087

theorem tailTrace_489052 : CollatzResearch.WordTrace tailWord_489052 prefixEnd_489052 148811105803096779556087 := by
  unfold tailWord_489052
  simp only [CollatzResearch.WordTrace]
  refine ⟨8918595912127801138534705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11891461216170401518046273 8918595912127801138534705)
  ·
    refine ⟨6688946934095850853901029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8918595912127801138534705 6688946934095850853901029)
    ·
      refine ⟨1254177550142972035106443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6688946934095850853901029 1254177550142972035106443)
      ·
        refine ⟨1881266325214458052659665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1254177550142972035106443 1881266325214458052659665)
        ·
          refine ⟨1410949743910843539494749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1881266325214458052659665 1410949743910843539494749)
          ·
            refine ⟨529106153966566327310531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1410949743910843539494749 529106153966566327310531)
            ·
              refine ⟨793659230949849490965797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 529106153966566327310531 793659230949849490965797)
              ·
                refine ⟨148811105803096779556087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 793659230949849490965797 148811105803096779556087)
                ·
                  rfl

theorem cell19_489052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 4].length) (baseStart_489052 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_489052 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_489052 prefixEnd_489052 := by exact prefixLift 489052
  have htrace : WordTrace (prefixWord ++ tailWord_489052) baseStart_489052 baseEnd_489052 := by
    simpa [prefixWord, tailWord_489052, baseEnd_489052] using wordTrace_append hprefix tailTrace_489052
  have hstable : (prefixWord ++ tailWord_489052).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489052).length < 2 ^ (prefixWord ++ tailWord_489052).sum := by decide
  have hdescent : baseEnd_489052 < baseStart_489052 := by decide
  rcases family_descends (prefixWord ++ tailWord_489052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489092 : List Nat := [2, 3, 2, 1, 4, 1, 6]
def baseStart_489092 : Nat := 118140960795 + 489092 * 2 ^ 59
def prefixEnd_489092 : Nat := 4983230072969 + 3 ^ 40 * 489092 * 2
def baseEnd_489092 : Nat := 49607759065462846222363

theorem tailTrace_489092 : CollatzResearch.WordTrace tailWord_489092 prefixEnd_489092 49607759065462846222363 := by
  unfold tailWord_489092
  simp only [CollatzResearch.WordTrace]
  refine ⟨8919325372055344554262765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11892433829407126072350353 8919325372055344554262765)
  ·
    refine ⟨3344747014520754207848537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8919325372055344554262765 3344747014520754207848537)
    ·
      refine ⟨2508560260890565655886403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3344747014520754207848537 2508560260890565655886403)
      ·
        refine ⟨3762840391335848483829605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2508560260890565655886403 3762840391335848483829605)
        ·
          refine ⟨705532573375471590718051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3762840391335848483829605 705532573375471590718051)
          ·
            refine ⟨1058298860063207386077077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 705532573375471590718051 1058298860063207386077077)
            ·
              refine ⟨49607759065462846222363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1058298860063207386077077 49607759065462846222363)
              ·
                rfl

theorem cell19_489092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 6].length) (baseStart_489092 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_489092 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_489092 prefixEnd_489092 := by exact prefixLift 489092
  have htrace : WordTrace (prefixWord ++ tailWord_489092) baseStart_489092 baseEnd_489092 := by
    simpa [prefixWord, tailWord_489092, baseEnd_489092] using wordTrace_append hprefix tailTrace_489092
  have hstable : (prefixWord ++ tailWord_489092).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489092).length < 2 ^ (prefixWord ++ tailWord_489092).sum := by decide
  have hdescent : baseEnd_489092 < baseStart_489092 := by decide
  rcases family_descends (prefixWord ++ tailWord_489092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489189 : List Nat := [1, 3, 1, 4, 1, 1, 1, 7]
def baseStart_489189 : Nat := 118140960795 + 489189 * 2 ^ 59
def prefixEnd_489189 : Nat := 4983230072969 + 3 ^ 40 * 489189 * 2
def baseEnd_489189 : Nat := 148852792825121054511269

theorem tailTrace_489189 : CollatzResearch.WordTrace tailWord_489189 prefixEnd_489189 148852792825121054511269 := by
  unfold tailWord_489189
  simp only [CollatzResearch.WordTrace]
  refine ⟨17842188624759274674806621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11894792416506183116537747 17842188624759274674806621)
  ·
    refine ⟨6690820734284728003052483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17842188624759274674806621 6690820734284728003052483)
    ·
      refine ⟨10036231101427092004578725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6690820734284728003052483 10036231101427092004578725)
      ·
        refine ⟨1881793331517579750858511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10036231101427092004578725 1881793331517579750858511)
        ·
          refine ⟨2822689997276369626287767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1881793331517579750858511 2822689997276369626287767)
          ·
            refine ⟨4234034995914554439431651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2822689997276369626287767 4234034995914554439431651)
            ·
              refine ⟨6351052493871831659147477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4234034995914554439431651 6351052493871831659147477)
              ·
                refine ⟨148852792825121054511269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6351052493871831659147477 148852792825121054511269)
                ·
                  rfl

theorem cell19_489189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 7].length) (baseStart_489189 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_489189 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_489189 prefixEnd_489189 := by exact prefixLift 489189
  have htrace : WordTrace (prefixWord ++ tailWord_489189) baseStart_489189 baseEnd_489189 := by
    simpa [prefixWord, tailWord_489189, baseEnd_489189] using wordTrace_append hprefix tailTrace_489189
  have hstable : (prefixWord ++ tailWord_489189).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489189).length < 2 ^ (prefixWord ++ tailWord_489189).sum := by decide
  have hdescent : baseEnd_489189 < baseStart_489189 := by decide
  rcases family_descends (prefixWord ++ tailWord_489189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489204 : List Nat := [2, 6, 1, 1, 1, 8]
def baseStart_489204 : Nat := 118140960795 + 489204 * 2 ^ 59
def prefixEnd_489204 : Nat := 4983230072969 + 3 ^ 40 * 489204 * 2
def baseEnd_489204 : Nat := 16539706344178384908655

theorem tailTrace_489204 : CollatzResearch.WordTrace tailWord_489204 prefixEnd_489204 16539706344178384908655 := by
  unfold tailWord_489204
  simp only [CollatzResearch.WordTrace]
  refine ⟨8921367859852466118301333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11895157146469954824401777 8921367859852466118301333)
  ·
    refine ⟨418189118430584349295375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 8921367859852466118301333 418189118430584349295375)
    ·
      refine ⟨627283677645876523943063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418189118430584349295375 627283677645876523943063)
      ·
        refine ⟨940925516468814785914595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 627283677645876523943063 940925516468814785914595)
        ·
          refine ⟨1411388274703222178871893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 940925516468814785914595 1411388274703222178871893)
          ·
            refine ⟨16539706344178384908655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1411388274703222178871893 16539706344178384908655)
            ·
              rfl

theorem cell19_489204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 8].length) (baseStart_489204 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_489204 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_489204 prefixEnd_489204 := by exact prefixLift 489204
  have htrace : WordTrace (prefixWord ++ tailWord_489204) baseStart_489204 baseEnd_489204 := by
    simpa [prefixWord, tailWord_489204, baseEnd_489204] using wordTrace_append hprefix tailTrace_489204
  have hstable : (prefixWord ++ tailWord_489204).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489204).length < 2 ^ (prefixWord ++ tailWord_489204).sum := by decide
  have hdescent : baseEnd_489204 < baseStart_489204 := by decide
  rcases family_descends (prefixWord ++ tailWord_489204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489223 : List Nat := [1, 1, 4, 4, 2, 2, 1, 4]
def baseStart_489223 : Nat := 118140960795 + 489223 * 2 ^ 59
def prefixEnd_489223 : Nat := 4983230072969 + 3 ^ 40 * 489223 * 2
def baseEnd_489223 : Nat := 148863138509419049755621

theorem tailTrace_489223 : CollatzResearch.WordTrace tailWord_489223 prefixEnd_489223 148863138509419049755621 := by
  unfold tailWord_489223
  simp only [CollatzResearch.WordTrace]
  refine ⟨17843428706636098481544323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11895619137757398987696215 17843428706636098481544323)
  ·
    refine ⟨26765143059954147722316485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17843428706636098481544323 26765143059954147722316485)
    ·
      refine ⟨5018464323741402697934341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26765143059954147722316485 5018464323741402697934341)
      ·
        refine ⟨940962060701513005862689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5018464323741402697934341 940962060701513005862689)
        ·
          refine ⟨705721545526134754397017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 940962060701513005862689 705721545526134754397017)
          ·
            refine ⟨529291159144601065797763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 705721545526134754397017 529291159144601065797763)
            ·
              refine ⟨793936738716901598696645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 529291159144601065797763 793936738716901598696645)
              ·
                refine ⟨148863138509419049755621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 793936738716901598696645 148863138509419049755621)
                ·
                  rfl

theorem cell19_489223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 4].length) (baseStart_489223 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_489223 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_489223 prefixEnd_489223 := by exact prefixLift 489223
  have htrace : WordTrace (prefixWord ++ tailWord_489223) baseStart_489223 baseEnd_489223 := by
    simpa [prefixWord, tailWord_489223, baseEnd_489223] using wordTrace_append hprefix tailTrace_489223
  have hstable : (prefixWord ++ tailWord_489223).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489223).length < 2 ^ (prefixWord ++ tailWord_489223).sum := by decide
  have hdescent : baseEnd_489223 < baseStart_489223 := by decide
  rcases family_descends (prefixWord ++ tailWord_489223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489227 : List Nat := [1, 1, 1, 1, 5, 1, 5, 4]
def baseStart_489227 : Nat := 118140960795 + 489227 * 2 ^ 59
def prefixEnd_489227 : Nat := 4983230072969 + 3 ^ 40 * 489227 * 2
def baseEnd_489227 : Nat := 148864355648748225666721

theorem tailTrace_489227 : CollatzResearch.WordTrace tailWord_489227 prefixEnd_489227 148864355648748225666721 := by
  unfold tailWord_489227
  simp only [CollatzResearch.WordTrace]
  refine ⟨17843574598621607164689935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11895716399081071443126623 17843574598621607164689935)
  ·
    refine ⟨26765361897932410747034903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17843574598621607164689935 26765361897932410747034903)
    ·
      refine ⟨40148042846898616120552355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26765361897932410747034903 40148042846898616120552355)
      ·
        refine ⟨60222064270347924180828533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40148042846898616120552355 60222064270347924180828533)
        ·
          refine ⟨5645818525345117891952675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60222064270347924180828533 5645818525345117891952675)
          ·
            refine ⟨8468727788017676837929013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5645818525345117891952675 8468727788017676837929013)
            ·
              refine ⟨793943230126657203555845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8468727788017676837929013 793943230126657203555845)
              ·
                refine ⟨148864355648748225666721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 793943230126657203555845 148864355648748225666721)
                ·
                  rfl

theorem cell19_489227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 4].length) (baseStart_489227 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_489227 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_489227 prefixEnd_489227 := by exact prefixLift 489227
  have htrace : WordTrace (prefixWord ++ tailWord_489227) baseStart_489227 baseEnd_489227 := by
    simpa [prefixWord, tailWord_489227, baseEnd_489227] using wordTrace_append hprefix tailTrace_489227
  have hstable : (prefixWord ++ tailWord_489227).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489227).length < 2 ^ (prefixWord ++ tailWord_489227).sum := by decide
  have hdescent : baseEnd_489227 < baseStart_489227 := by decide
  rcases family_descends (prefixWord ++ tailWord_489227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489244 : List Nat := [2, 2, 3, 1, 1, 2, 5, 3]
def baseStart_489244 : Nat := 118140960795 + 489244 * 2 ^ 59
def prefixEnd_489244 : Nat := 4983230072969 + 3 ^ 40 * 489244 * 2
def baseEnd_489244 : Nat := 148869528490897223288897

theorem tailTrace_489244 : CollatzResearch.WordTrace tailWord_489244 prefixEnd_489244 148869528490897223288897 := by
  unfold tailWord_489244
  simp only [CollatzResearch.WordTrace]
  refine ⟨8922097319780009534029393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11896129759706679378705857 8922097319780009534029393)
  ·
    refine ⟨6691572989835007150522045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8922097319780009534029393 6691572989835007150522045)
    ·
      refine ⟨2509339871188127681445767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6691572989835007150522045 2509339871188127681445767)
      ·
        refine ⟨3764009806782191522168651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2509339871188127681445767 3764009806782191522168651)
        ·
          refine ⟨5646014710173287283252977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3764009806782191522168651 5646014710173287283252977)
          ·
            refine ⟨4234511032629965462439733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5646014710173287283252977 4234511032629965462439733)
            ·
              refine ⟨396985409309059262103725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4234511032629965462439733 396985409309059262103725)
              ·
                refine ⟨148869528490897223288897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 396985409309059262103725 148869528490897223288897)
                ·
                  rfl

theorem cell19_489244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 5, 3].length) (baseStart_489244 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_489244 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_489244 prefixEnd_489244 := by exact prefixLift 489244
  have htrace : WordTrace (prefixWord ++ tailWord_489244) baseStart_489244 baseEnd_489244 := by
    simpa [prefixWord, tailWord_489244, baseEnd_489244] using wordTrace_append hprefix tailTrace_489244
  have hstable : (prefixWord ++ tailWord_489244).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489244).length < 2 ^ (prefixWord ++ tailWord_489244).sum := by decide
  have hdescent : baseEnd_489244 < baseStart_489244 := by decide
  rcases family_descends (prefixWord ++ tailWord_489244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489265 : List Nat := [1, 2, 2, 3, 2, 3, 6]
def baseStart_489265 : Nat := 118140960795 + 489265 * 2 ^ 59
def prefixEnd_489265 : Nat := 4983230072969 + 3 ^ 40 * 489265 * 2
def baseEnd_489265 : Nat := 49625306157458465607391

theorem tailTrace_489265 : CollatzResearch.WordTrace tailWord_489265 prefixEnd_489265 49625306157458465607391 := by
  unfold tailWord_489265
  simp only [CollatzResearch.WordTrace]
  refine ⟨17844960572483939654573249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11896640381655959769715499 17844960572483939654573249)
  ·
    refine ⟨13383720429362954740929937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17844960572483939654573249 13383720429362954740929937)
    ·
      refine ⟨10037790322022216055697453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13383720429362954740929937 10037790322022216055697453)
      ·
        refine ⟨3764171370758331020886545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10037790322022216055697453 3764171370758331020886545)
        ·
          refine ⟨2823128528068748265664909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3764171370758331020886545 2823128528068748265664909)
          ·
            refine ⟨1058673198025780599624341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2823128528068748265664909 1058673198025780599624341)
            ·
              refine ⟨49625306157458465607391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1058673198025780599624341 49625306157458465607391)
              ·
                rfl

theorem cell19_489265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 6].length) (baseStart_489265 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_489265 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_489265 prefixEnd_489265 := by exact prefixLift 489265
  have htrace : WordTrace (prefixWord ++ tailWord_489265) baseStart_489265 baseEnd_489265 := by
    simpa [prefixWord, tailWord_489265, baseEnd_489265] using wordTrace_append hprefix tailTrace_489265
  have hstable : (prefixWord ++ tailWord_489265).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489265).length < 2 ^ (prefixWord ++ tailWord_489265).sum := by decide
  have hdescent : baseEnd_489265 < baseStart_489265 := by decide
  rcases family_descends (prefixWord ++ tailWord_489265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489301 : List Nat := [1, 3, 2, 2, 2, 2, 4, 3]
def baseStart_489301 : Nat := 118140960795 + 489301 * 2 ^ 59
def prefixEnd_489301 : Nat := 4983230072969 + 3 ^ 40 * 489301 * 2
def baseEnd_489301 : Nat := 148886872726337980022075

theorem tailTrace_489301 : CollatzResearch.WordTrace tailWord_489301 prefixEnd_489301 148886872726337980022075 := by
  unfold tailWord_489301
  simp only [CollatzResearch.WordTrace]
  refine ⟨17846273600353517802883757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11897515733569011868589171 17846273600353517802883757)
  ·
    refine ⟨6692352600132569176081409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17846273600353517802883757 6692352600132569176081409)
    ·
      refine ⟨5019264450099426882061057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6692352600132569176081409 5019264450099426882061057)
      ·
        refine ⟨3764448337574570161545793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5019264450099426882061057 3764448337574570161545793)
        ·
          refine ⟨2823336253180927621159345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3764448337574570161545793 2823336253180927621159345)
          ·
            refine ⟨2117502189885695715869509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2823336253180927621159345 2117502189885695715869509)
            ·
              refine ⟨397031660603567946725533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2117502189885695715869509 397031660603567946725533)
              ·
                refine ⟨148886872726337980022075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 397031660603567946725533 148886872726337980022075)
                ·
                  rfl

theorem cell19_489301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 4, 3].length) (baseStart_489301 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_489301 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_489301 prefixEnd_489301 := by exact prefixLift 489301
  have htrace : WordTrace (prefixWord ++ tailWord_489301) baseStart_489301 baseEnd_489301 := by
    simpa [prefixWord, tailWord_489301, baseEnd_489301] using wordTrace_append hprefix tailTrace_489301
  have hstable : (prefixWord ++ tailWord_489301).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489301).length < 2 ^ (prefixWord ++ tailWord_489301).sum := by decide
  have hdescent : baseEnd_489301 < baseStart_489301 := by decide
  rcases family_descends (prefixWord ++ tailWord_489301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489377 : List Nat := [1, 2, 3, 4, 3, 6]
def baseStart_489377 : Nat := 118140960795 + 489377 * 2 ^ 59
def prefixEnd_489377 : Nat := 4983230072969 + 3 ^ 40 * 489377 * 2
def baseEnd_489377 : Nat := 16545555374843591370331

theorem tailTrace_489377 : CollatzResearch.WordTrace tailWord_489377 prefixEnd_489377 16545555374843591370331 := by
  unfold tailWord_489377
  simp only [CollatzResearch.WordTrace]
  refine ⟨17849045548078182782650385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11899363698718788521766923 17849045548078182782650385)
  ·
    refine ⟨13386784161058637086987789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17849045548078182782650385 13386784161058637086987789)
    ·
      refine ⟨5020044060396988907620421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13386784161058637086987789 5020044060396988907620421)
      ·
        refine ⟨941258261324435420178829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5020044060396988907620421 941258261324435420178829)
        ·
          refine ⟨352971847996663282567061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 941258261324435420178829 352971847996663282567061)
          ·
            refine ⟨16545555374843591370331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 352971847996663282567061 16545555374843591370331)
            ·
              rfl

theorem cell19_489377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 6].length) (baseStart_489377 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_489377 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_489377 prefixEnd_489377 := by exact prefixLift 489377
  have htrace : WordTrace (prefixWord ++ tailWord_489377) baseStart_489377 baseEnd_489377 := by
    simpa [prefixWord, tailWord_489377, baseEnd_489377] using wordTrace_append hprefix tailTrace_489377
  have hstable : (prefixWord ++ tailWord_489377).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489377).length < 2 ^ (prefixWord ++ tailWord_489377).sum := by decide
  have hdescent : baseEnd_489377 < baseStart_489377 := by decide
  rcases family_descends (prefixWord ++ tailWord_489377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489390 : List Nat := [4, 1, 5, 1, 1, 2, 1, 4]
def baseStart_489390 : Nat := 118140960795 + 489390 * 2 ^ 59
def prefixEnd_489390 : Nat := 4983230072969 + 3 ^ 40 * 489390 * 2
def baseEnd_489390 : Nat := 148913954076412144044055

theorem tailTrace_489390 : CollatzResearch.WordTrace tailWord_489390 prefixEnd_489390 148913954076412144044055 := by
  unfold tailWord_489390
  simp only [CollatzResearch.WordTrace]
  refine ⟨2231189962128885750359203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11899679798020724001915749 2231189962128885750359203)
  ·
    refine ⟨3346784943193328625538805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2231189962128885750359203 3346784943193328625538805)
    ·
      refine ⟨313761088424374558644263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3346784943193328625538805 313761088424374558644263)
      ·
        refine ⟨470641632636561837966395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313761088424374558644263 470641632636561837966395)
        ·
          refine ⟨705962448954842756949593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 470641632636561837966395 705962448954842756949593)
          ·
            refine ⟨529471836716132067712195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 705962448954842756949593 529471836716132067712195)
            ·
              refine ⟨794207755074198101568293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 529471836716132067712195 794207755074198101568293)
              ·
                refine ⟨148913954076412144044055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 794207755074198101568293 148913954076412144044055)
                ·
                  rfl

theorem cell19_489390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 4].length) (baseStart_489390 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_489390 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_489390 prefixEnd_489390 := by exact prefixLift 489390
  have htrace : WordTrace (prefixWord ++ tailWord_489390) baseStart_489390 baseEnd_489390 := by
    simpa [prefixWord, tailWord_489390, baseEnd_489390] using wordTrace_append hprefix tailTrace_489390
  have hstable : (prefixWord ++ tailWord_489390).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489390).length < 2 ^ (prefixWord ++ tailWord_489390).sum := by decide
  have hdescent : baseEnd_489390 < baseStart_489390 := by decide
  rcases family_descends (prefixWord ++ tailWord_489390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489470 : List Nat := [4, 2, 2, 2, 1, 1, 4, 3]
def baseStart_489470 : Nat := 118140960795 + 489470 * 2 ^ 59
def prefixEnd_489470 : Nat := 4983230072969 + 3 ^ 40 * 489470 * 2
def baseEnd_489470 : Nat := 148938296862995662266059

theorem tailTrace_489470 : CollatzResearch.WordTrace tailWord_489470 prefixEnd_489470 148938296862995662266059 := by
  unfold tailWord_489470
  simp only [CollatzResearch.WordTrace]
  refine ⟨2231554692092657458223233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11901625024494173110523909 2231554692092657458223233)
  ·
    refine ⟨1673666019069493093667425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2231554692092657458223233 1673666019069493093667425)
    ·
      refine ⟨1255249514302119820250569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1673666019069493093667425 1255249514302119820250569)
      ·
        refine ⟨941437135726589865187927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1255249514302119820250569 941437135726589865187927)
        ·
          refine ⟨1412155703589884797781891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 941437135726589865187927 1412155703589884797781891)
          ·
            refine ⟨2118233555384827196672837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1412155703589884797781891 2118233555384827196672837)
            ·
              refine ⟨397168791634655099376157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2118233555384827196672837 397168791634655099376157)
              ·
                refine ⟨148938296862995662266059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 397168791634655099376157 148938296862995662266059)
                ·
                  rfl

theorem cell19_489470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 4, 3].length) (baseStart_489470 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_489470 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_489470 prefixEnd_489470 := by exact prefixLift 489470
  have htrace : WordTrace (prefixWord ++ tailWord_489470) baseStart_489470 baseEnd_489470 := by
    simpa [prefixWord, tailWord_489470, baseEnd_489470] using wordTrace_append hprefix tailTrace_489470
  have hstable : (prefixWord ++ tailWord_489470).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489470).length < 2 ^ (prefixWord ++ tailWord_489470).sum := by decide
  have hdescent : baseEnd_489470 < baseStart_489470 := by decide
  rcases family_descends (prefixWord ++ tailWord_489470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489485 : List Nat := [1, 7, 1, 2, 2, 1, 5]
def baseStart_489485 : Nat := 118140960795 + 489485 * 2 ^ 59
def prefixEnd_489485 : Nat := 4983230072969 + 3 ^ 40 * 489485 * 2
def baseEnd_489485 : Nat := 49647620378493357310895

theorem tailTrace_489485 : CollatzResearch.WordTrace tailWord_489485 prefixEnd_489485 49647620378493357310895 := by
  unfold tailWord_489485
  simp only [CollatzResearch.WordTrace]
  refine ⟨17852984631686917227581909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11901989754457944818387939 17852984631686917227581909)
  ·
    refine ⟨418429327305162122521451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 17852984631686917227581909 418429327305162122521451)
    ·
      refine ⟨627643990957743183782177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418429327305162122521451 627643990957743183782177)
      ·
        refine ⟨470732993218307387836633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 627643990957743183782177 470732993218307387836633)
        ·
          refine ⟨353049744913730540877475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 470732993218307387836633 353049744913730540877475)
          ·
            refine ⟨529574617370595811316213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 353049744913730540877475 529574617370595811316213)
            ·
              refine ⟨49647620378493357310895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 529574617370595811316213 49647620378493357310895)
              ·
                rfl

theorem cell19_489485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 5].length) (baseStart_489485 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_489485 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_489485 prefixEnd_489485 := by exact prefixLift 489485
  have htrace : WordTrace (prefixWord ++ tailWord_489485) baseStart_489485 baseEnd_489485 := by
    simpa [prefixWord, tailWord_489485, baseEnd_489485] using wordTrace_append hprefix tailTrace_489485
  have hstable : (prefixWord ++ tailWord_489485).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489485).length < 2 ^ (prefixWord ++ tailWord_489485).sum := by decide
  have hdescent : baseEnd_489485 < baseStart_489485 := by decide
  rcases family_descends (prefixWord ++ tailWord_489485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489565 : List Nat := [1, 4, 4, 1, 1, 3, 1, 4]
def baseStart_489565 : Nat := 118140960795 + 489565 * 2 ^ 59
def prefixEnd_489565 : Nat := 4983230072969 + 3 ^ 40 * 489565 * 2
def baseEnd_489565 : Nat := 148967203922063590154689

theorem tailTrace_489565 : CollatzResearch.WordTrace tailWord_489565 prefixEnd_489565 148967203922063590154689 := by
  unfold tailWord_489565
  simp only [CollatzResearch.WordTrace]
  refine ⟨17855902471397090890494149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11903934980931393926996099 17855902471397090890494149)
  ·
    refine ⟨3347981713386954541967653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17855902471397090890494149 3347981713386954541967653)
    ·
      refine ⟨627746571260053976618935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3347981713386954541967653 627746571260053976618935)
      ·
        refine ⟨941619856890080964928403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 627746571260053976618935 941619856890080964928403)
        ·
          refine ⟨1412429785335121447392605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 941619856890080964928403 1412429785335121447392605)
          ·
            refine ⟨529661169500670542772227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1412429785335121447392605 529661169500670542772227)
            ·
              refine ⟨794491754251005814158341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 529661169500670542772227 794491754251005814158341)
              ·
                refine ⟨148967203922063590154689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 794491754251005814158341 148967203922063590154689)
                ·
                  rfl

theorem cell19_489565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 4].length) (baseStart_489565 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_489565 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_489565 prefixEnd_489565 := by exact prefixLift 489565
  have htrace : WordTrace (prefixWord ++ tailWord_489565) baseStart_489565 baseEnd_489565 := by
    simpa [prefixWord, tailWord_489565, baseEnd_489565] using wordTrace_append hprefix tailTrace_489565
  have hstable : (prefixWord ++ tailWord_489565).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489565).length < 2 ^ (prefixWord ++ tailWord_489565).sum := by decide
  have hdescent : baseEnd_489565 < baseStart_489565 := by decide
  rcases family_descends (prefixWord ++ tailWord_489565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489586 : List Nat := [3, 2, 1, 2, 2, 3, 3, 3]
def baseStart_489586 : Nat := 118140960795 + 489586 * 2 ^ 59
def prefixEnd_489586 : Nat := 4983230072969 + 3 ^ 40 * 489586 * 2
def baseEnd_489586 : Nat := 148973593903541763687965

theorem tailTrace_489586 : CollatzResearch.WordTrace tailWord_489586 prefixEnd_489586 148973593903541763687965 := by
  unfold tailWord_489586
  simp only [CollatzResearch.WordTrace]
  refine ⟨4464167101080252869252153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11904445602880674318005741 4464167101080252869252153)
  ·
    refine ⟨3348125325810189651939115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4464167101080252869252153 3348125325810189651939115)
    ·
      refine ⟨5022187988715284477908673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3348125325810189651939115 5022187988715284477908673)
      ·
        refine ⟨3766640991536463358431505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5022187988715284477908673 3766640991536463358431505)
        ·
          refine ⟨2824980743652347518823629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3766640991536463358431505 2824980743652347518823629)
          ·
            refine ⟨1059367778869630319558861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2824980743652347518823629 1059367778869630319558861)
            ·
              refine ⟨397262917076111369834573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1059367778869630319558861 397262917076111369834573)
              ·
                refine ⟨148973593903541763687965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 397262917076111369834573 148973593903541763687965)
                ·
                  rfl

theorem cell19_489586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 3, 3].length) (baseStart_489586 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_489586 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_489586 prefixEnd_489586 := by exact prefixLift 489586
  have htrace : WordTrace (prefixWord ++ tailWord_489586) baseStart_489586 baseEnd_489586 := by
    simpa [prefixWord, tailWord_489586, baseEnd_489586] using wordTrace_append hprefix tailTrace_489586
  have hstable : (prefixWord ++ tailWord_489586).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489586).length < 2 ^ (prefixWord ++ tailWord_489586).sum := by decide
  have hdescent : baseEnd_489586 < baseStart_489586 := by decide
  rcases family_descends (prefixWord ++ tailWord_489586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489609 : List Nat := [1, 2, 1, 1, 4, 2, 8]
def baseStart_489609 : Nat := 118140960795 + 489609 * 2 ^ 59
def prefixEnd_489609 : Nat := 4983230072969 + 3 ^ 40 * 489609 * 2
def baseEnd_489609 : Nat := 49660197484894841725597

theorem tailTrace_489609 : CollatzResearch.WordTrace tailWord_489609 prefixEnd_489609 49660197484894841725597 := by
  unfold tailWord_489609
  simp only [CollatzResearch.WordTrace]
  refine ⟨17857507283237686405095881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11905004855491790936730587 17857507283237686405095881)
  ·
    refine ⟨13393130462428264803821911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17857507283237686405095881 13393130462428264803821911)
    ·
      refine ⟨20089695693642397205732867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13393130462428264803821911 20089695693642397205732867)
      ·
        refine ⟨30134543540463595808599301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20089695693642397205732867 30134543540463595808599301)
        ·
          refine ⟨5650226913836924214112369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30134543540463595808599301 5650226913836924214112369)
          ·
            refine ⟨4237670185377693160584277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5650226913836924214112369 4237670185377693160584277)
            ·
              refine ⟨49660197484894841725597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4237670185377693160584277 49660197484894841725597)
              ·
                rfl

theorem cell19_489609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 8].length) (baseStart_489609 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_489609 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_489609 prefixEnd_489609 := by exact prefixLift 489609
  have htrace : WordTrace (prefixWord ++ tailWord_489609) baseStart_489609 baseEnd_489609 := by
    simpa [prefixWord, tailWord_489609, baseEnd_489609] using wordTrace_append hprefix tailTrace_489609
  have hstable : (prefixWord ++ tailWord_489609).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489609).length < 2 ^ (prefixWord ++ tailWord_489609).sum := by decide
  have hdescent : baseEnd_489609 < baseStart_489609 := by decide
  rcases family_descends (prefixWord ++ tailWord_489609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489639 : List Nat := [1, 1, 6, 2, 3, 1, 2, 3]
def baseStart_489639 : Nat := 118140960795 + 489639 * 2 ^ 59
def prefixEnd_489639 : Nat := 4983230072969 + 3 ^ 40 * 489639 * 2
def baseEnd_489639 : Nat := 148989720999653344510043

theorem tailTrace_489639 : CollatzResearch.WordTrace tailWord_489639 prefixEnd_489639 148989720999653344510043 := by
  unfold tailWord_489639
  simp only [CollatzResearch.WordTrace]
  refine ⟨17858601473129001528687971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11905734315419334352458647 17858601473129001528687971)
  ·
    refine ⟨26787902209693502293031957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17858601473129001528687971 26787902209693502293031957)
    ·
      refine ⟨1255682916079382919985873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 26787902209693502293031957 1255682916079382919985873)
      ·
        refine ⟨941762187059537189989405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1255682916079382919985873 941762187059537189989405)
        ·
          refine ⟨353160820147326446246027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 941762187059537189989405 353160820147326446246027)
          ·
            refine ⟨529741230220989669369041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 353160820147326446246027 529741230220989669369041)
            ·
              refine ⟨397305922665742252026781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 529741230220989669369041 397305922665742252026781)
              ·
                refine ⟨148989720999653344510043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 397305922665742252026781 148989720999653344510043)
                ·
                  rfl

theorem cell19_489639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 2, 3].length) (baseStart_489639 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_489639 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_489639 prefixEnd_489639 := by exact prefixLift 489639
  have htrace : WordTrace (prefixWord ++ tailWord_489639) baseStart_489639 baseEnd_489639 := by
    simpa [prefixWord, tailWord_489639, baseEnd_489639] using wordTrace_append hprefix tailTrace_489639
  have hstable : (prefixWord ++ tailWord_489639).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489639).length < 2 ^ (prefixWord ++ tailWord_489639).sum := by decide
  have hdescent : baseEnd_489639 < baseStart_489639 := by decide
  rcases family_descends (prefixWord ++ tailWord_489639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489662 : List Nat := [4, 2, 1, 1, 4, 2, 5]
def baseStart_489662 : Nat := 118140960795 + 489662 * 2 ^ 59
def prefixEnd_489662 : Nat := 4983230072969 + 3 ^ 40 * 489662 * 2
def baseEnd_489662 : Nat := 49665573183598701999623

theorem tailTrace_489662 : CollatzResearch.WordTrace tailWord_489662 prefixEnd_489662 49665573183598701999623 := by
  unfold tailWord_489662
  simp only [CollatzResearch.WordTrace]
  refine ⟨2232430044005709557096905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11906293568030450971183493 2232430044005709557096905)
  ·
    refine ⟨1674322533004282167822679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2232430044005709557096905 1674322533004282167822679)
    ·
      refine ⟨2511483799506423251734019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1674322533004282167822679 2511483799506423251734019)
      ·
        refine ⟨3767225699259634877601029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2511483799506423251734019 3767225699259634877601029)
        ·
          refine ⟨706354818611181539550193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3767225699259634877601029 706354818611181539550193)
          ·
            refine ⟨529766113958386154662645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 706354818611181539550193 529766113958386154662645)
            ·
              refine ⟨49665573183598701999623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 529766113958386154662645 49665573183598701999623)
              ·
                rfl

theorem cell19_489662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 5].length) (baseStart_489662 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_489662 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_489662 prefixEnd_489662 := by exact prefixLift 489662
  have htrace : WordTrace (prefixWord ++ tailWord_489662) baseStart_489662 baseEnd_489662 := by
    simpa [prefixWord, tailWord_489662, baseEnd_489662] using wordTrace_append hprefix tailTrace_489662
  have hstable : (prefixWord ++ tailWord_489662).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489662).length < 2 ^ (prefixWord ++ tailWord_489662).sum := by decide
  have hdescent : baseEnd_489662 < baseStart_489662 := by decide
  rcases family_descends (prefixWord ++ tailWord_489662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489664 : List Nat := [2, 1, 1, 2, 5, 3, 5]
def baseStart_489664 : Nat := 118140960795 + 489664 * 2 ^ 59
def prefixEnd_489664 : Nat := 4983230072969 + 3 ^ 40 * 489664 * 2
def baseEnd_489664 : Nat := 49665776040153564651473

theorem tailTrace_489664 : CollatzResearch.WordTrace tailWord_489664 prefixEnd_489664 49665776040153564651473 := by
  unfold tailWord_489664
  simp only [CollatzResearch.WordTrace]
  refine ⟨8929756649019215399174023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11906342198692287198898697 8929756649019215399174023)
  ·
    refine ⟨13394634973528823098761035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8929756649019215399174023 13394634973528823098761035)
    ·
      refine ⟨20091952460293234648141553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13394634973528823098761035 20091952460293234648141553)
      ·
        refine ⟨15068964345219925986106165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20091952460293234648141553 15068964345219925986106165)
        ·
          refine ⟨1412715407364368061197453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15068964345219925986106165 1412715407364368061197453)
          ·
            refine ⟨529768277761638022949045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1412715407364368061197453 529768277761638022949045)
            ·
              refine ⟨49665776040153564651473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 529768277761638022949045 49665776040153564651473)
              ·
                rfl

theorem cell19_489664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 5].length) (baseStart_489664 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_489664 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_489664 prefixEnd_489664 := by exact prefixLift 489664
  have htrace : WordTrace (prefixWord ++ tailWord_489664) baseStart_489664 baseEnd_489664 := by
    simpa [prefixWord, tailWord_489664, baseEnd_489664] using wordTrace_append hprefix tailTrace_489664
  have hstable : (prefixWord ++ tailWord_489664).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489664).length < 2 ^ (prefixWord ++ tailWord_489664).sum := by decide
  have hdescent : baseEnd_489664 < baseStart_489664 := by decide
  rcases family_descends (prefixWord ++ tailWord_489664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489761 : List Nat := [1, 2, 3, 2, 1, 1, 2, 7]
def baseStart_489761 : Nat := 118140960795 + 489761 * 2 ^ 59
def prefixEnd_489761 : Nat := 4983230072969 + 3 ^ 40 * 489761 * 2
def baseEnd_489761 : Nat := 149026843749193209798599

theorem tailTrace_489761 : CollatzResearch.WordTrace tailWord_489761 prefixEnd_489761 149026843749193209798599 := by
  unfold tailWord_489761
  simp only [CollatzResearch.WordTrace]
  refine ⟨17863051178687016364629137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11908700785791344243086091 17863051178687016364629137)
  ·
    refine ⟨13397288384015262273471853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17863051178687016364629137 13397288384015262273471853)
    ·
      refine ⟨5023983144005723352551945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13397288384015262273471853 5023983144005723352551945)
      ·
        refine ⟨3767987358004292514413959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5023983144005723352551945 3767987358004292514413959)
        ·
          refine ⟨5651981037006438771620939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3767987358004292514413959 5651981037006438771620939)
          ·
            refine ⟨8477971555509658157431409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5651981037006438771620939 8477971555509658157431409)
            ·
              refine ⟨6358478666632243618073557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8477971555509658157431409 6358478666632243618073557)
              ·
                refine ⟨149026843749193209798599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6358478666632243618073557 149026843749193209798599)
                ·
                  rfl

theorem cell19_489761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 7].length) (baseStart_489761 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_489761 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_489761 prefixEnd_489761 := by exact prefixLift 489761
  have htrace : WordTrace (prefixWord ++ tailWord_489761) baseStart_489761 baseEnd_489761 := by
    simpa [prefixWord, tailWord_489761, baseEnd_489761] using wordTrace_append hprefix tailTrace_489761
  have hstable : (prefixWord ++ tailWord_489761).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489761).length < 2 ^ (prefixWord ++ tailWord_489761).sum := by decide
  have hdescent : baseEnd_489761 < baseStart_489761 := by decide
  rcases family_descends (prefixWord ++ tailWord_489761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489778 : List Nat := [3, 2, 1, 1, 5, 1, 6]
def baseStart_489778 : Nat := 118140960795 + 489778 * 2 ^ 59
def prefixEnd_489778 : Nat := 4983230072969 + 3 ^ 40 * 489778 * 2
def baseEnd_489778 : Nat := 49677338863780735806925

theorem tailTrace_489778 : CollatzResearch.WordTrace tailWord_489778 prefixEnd_489778 49677338863780735806925 := by
  unfold tailWord_489778
  simp only [CollatzResearch.WordTrace]
  refine ⟨4465917804906357066999497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11909114146416952178665325 4465917804906357066999497)
  ·
    refine ⟨3349438353679767800249623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4465917804906357066999497 3349438353679767800249623)
    ·
      refine ⟨5024157530519651700374435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3349438353679767800249623 5024157530519651700374435)
      ·
        refine ⟨7536236295779477550561653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5024157530519651700374435 7536236295779477550561653)
        ·
          refine ⟨706522152729326020365155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7536236295779477550561653 706522152729326020365155)
          ·
            refine ⟨1059783229093989030547733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 706522152729326020365155 1059783229093989030547733)
            ·
              refine ⟨49677338863780735806925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1059783229093989030547733 49677338863780735806925)
              ·
                rfl

theorem cell19_489778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 6].length) (baseStart_489778 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_489778 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_489778 prefixEnd_489778 := by exact prefixLift 489778
  have htrace : WordTrace (prefixWord ++ tailWord_489778) baseStart_489778 baseEnd_489778 := by
    simpa [prefixWord, tailWord_489778, baseEnd_489778] using wordTrace_append hprefix tailTrace_489778
  have hstable : (prefixWord ++ tailWord_489778).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489778).length < 2 ^ (prefixWord ++ tailWord_489778).sum := by decide
  have hdescent : baseEnd_489778 < baseStart_489778 := by decide
  rcases family_descends (prefixWord ++ tailWord_489778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489799 : List Nat := [1, 1, 4, 1, 2, 2, 2, 6]
def baseStart_489799 : Nat := 118140960795 + 489799 * 2 ^ 59
def prefixEnd_489799 : Nat := 4983230072969 + 3 ^ 40 * 489799 * 2
def baseEnd_489799 : Nat := 149038406572820380954051

theorem tailTrace_489799 : CollatzResearch.WordTrace tailWord_489799 prefixEnd_489799 149038406572820380954051 := by
  unfold tailWord_489799
  simp only [CollatzResearch.WordTrace]
  refine ⟨17864437152549348854512451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11909624768366232569674967 17864437152549348854512451)
  ·
    refine ⟨26796655728824023281768677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17864437152549348854512451 26796655728824023281768677)
    ·
      refine ⟨5024372949154504365331627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26796655728824023281768677 5024372949154504365331627)
      ·
        refine ⟨7536559423731756547997441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5024372949154504365331627 7536559423731756547997441)
        ·
          refine ⟨5652419567798817410998081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7536559423731756547997441 5652419567798817410998081)
          ·
            refine ⟨4239314675849113058248561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5652419567798817410998081 4239314675849113058248561)
            ·
              refine ⟨3179486006886834793686421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4239314675849113058248561 3179486006886834793686421)
              ·
                refine ⟨149038406572820380954051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3179486006886834793686421 149038406572820380954051)
                ·
                  rfl

theorem cell19_489799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 6].length) (baseStart_489799 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_489799 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_489799 prefixEnd_489799 := by exact prefixLift 489799
  have htrace : WordTrace (prefixWord ++ tailWord_489799) baseStart_489799 baseEnd_489799 := by
    simpa [prefixWord, tailWord_489799, baseEnd_489799] using wordTrace_append hprefix tailTrace_489799
  have hstable : (prefixWord ++ tailWord_489799).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489799).length < 2 ^ (prefixWord ++ tailWord_489799).sum := by decide
  have hdescent : baseEnd_489799 < baseStart_489799 := by decide
  rcases family_descends (prefixWord ++ tailWord_489799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489909 : List Nat := [1, 3, 3, 2, 3, 2, 1, 4]
def baseStart_489909 : Nat := 118140960795 + 489909 * 2 ^ 59
def prefixEnd_489909 : Nat := 4983230072969 + 3 ^ 40 * 489909 * 2
def baseEnd_489909 : Nat := 149071877904372718509307

theorem tailTrace_489909 : CollatzResearch.WordTrace tailWord_489909 prefixEnd_489909 149071877904372718509307 := by
  unfold tailWord_489909
  simp only [CollatzResearch.WordTrace]
  refine ⟨17868449182150837641016781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11912299454767225094011187 17868449182150837641016781)
  ·
    refine ⟨6700668443306564115381293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17868449182150837641016781 6700668443306564115381293)
    ·
      refine ⟨2512750666239961543267985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6700668443306564115381293 2512750666239961543267985)
      ·
        refine ⟨1884562999679971157450989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2512750666239961543267985 1884562999679971157450989)
        ·
          refine ⟨706711124879989184044121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1884562999679971157450989 706711124879989184044121)
          ·
            refine ⟨530033343659991888033091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 706711124879989184044121 530033343659991888033091)
            ·
              refine ⟨795050015489987832049637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 530033343659991888033091 795050015489987832049637)
              ·
                refine ⟨149071877904372718509307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 795050015489987832049637 149071877904372718509307)
                ·
                  rfl

theorem cell19_489909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 4].length) (baseStart_489909 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_489909 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_489909 prefixEnd_489909 := by exact prefixLift 489909
  have htrace : WordTrace (prefixWord ++ tailWord_489909) baseStart_489909 baseEnd_489909 := by
    simpa [prefixWord, tailWord_489909, baseEnd_489909] using wordTrace_append hprefix tailTrace_489909
  have hstable : (prefixWord ++ tailWord_489909).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489909).length < 2 ^ (prefixWord ++ tailWord_489909).sum := by decide
  have hdescent : baseEnd_489909 < baseStart_489909 := by decide
  rcases family_descends (prefixWord ++ tailWord_489909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489911 : List Nat := [1, 1, 3, 1, 3, 5, 1, 4]
def baseStart_489911 : Nat := 118140960795 + 489911 * 2 ^ 59
def prefixEnd_489911 : Nat := 4983230072969 + 3 ^ 40 * 489911 * 2
def baseEnd_489911 : Nat := 149072486474037306464857

theorem tailTrace_489911 : CollatzResearch.WordTrace tailWord_489911 prefixEnd_489911 149072486474037306464857 := by
  unfold tailWord_489911
  simp only [CollatzResearch.WordTrace]
  refine ⟨17868522128143591982589587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11912348085429061321726391 17868522128143591982589587)
  ·
    refine ⟨26802783192215387973884381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17868522128143591982589587 26802783192215387973884381)
    ·
      refine ⟨10051043697080770490206643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26802783192215387973884381 10051043697080770490206643)
      ·
        refine ⟨15076565545621155735309965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10051043697080770490206643 15076565545621155735309965)
        ·
          refine ⟨5653712079607933400741237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15076565545621155735309965 5653712079607933400741237)
          ·
            refine ⟨530035507463243756319491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5653712079607933400741237 530035507463243756319491)
            ·
              refine ⟨795053261194865634479237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 530035507463243756319491 795053261194865634479237)
              ·
                refine ⟨149072486474037306464857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 795053261194865634479237 149072486474037306464857)
                ·
                  rfl

theorem cell19_489911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 4].length) (baseStart_489911 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_489911 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_489911 prefixEnd_489911 := by exact prefixLift 489911
  have htrace : WordTrace (prefixWord ++ tailWord_489911) baseStart_489911 baseEnd_489911 := by
    simpa [prefixWord, tailWord_489911, baseEnd_489911] using wordTrace_append hprefix tailTrace_489911
  have hstable : (prefixWord ++ tailWord_489911).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489911).length < 2 ^ (prefixWord ++ tailWord_489911).sum := by decide
  have hdescent : baseEnd_489911 < baseStart_489911 := by decide
  rcases family_descends (prefixWord ++ tailWord_489911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489930 : List Nat := [3, 1, 2, 1, 2, 2, 5, 3]
def baseStart_489930 : Nat := 118140960795 + 489930 * 2 ^ 59
def prefixEnd_489930 : Nat := 4983230072969 + 3 ^ 40 * 489930 * 2
def baseEnd_489930 : Nat := 149078267885850892042583

theorem tailTrace_489930 : CollatzResearch.WordTrace tailWord_489930 prefixEnd_489930 149078267885850892042583 := by
  unfold tailWord_489930
  simp only [CollatzResearch.WordTrace]
  refine ⟨4467303778768689556882811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11912810076716505485020829 4467303778768689556882811)
  ·
    refine ⟨6700955668153034335324217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4467303778768689556882811 6700955668153034335324217)
    ·
      refine ⟨5025716751114775751493163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6700955668153034335324217 5025716751114775751493163)
      ·
        refine ⟨7538575126672163627239745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5025716751114775751493163 7538575126672163627239745)
        ·
          refine ⟨5653931345004122720429809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7538575126672163627239745 5653931345004122720429809)
          ·
            refine ⟨4240448508753092040322357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5653931345004122720429809 4240448508753092040322357)
            ·
              refine ⟨397542047695602378780221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4240448508753092040322357 397542047695602378780221)
              ·
                refine ⟨149078267885850892042583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 397542047695602378780221 149078267885850892042583)
                ·
                  rfl

theorem cell19_489930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 5, 3].length) (baseStart_489930 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_489930 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_489930 prefixEnd_489930 := by exact prefixLift 489930
  have htrace : WordTrace (prefixWord ++ tailWord_489930) baseStart_489930 baseEnd_489930 := by
    simpa [prefixWord, tailWord_489930, baseEnd_489930] using wordTrace_append hprefix tailTrace_489930
  have hstable : (prefixWord ++ tailWord_489930).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489930).length < 2 ^ (prefixWord ++ tailWord_489930).sum := by decide
  have hdescent : baseEnd_489930 < baseStart_489930 := by decide
  rcases family_descends (prefixWord ++ tailWord_489930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489951 : List Nat := [1, 1, 2, 3, 3, 3, 6]
def baseStart_489951 : Nat := 118140960795 + 489951 * 2 ^ 59
def prefixEnd_489951 : Nat := 4983230072969 + 3 ^ 40 * 489951 * 2
def baseEnd_489951 : Nat := 49694885955776355191953

theorem tailTrace_489951 : CollatzResearch.WordTrace tailWord_489951 prefixEnd_489951 49694885955776355191953 := by
  unfold tailWord_489951
  simp only [CollatzResearch.WordTrace]
  refine ⟨17869981047998678814045707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11913320698665785876030471 17869981047998678814045707)
  ·
    refine ⟨26804971571998018221068561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17869981047998678814045707 26804971571998018221068561)
    ·
      refine ⟨20103728678998513665801421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26804971571998018221068561 20103728678998513665801421)
      ·
        refine ⟨7538898254624442624675533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20103728678998513665801421 7538898254624442624675533)
        ·
          refine ⟨2827086845484165984253325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7538898254624442624675533 2827086845484165984253325)
          ·
            refine ⟨1060157567056562244094997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2827086845484165984253325 1060157567056562244094997)
            ·
              refine ⟨49694885955776355191953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1060157567056562244094997 49694885955776355191953)
              ·
                rfl

theorem cell19_489951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 6].length) (baseStart_489951 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_489951 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_489951 prefixEnd_489951 := by exact prefixLift 489951
  have htrace : WordTrace (prefixWord ++ tailWord_489951) baseStart_489951 baseEnd_489951 := by
    simpa [prefixWord, tailWord_489951, baseEnd_489951] using wordTrace_append hprefix tailTrace_489951
  have hstable : (prefixWord ++ tailWord_489951).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489951).length < 2 ^ (prefixWord ++ tailWord_489951).sum := by decide
  have hdescent : baseEnd_489951 < baseStart_489951 := by decide
  rcases family_descends (prefixWord ++ tailWord_489951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489985 : List Nat := [1, 2, 4, 1, 3, 3, 2, 3]
def baseStart_489985 : Nat := 118140960795 + 489985 * 2 ^ 59
def prefixEnd_489985 : Nat := 4983230072969 + 3 ^ 40 * 489985 * 2
def baseEnd_489985 : Nat := 149095003551627060820211

theorem tailTrace_489985 : CollatzResearch.WordTrace tailWord_489985 prefixEnd_489985 149095003551627060820211 := by
  unfold tailWord_489985
  simp only [CollatzResearch.WordTrace]
  refine ⟨17871221129875502620783409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11914147419917001747188939 17871221129875502620783409)
  ·
    refine ⟨13403415847406626965587557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17871221129875502620783409 13403415847406626965587557)
    ·
      refine ⟨2513140471388742556047667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13403415847406626965587557 2513140471388742556047667)
      ·
        refine ⟨3769710707083113834071501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2513140471388742556047667 3769710707083113834071501)
        ·
          refine ⟨1413641515156167687776813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3769710707083113834071501 1413641515156167687776813)
          ·
            refine ⟨530115568183562882916305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1413641515156167687776813 530115568183562882916305)
            ·
              refine ⟨397586676137672162187229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 530115568183562882916305 397586676137672162187229)
              ·
                refine ⟨149095003551627060820211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 397586676137672162187229 149095003551627060820211)
                ·
                  rfl

theorem cell19_489985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 2, 3].length) (baseStart_489985 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_489985 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_489985 prefixEnd_489985 := by exact prefixLift 489985
  have htrace : WordTrace (prefixWord ++ tailWord_489985) baseStart_489985 baseEnd_489985 := by
    simpa [prefixWord, tailWord_489985, baseEnd_489985] using wordTrace_append hprefix tailTrace_489985
  have hstable : (prefixWord ++ tailWord_489985).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489985).length < 2 ^ (prefixWord ++ tailWord_489985).sum := by decide
  have hdescent : baseEnd_489985 < baseStart_489985 := by decide
  rcases family_descends (prefixWord ++ tailWord_489985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490004 : List Nat := [2, 4, 3, 1, 1, 3, 5]
def baseStart_490004 : Nat := 118140960795 + 490004 * 2 ^ 59
def prefixEnd_490004 : Nat := 4983230072969 + 3 ^ 40 * 490004 * 2
def baseEnd_490004 : Nat := 49700261654480215465979

theorem tailTrace_490004 : CollatzResearch.WordTrace tailWord_490004 prefixEnd_490004 49700261654480215465979 := by
  unfold tailWord_490004
  simp only [CollatzResearch.WordTrace]
  refine ⟨8935957058403334432862533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11914609411204445910483377 8935957058403334432862533)
  ·
    refine ⟨1675491948450625206161725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8935957058403334432862533 1675491948450625206161725)
    ·
      refine ⟨628309480668984452310647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1675491948450625206161725 628309480668984452310647)
      ·
        refine ⟨942464221003476678465971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 628309480668984452310647 942464221003476678465971)
        ·
          refine ⟨1413696331505215017698957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 942464221003476678465971 1413696331505215017698957)
          ·
            refine ⟨530136124314455631637109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1413696331505215017698957 530136124314455631637109)
            ·
              refine ⟨49700261654480215465979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 530136124314455631637109 49700261654480215465979)
              ·
                rfl

theorem cell19_490004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 5].length) (baseStart_490004 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_490004 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_490004 prefixEnd_490004 := by exact prefixLift 490004
  have htrace : WordTrace (prefixWord ++ tailWord_490004) baseStart_490004 baseEnd_490004 := by
    simpa [prefixWord, tailWord_490004, baseEnd_490004] using wordTrace_append hprefix tailTrace_490004
  have hstable : (prefixWord ++ tailWord_490004).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490004).length < 2 ^ (prefixWord ++ tailWord_490004).sum := by decide
  have hdescent : baseEnd_490004 < baseStart_490004 := by decide
  rcases family_descends (prefixWord ++ tailWord_490004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490008 : List Nat := [2, 1, 2, 3, 3, 1, 7]
def baseStart_490008 : Nat := 118140960795 + 490008 * 2 ^ 59
def prefixEnd_490008 : Nat := 4983230072969 + 3 ^ 40 * 490008 * 2
def baseEnd_490008 : Nat := 49700667367589940769679

theorem tailTrace_490008 : CollatzResearch.WordTrace tailWord_490008 prefixEnd_490008 49700667367589940769679 := by
  unfold tailWord_490008
  simp only [CollatzResearch.WordTrace]
  refine ⟨8936030004396088774435339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11914706672528118365913785 8936030004396088774435339)
  ·
    refine ⟨13404045006594133161653009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8936030004396088774435339 13404045006594133161653009)
    ·
      refine ⟨10053033754945599871239757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13404045006594133161653009 10053033754945599871239757)
      ·
        refine ⟨3769887658104599951714909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10053033754945599871239757 3769887658104599951714909)
        ·
          refine ⟨1413707871789224981893091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3769887658104599951714909 1413707871789224981893091)
          ·
            refine ⟨2120561807683837472839637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1413707871789224981893091 2120561807683837472839637)
            ·
              refine ⟨49700667367589940769679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2120561807683837472839637 49700667367589940769679)
              ·
                rfl

theorem cell19_490008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 7].length) (baseStart_490008 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_490008 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_490008 prefixEnd_490008 := by exact prefixLift 490008
  have htrace : WordTrace (prefixWord ++ tailWord_490008) baseStart_490008 baseEnd_490008 := by
    simpa [prefixWord, tailWord_490008, baseEnd_490008] using wordTrace_append hprefix tailTrace_490008
  have hstable : (prefixWord ++ tailWord_490008).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490008).length < 2 ^ (prefixWord ++ tailWord_490008).sum := by decide
  have hdescent : baseEnd_490008 < baseStart_490008 := by decide
  rcases family_descends (prefixWord ++ tailWord_490008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490272 : List Nat := [2, 1, 1, 5, 1, 3, 3, 3]
def baseStart_490272 : Nat := 118140960795 + 490272 * 2 ^ 59
def prefixEnd_490272 : Nat := 4983230072969 + 3 ^ 40 * 490272 * 2
def baseEnd_490272 : Nat := 149182333298495432441651

theorem tailTrace_490272 : CollatzResearch.WordTrace tailWord_490272 prefixEnd_490272 149182333298495432441651 := by
  unfold tailWord_490272
  simp only [CollatzResearch.WordTrace]
  refine ⟨8940844439917875318240535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11921125919890500424320713 8940844439917875318240535)
  ·
    refine ⟨13411266659876812977360803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8940844439917875318240535 13411266659876812977360803)
    ·
      refine ⟨20116899989815219466041205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13411266659876812977360803 20116899989815219466041205)
      ·
        refine ⟨1885959374045176824941363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20116899989815219466041205 1885959374045176824941363)
        ·
          refine ⟨2828939061067765237412045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1885959374045176824941363 2828939061067765237412045)
          ·
            refine ⟨1060852147900411964029517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2828939061067765237412045 1060852147900411964029517)
            ·
              refine ⟨397819555462654486511069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1060852147900411964029517 397819555462654486511069)
              ·
                refine ⟨149182333298495432441651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 397819555462654486511069 149182333298495432441651)
                ·
                  rfl

theorem cell19_490272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 3, 3].length) (baseStart_490272 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_490272 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_490272 prefixEnd_490272 := by exact prefixLift 490272
  have htrace : WordTrace (prefixWord ++ tailWord_490272) baseStart_490272 baseEnd_490272 := by
    simpa [prefixWord, tailWord_490272, baseEnd_490272] using wordTrace_append hprefix tailTrace_490272
  have hstable : (prefixWord ++ tailWord_490272).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490272).length < 2 ^ (prefixWord ++ tailWord_490272).sum := by decide
  have hdescent : baseEnd_490272 < baseStart_490272 := by decide
  rcases family_descends (prefixWord ++ tailWord_490272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490293 : List Nat := [1, 3, 3, 1, 3, 2, 6]
def baseStart_490293 : Nat := 118140960795 + 490293 * 2 ^ 59
def prefixEnd_490293 : Nat := 4983230072969 + 3 ^ 40 * 490293 * 2
def baseEnd_490293 : Nat := 49729574426657868658309

theorem tailTrace_490293 : CollatzResearch.WordTrace tailWord_490293 prefixEnd_490293 49729574426657868658309 := by
  unfold tailWord_490293
  simp only [CollatzResearch.WordTrace]
  refine ⟨17882454812759671222995533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11921636541839780815330355 17882454812759671222995533)
  ·
    refine ⟨6705920554784876708623325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17882454812759671222995533 6705920554784876708623325)
    ·
      refine ⟨2514720208044328765733747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6705920554784876708623325 2514720208044328765733747)
      ·
        refine ⟨3772080312066493148600621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2514720208044328765733747 3772080312066493148600621)
        ·
          refine ⟨1414530117024934930725233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3772080312066493148600621 1414530117024934930725233)
          ·
            refine ⟨1060897587768701198043925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1414530117024934930725233 1060897587768701198043925)
            ·
              refine ⟨49729574426657868658309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1060897587768701198043925 49729574426657868658309)
              ·
                rfl

theorem cell19_490293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 6].length) (baseStart_490293 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_490293 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_490293 prefixEnd_490293 := by exact prefixLift 490293
  have htrace : WordTrace (prefixWord ++ tailWord_490293) baseStart_490293 baseEnd_490293 := by
    simpa [prefixWord, tailWord_490293, baseEnd_490293] using wordTrace_append hprefix tailTrace_490293
  have hstable : (prefixWord ++ tailWord_490293).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490293).length < 2 ^ (prefixWord ++ tailWord_490293).sum := by decide
  have hdescent : baseEnd_490293 < baseStart_490293 := by decide
  rcases family_descends (prefixWord ++ tailWord_490293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490295 : List Nat := [1, 1, 3, 1, 2, 1, 10]
def baseStart_490295 : Nat := 118140960795 + 490295 * 2 ^ 59
def prefixEnd_490295 : Nat := 4983230072969 + 3 ^ 40 * 490295 * 2
def baseEnd_490295 : Nat := 49729777283212731310159

theorem tailTrace_490295 : CollatzResearch.WordTrace tailWord_490295 prefixEnd_490295 49729777283212731310159 := by
  unfold tailWord_490295
  simp only [CollatzResearch.WordTrace]
  refine ⟨17882527758752425564568339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11921685172501617043045559 17882527758752425564568339)
  ·
    refine ⟨26823791638128638346852509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17882527758752425564568339 26823791638128638346852509)
    ·
      refine ⟨10058921864298239380069691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26823791638128638346852509 10058921864298239380069691)
      ·
        refine ⟨15088382796447359070104537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10058921864298239380069691 15088382796447359070104537)
        ·
          refine ⟨11316287097335519302578403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15088382796447359070104537 11316287097335519302578403)
          ·
            refine ⟨16974430646003278953867605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11316287097335519302578403 16974430646003278953867605)
            ·
              refine ⟨49729777283212731310159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16974430646003278953867605 49729777283212731310159)
              ·
                rfl

theorem cell19_490295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 10].length) (baseStart_490295 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_490295 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_490295 prefixEnd_490295 := by exact prefixLift 490295
  have htrace : WordTrace (prefixWord ++ tailWord_490295) baseStart_490295 baseEnd_490295 := by
    simpa [prefixWord, tailWord_490295, baseEnd_490295] using wordTrace_append hprefix tailTrace_490295
  have hstable : (prefixWord ++ tailWord_490295).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490295).length < 2 ^ (prefixWord ++ tailWord_490295).sum := by decide
  have hdescent : baseEnd_490295 < baseStart_490295 := by decide
  rcases family_descends (prefixWord ++ tailWord_490295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490329 : List Nat := [1, 2, 1, 2, 2, 6, 2, 3]
def baseStart_490329 : Nat := 118140960795 + 490329 * 2 ^ 59
def prefixEnd_490329 : Nat := 4983230072969 + 3 ^ 40 * 490329 * 2
def baseEnd_490329 : Nat := 149199677533936189174829

theorem tailTrace_490329 : CollatzResearch.WordTrace tailWord_490329 prefixEnd_490329 149199677533936189174829 := by
  unfold tailWord_490329
  simp only [CollatzResearch.WordTrace]
  refine ⟨17883767840629249371306041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11922511893752832914204027 17883767840629249371306041)
  ·
    refine ⟨13412825880471937028479531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17883767840629249371306041 13412825880471937028479531)
    ·
      refine ⟨20119238820707905542719297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13412825880471937028479531 20119238820707905542719297)
      ·
        refine ⟨15089429115530929157039473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20119238820707905542719297 15089429115530929157039473)
        ·
          refine ⟨11317071836648196867779605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15089429115530929157039473 11317071836648196867779605)
          ·
            refine ⟨530487742342884228177169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 11317071836648196867779605 530487742342884228177169)
            ·
              refine ⟨397865806757163171132877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 530487742342884228177169 397865806757163171132877)
              ·
                refine ⟨149199677533936189174829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 397865806757163171132877 149199677533936189174829)
                ·
                  rfl

theorem cell19_490329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 2, 3].length) (baseStart_490329 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_490329 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_490329 prefixEnd_490329 := by exact prefixLift 490329
  have htrace : WordTrace (prefixWord ++ tailWord_490329) baseStart_490329 baseEnd_490329 := by
    simpa [prefixWord, tailWord_490329, baseEnd_490329] using wordTrace_append hprefix tailTrace_490329
  have hstable : (prefixWord ++ tailWord_490329).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490329).length < 2 ^ (prefixWord ++ tailWord_490329).sum := by decide
  have hdescent : baseEnd_490329 < baseStart_490329 := by decide
  rcases family_descends (prefixWord ++ tailWord_490329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490352 : List Nat := [2, 1, 1, 1, 4, 1, 9]
def baseStart_490352 : Nat := 118140960795 + 490352 * 2 ^ 59
def prefixEnd_490352 : Nat := 4983230072969 + 3 ^ 40 * 490352 * 2
def baseEnd_490352 : Nat := 49735558695026316887885

theorem tailTrace_490352 : CollatzResearch.WordTrace tailWord_490352 prefixEnd_490352 49735558695026316887885 := by
  unfold tailWord_490352
  simp only [CollatzResearch.WordTrace]
  refine ⟨8942303359772962149696655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11923071146363949532928873 8942303359772962149696655)
  ·
    refine ⟨13413455039659443224544983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8942303359772962149696655 13413455039659443224544983)
    ·
      refine ⟨20120182559489164836817475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13413455039659443224544983 20120182559489164836817475)
      ·
        refine ⟨30180273839233747255226213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20120182559489164836817475 30180273839233747255226213)
        ·
          refine ⟨5658801344856327610354915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30180273839233747255226213 5658801344856327610354915)
          ·
            refine ⟨8488202017284491415532373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5658801344856327610354915 8488202017284491415532373)
            ·
              refine ⟨49735558695026316887885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8488202017284491415532373 49735558695026316887885)
              ·
                rfl

theorem cell19_490352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 9].length) (baseStart_490352 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_490352 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_490352 prefixEnd_490352 := by exact prefixLift 490352
  have htrace : WordTrace (prefixWord ++ tailWord_490352) baseStart_490352 baseEnd_490352 := by
    simpa [prefixWord, tailWord_490352, baseEnd_490352] using wordTrace_append hprefix tailTrace_490352
  have hstable : (prefixWord ++ tailWord_490352).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490352).length < 2 ^ (prefixWord ++ tailWord_490352).sum := by decide
  have hdescent : baseEnd_490352 < baseStart_490352 := by decide
  rcases family_descends (prefixWord ++ tailWord_490352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490388 : List Nat := [2, 4, 2, 1, 1, 1, 1, 7]
def baseStart_490388 : Nat := 118140960795 + 490388 * 2 ^ 59
def prefixEnd_490388 : Nat := 4983230072969 + 3 ^ 40 * 490388 * 2
def baseEnd_490388 : Nat := 149217630339041533863557

theorem tailTrace_490388 : CollatzResearch.WordTrace tailWord_490388 prefixEnd_490388 149217630339041533863557 := by
  unfold tailWord_490388
  simp only [CollatzResearch.WordTrace]
  refine ⟨8942959873707751223851909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11923946498277001631802545 8942959873707751223851909)
  ·
    refine ⟨1676804976320203354472233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8942959873707751223851909 1676804976320203354472233)
    ·
      refine ⟨1257603732240152515854175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1676804976320203354472233 1257603732240152515854175)
      ·
        refine ⟨1886405598360228773781263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1257603732240152515854175 1886405598360228773781263)
        ·
          refine ⟨2829608397540343160671895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1886405598360228773781263 2829608397540343160671895)
          ·
            refine ⟨4244412596310514741007843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2829608397540343160671895 4244412596310514741007843)
            ·
              refine ⟨6366618894465772111511765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4244412596310514741007843 6366618894465772111511765)
              ·
                refine ⟨149217630339041533863557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6366618894465772111511765 149217630339041533863557)
                ·
                  rfl

theorem cell19_490388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 7].length) (baseStart_490388 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_490388 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_490388 prefixEnd_490388 := by exact prefixLift 490388
  have htrace : WordTrace (prefixWord ++ tailWord_490388) baseStart_490388 baseEnd_490388 := by
    simpa [prefixWord, tailWord_490388, baseEnd_490388] using wordTrace_append hprefix tailTrace_490388
  have hstable : (prefixWord ++ tailWord_490388).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490388).length < 2 ^ (prefixWord ++ tailWord_490388).sum := by decide
  have hdescent : baseEnd_490388 < baseStart_490388 := by decide
  rcases family_descends (prefixWord ++ tailWord_490388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490407 : List Nat := [1, 1, 6, 1, 3, 7]
def baseStart_490407 : Nat := 118140960795 + 490407 * 2 ^ 59
def prefixEnd_490407 : Nat := 4983230072969 + 3 ^ 40 * 490407 * 2
def baseEnd_490407 : Nat := 16580379083428346604587

theorem tailTrace_490407 : CollatzResearch.WordTrace tailWord_490407 prefixEnd_490407 16580379083428346604587 := by
  unfold tailWord_490407
  simp only [CollatzResearch.WordTrace]
  refine ⟨17886612734346668692645475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11924408489564445795096983 17886612734346668692645475)
  ·
    refine ⟨26829919101520003038968213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17886612734346668692645475 26829919101520003038968213)
    ·
      refine ⟨1257652457883750142451635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 26829919101520003038968213 1257652457883750142451635)
      ·
        refine ⟨1886478686825625213677453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1257652457883750142451635 1886478686825625213677453)
        ·
          refine ⟨707429507559609455129045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1886478686825625213677453 707429507559609455129045)
          ·
            refine ⟨16580379083428346604587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 707429507559609455129045 16580379083428346604587)
            ·
              rfl

theorem cell19_490407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 7].length) (baseStart_490407 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_490407 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_490407 prefixEnd_490407 := by exact prefixLift 490407
  have htrace : WordTrace (prefixWord ++ tailWord_490407) baseStart_490407 baseEnd_490407 := by
    simpa [prefixWord, tailWord_490407, baseEnd_490407] using wordTrace_append hprefix tailTrace_490407
  have hstable : (prefixWord ++ tailWord_490407).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490407).length < 2 ^ (prefixWord ++ tailWord_490407).sum := by decide
  have hdescent : baseEnd_490407 < baseStart_490407 := by decide
  rcases family_descends (prefixWord ++ tailWord_490407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490498 : List Nat := [3, 4, 1, 3, 1, 1, 1, 5]
def baseStart_490498 : Nat := 118140960795 + 490498 * 2 ^ 59
def prefixEnd_490498 : Nat := 4983230072969 + 3 ^ 40 * 490498 * 2
def baseEnd_490498 : Nat := 149251101670593871418813

theorem tailTrace_490498 : CollatzResearch.WordTrace tailWord_490498 prefixEnd_490498 149251101670593871418813 := by
  unfold tailWord_490498
  simp only [CollatzResearch.WordTrace]
  refine ⟨4472482944254247808552037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11926621184677994156138765 4472482944254247808552037)
  ·
    refine ⟨838590552047671464103507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4472482944254247808552037 838590552047671464103507)
    ·
      refine ⟨1257885828071507196155261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 838590552047671464103507 1257885828071507196155261)
      ·
        refine ⟨471707185526815198558223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1257885828071507196155261 471707185526815198558223)
        ·
          refine ⟨707560778290222797837335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 471707185526815198558223 707560778290222797837335)
          ·
            refine ⟨1061341167435334196756003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 707560778290222797837335 1061341167435334196756003)
            ·
              refine ⟨1592011751153001295134005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1061341167435334196756003 1592011751153001295134005)
              ·
                refine ⟨149251101670593871418813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1592011751153001295134005 149251101670593871418813)
                ·
                  rfl

theorem cell19_490498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 5].length) (baseStart_490498 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_490498 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_490498 prefixEnd_490498 := by exact prefixLift 490498
  have htrace : WordTrace (prefixWord ++ tailWord_490498) baseStart_490498 baseEnd_490498 := by
    simpa [prefixWord, tailWord_490498, baseEnd_490498] using wordTrace_append hprefix tailTrace_490498
  have hstable : (prefixWord ++ tailWord_490498).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490498).length < 2 ^ (prefixWord ++ tailWord_490498).sum := by decide
  have hdescent : baseEnd_490498 < baseStart_490498 := by decide
  rcases family_descends (prefixWord ++ tailWord_490498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490538 : List Nat := [3, 1, 4, 1, 3, 1, 2, 4]
def baseStart_490538 : Nat := 118140960795 + 490538 * 2 ^ 59
def prefixEnd_490538 : Nat := 4983230072969 + 3 ^ 40 * 490538 * 2
def baseEnd_490538 : Nat := 149263273063885630529815

theorem tailTrace_490538 : CollatzResearch.WordTrace tailWord_490538 prefixEnd_490538 149263273063885630529815 := by
  unfold tailWord_490538
  simp only [CollatzResearch.WordTrace]
  refine ⟨4472847674218019516416067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11927593797914718710442845 4472847674218019516416067)
  ·
    refine ⟨6709271511327029274624101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4472847674218019516416067 6709271511327029274624101)
    ·
      refine ⟨1257988408373817988992019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6709271511327029274624101 1257988408373817988992019)
      ·
        refine ⟨1886982612560726983488029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1257988408373817988992019 1886982612560726983488029)
        ·
          refine ⟨707618479710272618808011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1886982612560726983488029 707618479710272618808011)
          ·
            refine ⟨1061427719565408928212017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 707618479710272618808011 1061427719565408928212017)
            ·
              refine ⟨796070789674056696159013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1061427719565408928212017 796070789674056696159013)
              ·
                refine ⟨149263273063885630529815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 796070789674056696159013 149263273063885630529815)
                ·
                  rfl

theorem cell19_490538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 4].length) (baseStart_490538 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_490538 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_490538 prefixEnd_490538 := by exact prefixLift 490538
  have htrace : WordTrace (prefixWord ++ tailWord_490538) baseStart_490538 baseEnd_490538 := by
    simpa [prefixWord, tailWord_490538, baseEnd_490538] using wordTrace_append hprefix tailTrace_490538
  have hstable : (prefixWord ++ tailWord_490538).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490538).length < 2 ^ (prefixWord ++ tailWord_490538).sum := by decide
  have hdescent : baseEnd_490538 < baseStart_490538 := by decide
  rcases family_descends (prefixWord ++ tailWord_490538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490614 : List Nat := [5, 1, 1, 2, 1, 1, 5, 3]
def baseStart_490614 : Nat := 118140960795 + 490614 * 2 ^ 59
def prefixEnd_490614 : Nat := 4983230072969 + 3 ^ 40 * 490614 * 2
def baseEnd_490614 : Nat := 149286398711139972840719

theorem tailTrace_490614 : CollatzResearch.WordTrace tailWord_490614 prefixEnd_490614 149286398711139972840719 := by
  unfold tailWord_490614
  simp only [CollatzResearch.WordTrace]
  refine ⟨1118385165287296440339431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11929441763064495363620597 1118385165287296440339431)
  ·
    refine ⟨1677577747930944660509147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1118385165287296440339431 1677577747930944660509147)
    ·
      refine ⟨2516366621896416990763721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1677577747930944660509147 2516366621896416990763721)
      ·
        refine ⟨1887274966422312743072791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2516366621896416990763721 1887274966422312743072791)
        ·
          refine ⟨2830912449633469114609187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1887274966422312743072791 2830912449633469114609187)
          ·
            refine ⟨4246368674450203671913781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2830912449633469114609187 4246368674450203671913781)
            ·
              refine ⟨398097063229706594241917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4246368674450203671913781 398097063229706594241917)
              ·
                refine ⟨149286398711139972840719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 398097063229706594241917 149286398711139972840719)
                ·
                  rfl

theorem cell19_490614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_490614 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_490614 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_490614 prefixEnd_490614 := by exact prefixLift 490614
  have htrace : WordTrace (prefixWord ++ tailWord_490614) baseStart_490614 baseEnd_490614 := by
    simpa [prefixWord, tailWord_490614, baseEnd_490614] using wordTrace_append hprefix tailTrace_490614
  have hstable : (prefixWord ++ tailWord_490614).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490614).length < 2 ^ (prefixWord ++ tailWord_490614).sum := by decide
  have hdescent : baseEnd_490614 < baseStart_490614 := by decide
  rcases family_descends (prefixWord ++ tailWord_490614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490656 : List Nat := [2, 1, 1, 4, 2, 1, 2, 6]
def baseStart_490656 : Nat := 118140960795 + 490656 * 2 ^ 59
def prefixEnd_490656 : Nat := 4983230072969 + 3 ^ 40 * 490656 * 2
def baseEnd_490656 : Nat := 149299178674096319907271

theorem tailTrace_490656 : CollatzResearch.WordTrace tailWord_490656 prefixEnd_490656 149299178674096319907271 := by
  unfold tailWord_490656
  simp only [CollatzResearch.WordTrace]
  refine ⟨8947847255222292109229911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11930463006963056145639881 8947847255222292109229911)
  ·
    refine ⟨13421770882833438163844867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8947847255222292109229911 13421770882833438163844867)
    ·
      refine ⟨20132656324250157245767301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13421770882833438163844867 20132656324250157245767301)
      ·
        refine ⟨3774873060796904483581369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20132656324250157245767301 3774873060796904483581369)
        ·
          refine ⟨2831154795597678362686027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3774873060796904483581369 2831154795597678362686027)
          ·
            refine ⟨4246732193396517544029041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2831154795597678362686027 4246732193396517544029041)
            ·
              refine ⟨3185049145047388158021781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4246732193396517544029041 3185049145047388158021781)
              ·
                refine ⟨149299178674096319907271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3185049145047388158021781 149299178674096319907271)
                ·
                  rfl

theorem cell19_490656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 6].length) (baseStart_490656 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_490656 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_490656 prefixEnd_490656 := by exact prefixLift 490656
  have htrace : WordTrace (prefixWord ++ tailWord_490656) baseStart_490656 baseEnd_490656 := by
    simpa [prefixWord, tailWord_490656, baseEnd_490656] using wordTrace_append hprefix tailTrace_490656
  have hstable : (prefixWord ++ tailWord_490656).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490656).length < 2 ^ (prefixWord ++ tailWord_490656).sum := by decide
  have hdescent : baseEnd_490656 < baseStart_490656 := by decide
  rcases family_descends (prefixWord ++ tailWord_490656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490669 : List Nat := [1, 5, 2, 1, 3, 2, 2, 3]
def baseStart_490669 : Nat := 118140960795 + 490669 * 2 ^ 59
def prefixEnd_490669 : Nat := 4983230072969 + 3 ^ 40 * 490669 * 2
def baseEnd_490669 : Nat := 149303134376916141618347

theorem tailTrace_490669 : CollatzResearch.WordTrace tailWord_490669 prefixEnd_490669 149303134376916141618347 := by
  unfold tailWord_490669
  simp only [CollatzResearch.WordTrace]
  refine ⟨17896168659397487438683061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11930779106264991625788707 17896168659397487438683061)
  ·
    refine ⟨1677765811818514447376537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17896168659397487438683061 1677765811818514447376537)
    ·
      refine ⟨1258324358863885835532403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1677765811818514447376537 1258324358863885835532403)
      ·
        refine ⟨1887486538295828753298605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1258324358863885835532403 1887486538295828753298605)
        ·
          refine ⟨707807451860935782486977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1887486538295828753298605 707807451860935782486977)
          ·
            refine ⟨530855588895701836865233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 707807451860935782486977 530855588895701836865233)
            ·
              refine ⟨398141691671776377648925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 530855588895701836865233 398141691671776377648925)
              ·
                refine ⟨149303134376916141618347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 398141691671776377648925 149303134376916141618347)
                ·
                  rfl

theorem cell19_490669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 2, 3].length) (baseStart_490669 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_490669 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_490669 prefixEnd_490669 := by exact prefixLift 490669
  have htrace : WordTrace (prefixWord ++ tailWord_490669) baseStart_490669 baseEnd_490669 := by
    simpa [prefixWord, tailWord_490669, baseEnd_490669] using wordTrace_append hprefix tailTrace_490669
  have hstable : (prefixWord ++ tailWord_490669).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490669).length < 2 ^ (prefixWord ++ tailWord_490669).sum := by decide
  have hdescent : baseEnd_490669 < baseStart_490669 := by decide
  rcases family_descends (prefixWord ++ tailWord_490669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490673 : List Nat := [1, 2, 2, 5, 1, 2, 1, 5]
def baseStart_490673 : Nat := 118140960795 + 490673 * 2 ^ 59
def prefixEnd_490673 : Nat := 4983230072969 + 3 ^ 40 * 490673 * 2
def baseEnd_490673 : Nat := 149304351516245317529447

theorem tailTrace_490673 : CollatzResearch.WordTrace tailWord_490673 prefixEnd_490673 149304351516245317529447 := by
  unfold tailWord_490673
  simp only [CollatzResearch.WordTrace]
  refine ⟨17896314551382996121828673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11930876367588664081219115 17896314551382996121828673)
  ·
    refine ⟨13422235913537247091371505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17896314551382996121828673 13422235913537247091371505)
    ·
      refine ⟨10066676935152935318528629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13422235913537247091371505 10066676935152935318528629)
      ·
        refine ⟨943750962670587686112059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10066676935152935318528629 943750962670587686112059)
        ·
          refine ⟨1415626444005881529168089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 943750962670587686112059 1415626444005881529168089)
          ·
            refine ⟨1061719833004411146876067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1415626444005881529168089 1061719833004411146876067)
            ·
              refine ⟨1592579749506616720314101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1061719833004411146876067 1592579749506616720314101)
              ·
                refine ⟨149304351516245317529447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1592579749506616720314101 149304351516245317529447)
                ·
                  rfl

theorem cell19_490673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 5].length) (baseStart_490673 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_490673 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_490673 prefixEnd_490673 := by exact prefixLift 490673
  have htrace : WordTrace (prefixWord ++ tailWord_490673) baseStart_490673 baseEnd_490673 := by
    simpa [prefixWord, tailWord_490673, baseEnd_490673] using wordTrace_append hprefix tailTrace_490673
  have hstable : (prefixWord ++ tailWord_490673).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490673).length < 2 ^ (prefixWord ++ tailWord_490673).sum := by decide
  have hdescent : baseEnd_490673 < baseStart_490673 := by decide
  rcases family_descends (prefixWord ++ tailWord_490673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490732 : List Nat := [2, 2, 1, 1, 2, 4, 2, 5]
def baseStart_490732 : Nat := 118140960795 + 490732 * 2 ^ 59
def prefixEnd_490732 : Nat := 4983230072969 + 3 ^ 40 * 490732 * 2
def baseEnd_490732 : Nat := 149322304321350662218175

theorem tailTrace_490732 : CollatzResearch.WordTrace tailWord_490732 prefixEnd_490732 149322304321350662218175 := by
  unfold tailWord_490732
  simp only [CollatzResearch.WordTrace]
  refine ⟨8949233229084624599113225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11932310972112832798817633 8949233229084624599113225)
  ·
    refine ⟨6711924921813468449334919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8949233229084624599113225 6711924921813468449334919)
    ·
      refine ⟨10067887382720202674002379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6711924921813468449334919 10067887382720202674002379)
      ·
        refine ⟨15101831074080304011003569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10067887382720202674002379 15101831074080304011003569)
        ·
          refine ⟨11326373305560228008252677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15101831074080304011003569 11326373305560228008252677)
          ·
            refine ⟨2123694994792542751547377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11326373305560228008252677 2123694994792542751547377)
            ·
              refine ⟨1592771246094407063660533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2123694994792542751547377 1592771246094407063660533)
              ·
                refine ⟨149322304321350662218175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1592771246094407063660533 149322304321350662218175)
                ·
                  rfl

theorem cell19_490732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 5].length) (baseStart_490732 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_490732 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_490732 prefixEnd_490732 := by exact prefixLift 490732
  have htrace : WordTrace (prefixWord ++ tailWord_490732) baseStart_490732 baseEnd_490732 := by
    simpa [prefixWord, tailWord_490732, baseEnd_490732] using wordTrace_append hprefix tailTrace_490732
  have hstable : (prefixWord ++ tailWord_490732).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490732).length < 2 ^ (prefixWord ++ tailWord_490732).sum := by decide
  have hdescent : baseEnd_490732 < baseStart_490732 := by decide
  rcases family_descends (prefixWord ++ tailWord_490732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490787 : List Nat := [1, 1, 1, 4, 2, 4, 3, 3]
def baseStart_490787 : Nat := 118140960795 + 490787 * 2 ^ 59
def prefixEnd_490787 : Nat := 4983230072969 + 3 ^ 40 * 490787 * 2
def baseEnd_490787 : Nat := 149339039987126830995803

theorem tailTrace_490787 : CollatzResearch.WordTrace tailWord_490787 prefixEnd_490787 149339039987126830995803 := by
  unfold tailWord_490787
  simp only [CollatzResearch.WordTrace]
  refine ⟨17900472472969993591478615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11933648315313329060985743 17900472472969993591478615)
  ·
    refine ⟨26850708709454990387217923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17900472472969993591478615 26850708709454990387217923)
    ·
      refine ⟨40276063064182485580826885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26850708709454990387217923 40276063064182485580826885)
      ·
        refine ⟨7551761824534216046405041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40276063064182485580826885 7551761824534216046405041)
        ·
          refine ⟨5663821368400662034803781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7551761824534216046405041 5663821368400662034803781)
          ·
            refine ⟨1061966506575124131525709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5663821368400662034803781 1061966506575124131525709)
            ·
              refine ⟨398237439965671549322141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1061966506575124131525709 398237439965671549322141)
              ·
                refine ⟨149339039987126830995803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 398237439965671549322141 149339039987126830995803)
                ·
                  rfl

theorem cell19_490787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 3, 3].length) (baseStart_490787 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_490787 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_490787 prefixEnd_490787 := by exact prefixLift 490787
  have htrace : WordTrace (prefixWord ++ tailWord_490787) baseStart_490787 baseEnd_490787 := by
    simpa [prefixWord, tailWord_490787, baseEnd_490787] using wordTrace_append hprefix tailTrace_490787
  have hstable : (prefixWord ++ tailWord_490787).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490787).length < 2 ^ (prefixWord ++ tailWord_490787).sum := by decide
  have hdescent : baseEnd_490787 < baseStart_490787 := by decide
  rcases family_descends (prefixWord ++ tailWord_490787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490838 : List Nat := [5, 2, 3, 1, 1, 1, 1, 5]
def baseStart_490838 : Nat := 118140960795 + 490838 * 2 ^ 59
def prefixEnd_490838 : Nat := 4983230072969 + 3 ^ 40 * 490838 * 2
def baseEnd_490838 : Nat := 149354558513573823862331

theorem tailTrace_490838 : CollatzResearch.WordTrace tailWord_490838 prefixEnd_490838 149354558513573823862331 := by
  unfold tailWord_490838
  simp only [CollatzResearch.WordTrace]
  refine ⟨1118895787236576831349073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11934888397190152867723445 1118895787236576831349073)
  ·
    refine ⟨839171840427432623511805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1118895787236576831349073 839171840427432623511805)
    ·
      refine ⟨314689440160287233816927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 839171840427432623511805 314689440160287233816927)
      ·
        refine ⟨472034160240430850725391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314689440160287233816927 472034160240430850725391)
        ·
          refine ⟨708051240360646276088087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 472034160240430850725391 708051240360646276088087)
          ·
            refine ⟨1062076860540969414132131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 708051240360646276088087 1062076860540969414132131)
            ·
              refine ⟨1593115290811454121198197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1062076860540969414132131 1593115290811454121198197)
              ·
                refine ⟨149354558513573823862331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1593115290811454121198197 149354558513573823862331)
                ·
                  rfl

theorem cell19_490838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 5].length) (baseStart_490838 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_490838 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_490838 prefixEnd_490838 := by exact prefixLift 490838
  have htrace : WordTrace (prefixWord ++ tailWord_490838) baseStart_490838 baseEnd_490838 := by
    simpa [prefixWord, tailWord_490838, baseEnd_490838] using wordTrace_append hprefix tailTrace_490838
  have hstable : (prefixWord ++ tailWord_490838).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490838).length < 2 ^ (prefixWord ++ tailWord_490838).sum := by decide
  have hdescent : baseEnd_490838 < baseStart_490838 := by decide
  rcases family_descends (prefixWord ++ tailWord_490838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490878 : List Nat := [4, 2, 3, 2, 1, 1, 2, 4]
def baseStart_490878 : Nat := 118140960795 + 490878 * 2 ^ 59
def prefixEnd_490878 : Nat := 4983230072969 + 3 ^ 40 * 490878 * 2
def baseEnd_490878 : Nat := 149366729906865582973333

theorem tailTrace_490878 : CollatzResearch.WordTrace tailWord_490878 prefixEnd_490878 149366729906865582973333 := by
  unfold tailWord_490878
  simp only [CollatzResearch.WordTrace]
  refine ⟨2237973939455039516630161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11935861010426877422027525 2237973939455039516630161)
  ·
    refine ⟨1678480454591279637472621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2237973939455039516630161 1678480454591279637472621)
    ·
      refine ⟨629430170471729864052233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1678480454591279637472621 629430170471729864052233)
      ·
        refine ⟨472072627853797398039175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 629430170471729864052233 472072627853797398039175)
        ·
          refine ⟨708108941780696097058763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 472072627853797398039175 708108941780696097058763)
          ·
            refine ⟨1062163412671044145588145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 708108941780696097058763 1062163412671044145588145)
            ·
              refine ⟨796622559503283109191109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1062163412671044145588145 796622559503283109191109)
              ·
                refine ⟨149366729906865582973333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 796622559503283109191109 149366729906865582973333)
                ·
                  rfl

theorem cell19_490878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 4].length) (baseStart_490878 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_490878 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_490878 prefixEnd_490878 := by exact prefixLift 490878
  have htrace : WordTrace (prefixWord ++ tailWord_490878) baseStart_490878 baseEnd_490878 := by
    simpa [prefixWord, tailWord_490878, baseEnd_490878] using wordTrace_append hprefix tailTrace_490878
  have hstable : (prefixWord ++ tailWord_490878).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490878).length < 2 ^ (prefixWord ++ tailWord_490878).sum := by decide
  have hdescent : baseEnd_490878 < baseStart_490878 := by decide
  rcases family_descends (prefixWord ++ tailWord_490878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490884 : List Nat := [2, 3, 2, 1, 1, 3, 1, 6]
def baseStart_490884 : Nat := 118140960795 + 490884 * 2 ^ 59
def prefixEnd_490884 : Nat := 4983230072969 + 3 ^ 40 * 490884 * 2
def baseEnd_490884 : Nat := 149368555615859346839983

theorem tailTrace_490884 : CollatzResearch.WordTrace tailWord_490884 prefixEnd_490884 149368555615859346839983 := by
  unfold tailWord_490884
  simp only [CollatzResearch.WordTrace]
  refine ⟨8952005176809289578879853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11936006902412386105173137 8952005176809289578879853)
  ·
    refine ⟨3357001941303483592079945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8952005176809289578879853 3357001941303483592079945)
    ·
      refine ⟨2517751455977612694059959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3357001941303483592079945 2517751455977612694059959)
      ·
        refine ⟨3776627183966419041089939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2517751455977612694059959 3776627183966419041089939)
        ·
          refine ⟨5664940775949628561634909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3776627183966419041089939 5664940775949628561634909)
          ·
            refine ⟨2124352790981110710613091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5664940775949628561634909 2124352790981110710613091)
            ·
              refine ⟨3186529186471666065919637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2124352790981110710613091 3186529186471666065919637)
              ·
                refine ⟨149368555615859346839983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3186529186471666065919637 149368555615859346839983)
                ·
                  rfl

theorem cell19_490884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 6].length) (baseStart_490884 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_490884 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_490884 prefixEnd_490884 := by exact prefixLift 490884
  have htrace : WordTrace (prefixWord ++ tailWord_490884) baseStart_490884 baseEnd_490884 := by
    simpa [prefixWord, tailWord_490884, baseEnd_490884] using wordTrace_append hprefix tailTrace_490884
  have hstable : (prefixWord ++ tailWord_490884).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490884).length < 2 ^ (prefixWord ++ tailWord_490884).sum := by decide
  have hdescent : baseEnd_490884 < baseStart_490884 := by decide
  rcases family_descends (prefixWord ++ tailWord_490884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490920 : List Nat := [2, 1, 6, 1, 2, 7]
def baseStart_490920 : Nat := 118140960795 + 490920 * 2 ^ 59
def prefixEnd_490920 : Nat := 4983230072969 + 3 ^ 40 * 490920 * 2
def baseEnd_490920 : Nat := 16597723318869103337765

theorem tailTrace_490920 : CollatzResearch.WordTrace tailWord_490920 prefixEnd_490920 16597723318869103337765 := by
  unfold tailWord_490920
  simp only [CollatzResearch.WordTrace]
  refine ⟨8952661690744078653035107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11936882254325438204046809 8952661690744078653035107)
  ·
    refine ⟨13428992536116117979552661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8952661690744078653035107 13428992536116117979552661)
    ·
      refine ⟨629484025130443030291531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 13428992536116117979552661 629484025130443030291531)
      ·
        refine ⟨944226037695664545437297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 629484025130443030291531 944226037695664545437297)
        ·
          refine ⟨708169528271748409077973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 944226037695664545437297 708169528271748409077973)
          ·
            refine ⟨16597723318869103337765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 708169528271748409077973 16597723318869103337765)
            ·
              rfl

theorem cell19_490920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 7].length) (baseStart_490920 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_490920 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_490920 prefixEnd_490920 := by exact prefixLift 490920
  have htrace : WordTrace (prefixWord ++ tailWord_490920) baseStart_490920 baseEnd_490920 := by
    simpa [prefixWord, tailWord_490920, baseEnd_490920] using wordTrace_append hprefix tailTrace_490920
  have hstable : (prefixWord ++ tailWord_490920).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490920).length < 2 ^ (prefixWord ++ tailWord_490920).sum := by decide
  have hdescent : baseEnd_490920 < baseStart_490920 := by decide
  rcases family_descends (prefixWord ++ tailWord_490920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490937 : List Nat := [1, 2, 1, 4, 5, 1, 1, 4]
def baseStart_490937 : Nat := 118140960795 + 490937 * 2 ^ 59
def prefixEnd_490937 : Nat := 4983230072969 + 3 ^ 40 * 490937 * 2
def baseEnd_490937 : Nat := 149384682711970927662061

theorem tailTrace_490937 : CollatzResearch.WordTrace tailWord_490937 prefixEnd_490937 149384682711970927662061 := by
  unfold tailWord_490937
  simp only [CollatzResearch.WordTrace]
  refine ⟨17905943422426569209439065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11937295614951046139626043 17905943422426569209439065)
  ·
    refine ⟨13429457566819926907079299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17905943422426569209439065 13429457566819926907079299)
    ·
      refine ⟨20144186350229890360618949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13429457566819926907079299 20144186350229890360618949)
      ·
        refine ⟨3777034940668104442616053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20144186350229890360618949 3777034940668104442616053)
        ·
          refine ⟨354097025687634791495255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3777034940668104442616053 354097025687634791495255)
          ·
            refine ⟨531145538531452187242883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 354097025687634791495255 531145538531452187242883)
            ·
              refine ⟨796718307797178280864325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 531145538531452187242883 796718307797178280864325)
              ·
                refine ⟨149384682711970927662061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 796718307797178280864325 149384682711970927662061)
                ·
                  rfl

theorem cell19_490937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 4].length) (baseStart_490937 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_490937 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_490937 prefixEnd_490937 := by exact prefixLift 490937
  have htrace : WordTrace (prefixWord ++ tailWord_490937) baseStart_490937 baseEnd_490937 := by
    simpa [prefixWord, tailWord_490937, baseEnd_490937] using wordTrace_append hprefix tailTrace_490937
  have hstable : (prefixWord ++ tailWord_490937).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490937).length < 2 ^ (prefixWord ++ tailWord_490937).sum := by decide
  have hdescent : baseEnd_490937 < baseStart_490937 := by decide
  rcases family_descends (prefixWord ++ tailWord_490937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490979 : List Nat := [1, 1, 1, 6, 2, 2, 6]
def baseStart_490979 : Nat := 118140960795 + 490979 * 2 ^ 59
def prefixEnd_490979 : Nat := 4983230072969 + 3 ^ 40 * 490979 * 2
def baseEnd_490979 : Nat := 49799154224975758242871

theorem tailTrace_490979 : CollatzResearch.WordTrace tailWord_490979 prefixEnd_490979 49799154224975758242871 := by
  unfold tailWord_490979
  simp only [CollatzResearch.WordTrace]
  refine ⟨17907475288274410382467991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11938316858849606921645327 17907475288274410382467991)
  ·
    refine ⟨26861212932411615573701987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17907475288274410382467991 26861212932411615573701987)
    ·
      refine ⟨40291819398617423360552981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26861212932411615573701987 40291819398617423360552981)
      ·
        refine ⟨1888679034310191720025921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 40291819398617423360552981 1888679034310191720025921)
        ·
          refine ⟨1416509275732643790019441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1888679034310191720025921 1416509275732643790019441)
          ·
            refine ⟨1062381956799482842514581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1416509275732643790019441 1062381956799482842514581)
            ·
              refine ⟨49799154224975758242871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1062381956799482842514581 49799154224975758242871)
              ·
                rfl

theorem cell19_490979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 6].length) (baseStart_490979 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_490979 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_490979 prefixEnd_490979 := by exact prefixLift 490979
  have htrace : WordTrace (prefixWord ++ tailWord_490979) baseStart_490979 baseEnd_490979 := by
    simpa [prefixWord, tailWord_490979, baseEnd_490979] using wordTrace_append hprefix tailTrace_490979
  have hstable : (prefixWord ++ tailWord_490979).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490979).length < 2 ^ (prefixWord ++ tailWord_490979).sum := by decide
  have hdescent : baseEnd_490979 < baseStart_490979 := by decide
  rcases family_descends (prefixWord ++ tailWord_490979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491015 : List Nat := [1, 1, 4, 3, 2, 1, 4, 3]
def baseStart_491015 : Nat := 118140960795 + 491015 * 2 ^ 59
def prefixEnd_491015 : Nat := 4983230072969 + 3 ^ 40 * 491015 * 2
def baseEnd_491015 : Nat := 149408416928889857928515

theorem tailTrace_491015 : CollatzResearch.WordTrace tailWord_491015 prefixEnd_491015 149408416928889857928515 := by
  unfold tailWord_491015
  simp only [CollatzResearch.WordTrace]
  refine ⟨17908788316143988530778499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11939192210762659020518999 17908788316143988530778499)
  ·
    refine ⟨26863182474215982796167749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17908788316143988530778499 26863182474215982796167749)
    ·
      refine ⟨5036846713915496774281453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26863182474215982796167749 5036846713915496774281453)
      ·
        refine ⟨1888817517718311290355545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5036846713915496774281453 1888817517718311290355545)
        ·
          refine ⟨1416613138288733467766659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1888817517718311290355545 1416613138288733467766659)
          ·
            refine ⟨2124919707433100201649989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1416613138288733467766659 2124919707433100201649989)
            ·
              refine ⟨398422445143706287809373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2124919707433100201649989 398422445143706287809373)
              ·
                refine ⟨149408416928889857928515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 398422445143706287809373 149408416928889857928515)
                ·
                  rfl

theorem cell19_491015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 4, 3].length) (baseStart_491015 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_491015 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_491015 prefixEnd_491015 := by exact prefixLift 491015
  have htrace : WordTrace (prefixWord ++ tailWord_491015) baseStart_491015 baseEnd_491015 := by
    simpa [prefixWord, tailWord_491015, baseEnd_491015] using wordTrace_append hprefix tailTrace_491015
  have hstable : (prefixWord ++ tailWord_491015).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491015).length < 2 ^ (prefixWord ++ tailWord_491015).sum := by decide
  have hdescent : baseEnd_491015 < baseStart_491015 := by decide
  rcases family_descends (prefixWord ++ tailWord_491015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491095 : List Nat := [1, 1, 3, 2, 2, 10]
def baseStart_491095 : Nat := 118140960795 + 491095 * 2 ^ 59
def prefixEnd_491095 : Nat := 4983230072969 + 3 ^ 40 * 491095 * 2
def baseEnd_491095 : Nat := 16603639968385930683391

theorem tailTrace_491095 : CollatzResearch.WordTrace tailWord_491095 prefixEnd_491095 16603639968385930683391 := by
  unfold tailWord_491095
  simp only [CollatzResearch.WordTrace]
  refine ⟨17911706155854162193690739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11941137437236108129127159 17911706155854162193690739)
  ·
    refine ⟨26867559233781243290536109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17911706155854162193690739 26867559233781243290536109)
    ·
      refine ⟨10075334712667966233951041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26867559233781243290536109 10075334712667966233951041)
      ·
        refine ⟨7556501034500974675463281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10075334712667966233951041 7556501034500974675463281)
        ·
          refine ⟨5667375775875731006597461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7556501034500974675463281 5667375775875731006597461)
          ·
            refine ⟨16603639968385930683391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5667375775875731006597461 16603639968385930683391)
            ·
              rfl

theorem cell19_491095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 10].length) (baseStart_491095 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_491095 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_491095 prefixEnd_491095 := by exact prefixLift 491095
  have htrace : WordTrace (prefixWord ++ tailWord_491095) baseStart_491095 baseEnd_491095 := by
    simpa [prefixWord, tailWord_491095, baseEnd_491095] using wordTrace_append hprefix tailTrace_491095
  have hstable : (prefixWord ++ tailWord_491095).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491095).length < 2 ^ (prefixWord ++ tailWord_491095).sum := by decide
  have hdescent : baseEnd_491095 < baseStart_491095 := by decide
  rcases family_descends (prefixWord ++ tailWord_491095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491131 : List Nat := [1, 1, 1, 1, 1, 4, 7, 3]
def baseStart_491131 : Nat := 118140960795 + 491131 * 2 ^ 59
def prefixEnd_491131 : Nat := 4983230072969 + 3 ^ 40 * 491131 * 2
def baseEnd_491131 : Nat := 149443713969435959350421

theorem tailTrace_491131 : CollatzResearch.WordTrace tailWord_491131 prefixEnd_491131 149443713969435959350421 := by
  unfold tailWord_491131
  simp only [CollatzResearch.WordTrace]
  refine ⟨17913019183723740342001247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11942012789149160228000831 17913019183723740342001247)
  ·
    refine ⟨26869528775585610513001871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17913019183723740342001247 26869528775585610513001871)
    ·
      refine ⟨40304293163378415769502807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26869528775585610513001871 40304293163378415769502807)
      ·
        refine ⟨60456439745067623654254211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40304293163378415769502807 60456439745067623654254211)
        ·
          refine ⟨90684659617601435481381317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60456439745067623654254211 90684659617601435481381317)
          ·
            refine ⟨17003373678300269152758997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90684659617601435481381317 17003373678300269152758997)
            ·
              refine ⟨398516570585162558267789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 17003373678300269152758997 398516570585162558267789)
              ·
                refine ⟨149443713969435959350421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 398516570585162558267789 149443713969435959350421)
                ·
                  rfl

theorem cell19_491131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 7, 3].length) (baseStart_491131 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_491131 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_491131 prefixEnd_491131 := by exact prefixLift 491131
  have htrace : WordTrace (prefixWord ++ tailWord_491131) baseStart_491131 baseEnd_491131 := by
    simpa [prefixWord, tailWord_491131, baseEnd_491131] using wordTrace_append hprefix tailTrace_491131
  have hstable : (prefixWord ++ tailWord_491131).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491131).length < 2 ^ (prefixWord ++ tailWord_491131).sum := by decide
  have hdescent : baseEnd_491131 < baseStart_491131 := by decide
  rcases family_descends (prefixWord ++ tailWord_491131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491150 : List Nat := [4, 1, 1, 3, 1, 3, 6]
def baseStart_491150 : Nat := 118140960795 + 491150 * 2 ^ 59
def prefixEnd_491150 : Nat := 4983230072969 + 3 ^ 40 * 491150 * 2
def baseEnd_491150 : Nat := 49816498460416514976049

theorem tailTrace_491150 : CollatzResearch.WordTrace tailWord_491150 prefixEnd_491150 49816498460416514976049 := by
  unfold tailWord_491150
  simp only [CollatzResearch.WordTrace]
  refine ⟨2239214021331863323367863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11942474780436604391295269 2239214021331863323367863)
  ·
    refine ⟨3358821031997794985051795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2239214021331863323367863 3358821031997794985051795)
    ·
      refine ⟨5038231547996692477577693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3358821031997794985051795 5038231547996692477577693)
      ·
        refine ⟨1889336830498759679091635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5038231547996692477577693 1889336830498759679091635)
        ·
          refine ⟨2834005245748139518637453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1889336830498759679091635 2834005245748139518637453)
          ·
            refine ⟨1062751967155552319489045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2834005245748139518637453 1062751967155552319489045)
            ·
              refine ⟨49816498460416514976049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1062751967155552319489045 49816498460416514976049)
              ·
                rfl

theorem cell19_491150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 6].length) (baseStart_491150 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_491150 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_491150 prefixEnd_491150 := by exact prefixLift 491150
  have htrace : WordTrace (prefixWord ++ tailWord_491150) baseStart_491150 baseEnd_491150 := by
    simpa [prefixWord, tailWord_491150, baseEnd_491150] using wordTrace_append hprefix tailTrace_491150
  have hstable : (prefixWord ++ tailWord_491150).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491150).length < 2 ^ (prefixWord ++ tailWord_491150).sum := by decide
  have hdescent : baseEnd_491150 < baseStart_491150 := by decide
  rcases family_descends (prefixWord ++ tailWord_491150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491171 : List Nat := [1, 1, 1, 4, 1, 1, 4, 6]
def baseStart_491171 : Nat := 118140960795 + 491171 * 2 ^ 59
def prefixEnd_491171 : Nat := 4983230072969 + 3 ^ 40 * 491171 * 2
def baseEnd_491171 : Nat := 149455885362727718461423

theorem tailTrace_491171 : CollatzResearch.WordTrace tailWord_491171 prefixEnd_491171 149455885362727718461423 := by
  unfold tailWord_491171
  simp only [CollatzResearch.WordTrace]
  refine ⟨17914478103578827173457367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11942985402385884782304911 17914478103578827173457367)
  ·
    refine ⟨26871717155368240760186051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17914478103578827173457367 26871717155368240760186051)
    ·
      refine ⟨40307575733052361140279077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26871717155368240760186051 40307575733052361140279077)
      ·
        refine ⟨7557670449947317713802327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40307575733052361140279077 7557670449947317713802327)
        ·
          refine ⟨11336505674920976570703491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7557670449947317713802327 11336505674920976570703491)
          ·
            refine ⟨17004758512381464856055237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11336505674920976570703491 17004758512381464856055237)
            ·
              refine ⟨3188392221071524660510357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17004758512381464856055237 3188392221071524660510357)
              ·
                refine ⟨149455885362727718461423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3188392221071524660510357 149455885362727718461423)
                ·
                  rfl

theorem cell19_491171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 6].length) (baseStart_491171 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_491171 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_491171 prefixEnd_491171 := by exact prefixLift 491171
  have htrace : WordTrace (prefixWord ++ tailWord_491171) baseStart_491171 baseEnd_491171 := by
    simpa [prefixWord, tailWord_491171, baseEnd_491171] using wordTrace_append hprefix tailTrace_491171
  have hstable : (prefixWord ++ tailWord_491171).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491171).length < 2 ^ (prefixWord ++ tailWord_491171).sum := by decide
  have hdescent : baseEnd_491171 < baseStart_491171 := by decide
  rcases family_descends (prefixWord ++ tailWord_491171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491182 : List Nat := [4, 1, 4, 1, 2, 2, 2, 3]
def baseStart_491182 : Nat := 118140960795 + 491182 * 2 ^ 59
def prefixEnd_491182 : Nat := 4983230072969 + 3 ^ 40 * 491182 * 2
def baseEnd_491182 : Nat := 149459232495882952216949

theorem tailTrace_491182 : CollatzResearch.WordTrace tailWord_491182 prefixEnd_491182 149459232495882952216949 := by
  unfold tailWord_491182
  simp only [CollatzResearch.WordTrace]
  refine ⟨2239359913317372006513475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11943252871025984034738533 2239359913317372006513475)
  ·
    refine ⟨3359039869976058009770213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2239359913317372006513475 3359039869976058009770213)
    ·
      refine ⟨629819975620510876831915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3359039869976058009770213 629819975620510876831915)
      ·
        refine ⟨944729963430766315247873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 629819975620510876831915 944729963430766315247873)
        ·
          refine ⟨708547472573074736435905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 944729963430766315247873 708547472573074736435905)
          ·
            refine ⟨531410604429806052326929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 708547472573074736435905 531410604429806052326929)
            ·
              refine ⟨398557953322354539245197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 531410604429806052326929 398557953322354539245197)
              ·
                refine ⟨149459232495882952216949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 398557953322354539245197 149459232495882952216949)
                ·
                  rfl

theorem cell19_491182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 2, 3].length) (baseStart_491182 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_491182 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_491182 prefixEnd_491182 := by exact prefixLift 491182
  have htrace : WordTrace (prefixWord ++ tailWord_491182) baseStart_491182 baseEnd_491182 := by
    simpa [prefixWord, tailWord_491182, baseEnd_491182] using wordTrace_append hprefix tailTrace_491182
  have hstable : (prefixWord ++ tailWord_491182).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491182).length < 2 ^ (prefixWord ++ tailWord_491182).sum := by decide
  have hdescent : baseEnd_491182 < baseStart_491182 := by decide
  rcases family_descends (prefixWord ++ tailWord_491182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491226 : List Nat := [3, 1, 1, 2, 2, 4, 2, 4]
def baseStart_491226 : Nat := 118140960795 + 491226 * 2 ^ 59
def prefixEnd_491226 : Nat := 4983230072969 + 3 ^ 40 * 491226 * 2
def baseEnd_491226 : Nat := 149472621028503887239051

theorem tailTrace_491226 : CollatzResearch.WordTrace tailWord_491226 prefixEnd_491226 149472621028503887239051 := by
  unfold tailWord_491226
  simp only [CollatzResearch.WordTrace]
  refine ⟨4479121029594892891677383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11944322745586381044473021 4479121029594892891677383)
  ·
    refine ⟨6718681544392339337516075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4479121029594892891677383 6718681544392339337516075)
    ·
      refine ⟨10078022316588509006274113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6718681544392339337516075 10078022316588509006274113)
      ·
        refine ⟨7558516737441381754705585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10078022316588509006274113 7558516737441381754705585)
        ·
          refine ⟨5668887553081036316029189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7558516737441381754705585 5668887553081036316029189)
          ·
            refine ⟨1062916416202694309255473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5668887553081036316029189 1062916416202694309255473)
            ·
              refine ⟨797187312152020731941605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1062916416202694309255473 797187312152020731941605)
              ·
                refine ⟨149472621028503887239051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 797187312152020731941605 149472621028503887239051)
                ·
                  rfl

theorem cell19_491226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 4].length) (baseStart_491226 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_491226 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_491226 prefixEnd_491226 := by exact prefixLift 491226
  have htrace : WordTrace (prefixWord ++ tailWord_491226) baseStart_491226 baseEnd_491226 := by
    simpa [prefixWord, tailWord_491226, baseEnd_491226] using wordTrace_append hprefix tailTrace_491226
  have hstable : (prefixWord ++ tailWord_491226).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491226).length < 2 ^ (prefixWord ++ tailWord_491226).sum := by decide
  have hdescent : baseEnd_491226 < baseStart_491226 := by decide
  rcases family_descends (prefixWord ++ tailWord_491226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491245 : List Nat := [1, 5, 1, 2, 1, 2, 2, 5]
def baseStart_491245 : Nat := 118140960795 + 491245 * 2 ^ 59
def prefixEnd_491245 : Nat := 4983230072969 + 3 ^ 40 * 491245 * 2
def baseEnd_491245 : Nat := 149478402440317472816777

theorem tailTrace_491245 : CollatzResearch.WordTrace tailWord_491245 prefixEnd_491245 149478402440317472816777 := by
  unfold tailWord_491245
  simp only [CollatzResearch.WordTrace]
  refine ⟨17917177105310737811651189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11944784736873825207767459 17917177105310737811651189)
  ·
    refine ⟨1679735353622881669842299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17917177105310737811651189 1679735353622881669842299)
    ·
      refine ⟨2519603030434322504763449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1679735353622881669842299 2519603030434322504763449)
      ·
        refine ⟨1889702272825741878572587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2519603030434322504763449 1889702272825741878572587)
        ·
          refine ⟨2834553409238612817858881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1889702272825741878572587 2834553409238612817858881)
          ·
            refine ⟨2125915056928959613394161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2834553409238612817858881 2125915056928959613394161)
            ·
              refine ⟨1594436292696719710045621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2125915056928959613394161 1594436292696719710045621)
              ·
                refine ⟨149478402440317472816777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1594436292696719710045621 149478402440317472816777)
                ·
                  rfl

theorem cell19_491245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 5].length) (baseStart_491245 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_491245 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_491245 prefixEnd_491245 := by exact prefixLift 491245
  have htrace : WordTrace (prefixWord ++ tailWord_491245) baseStart_491245 baseEnd_491245 := by
    simpa [prefixWord, tailWord_491245, baseEnd_491245] using wordTrace_append hprefix tailTrace_491245
  have hstable : (prefixWord ++ tailWord_491245).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491245).length < 2 ^ (prefixWord ++ tailWord_491245).sum := by decide
  have hdescent : baseEnd_491245 < baseStart_491245 := by decide
  rcases family_descends (prefixWord ++ tailWord_491245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491247 : List Nat := [1, 1, 2, 1, 5, 1, 1, 7]
def baseStart_491247 : Nat := 118140960795 + 491247 * 2 ^ 59
def prefixEnd_491247 : Nat := 4983230072969 + 3 ^ 40 * 491247 * 2
def baseEnd_491247 : Nat := 149479011009982060772327

theorem tailTrace_491247 : CollatzResearch.WordTrace tailWord_491247 prefixEnd_491247 149479011009982060772327 := by
  unfold tailWord_491247
  simp only [CollatzResearch.WordTrace]
  refine ⟨17917250051303492153223995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11944833367535661435482663 17917250051303492153223995)
  ·
    refine ⟨26875875076955238229835993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17917250051303492153223995 26875875076955238229835993)
    ·
      refine ⟨20156906307716428672376995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26875875076955238229835993 20156906307716428672376995)
      ·
        refine ⟨30235359461574643008565493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20156906307716428672376995 30235359461574643008565493)
        ·
          refine ⟨2834564949522622782053015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30235359461574643008565493 2834564949522622782053015)
          ·
            refine ⟨4251847424283934173079523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2834564949522622782053015 4251847424283934173079523)
            ·
              refine ⟨6377771136425901259619285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4251847424283934173079523 6377771136425901259619285)
              ·
                refine ⟨149479011009982060772327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6377771136425901259619285 149479011009982060772327)
                ·
                  rfl

theorem cell19_491247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 7].length) (baseStart_491247 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_491247 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_491247 prefixEnd_491247 := by exact prefixLift 491247
  have htrace : WordTrace (prefixWord ++ tailWord_491247) baseStart_491247 baseEnd_491247 := by
    simpa [prefixWord, tailWord_491247, baseEnd_491247] using wordTrace_append hprefix tailTrace_491247
  have hstable : (prefixWord ++ tailWord_491247).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491247).length < 2 ^ (prefixWord ++ tailWord_491247).sum := by decide
  have hdescent : baseEnd_491247 < baseStart_491247 := by decide
  rcases family_descends (prefixWord ++ tailWord_491247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491262 : List Nat := [4, 2, 2, 1, 4, 6]
def baseStart_491262 : Nat := 118140960795 + 491262 * 2 ^ 59
def prefixEnd_491262 : Nat := 4983230072969 + 3 ^ 40 * 491262 * 2
def baseEnd_491262 : Nat := 16609286142496274493217

theorem tailTrace_491262 : CollatzResearch.WordTrace tailWord_491262 prefixEnd_491262 16609286142496274493217 := by
  unfold tailWord_491262
  simp only [CollatzResearch.WordTrace]
  refine ⟨2239724643281143714377505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11945198097499433143346693 2239724643281143714377505)
  ·
    refine ⟨1679793482460857785783129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2239724643281143714377505 1679793482460857785783129)
    ·
      refine ⟨1259845111845643339337347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1679793482460857785783129 1259845111845643339337347)
      ·
        refine ⟨1889767667768465009006021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1259845111845643339337347 1889767667768465009006021)
        ·
          refine ⟨354331437706587189188629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1889767667768465009006021 354331437706587189188629)
          ·
            refine ⟨16609286142496274493217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 354331437706587189188629 16609286142496274493217)
            ·
              rfl

theorem cell19_491262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 6].length) (baseStart_491262 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_491262 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_491262 prefixEnd_491262 := by exact prefixLift 491262
  have htrace : WordTrace (prefixWord ++ tailWord_491262) baseStart_491262 baseEnd_491262 := by
    simpa [prefixWord, tailWord_491262, baseEnd_491262] using wordTrace_append hprefix tailTrace_491262
  have hstable : (prefixWord ++ tailWord_491262).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491262).length < 2 ^ (prefixWord ++ tailWord_491262).sum := by decide
  have hdescent : baseEnd_491262 < baseStart_491262 := by decide
  rcases family_descends (prefixWord ++ tailWord_491262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491300 : List Nat := [2, 3, 1, 3, 2, 2, 3, 3]
def baseStart_491300 : Nat := 118140960795 + 491300 * 2 ^ 59
def prefixEnd_491300 : Nat := 4983230072969 + 3 ^ 40 * 491300 * 2
def baseEnd_491300 : Nat := 149495138106093641594405

theorem tailTrace_491300 : CollatzResearch.WordTrace tailWord_491300 prefixEnd_491300 149495138106093641594405 := by
  unfold tailWord_491300
  simp only [CollatzResearch.WordTrace]
  refine ⟨8959591560055741102451677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11946122080074321469935569 8959591560055741102451677)
  ·
    refine ⟨3359846835020902913419379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8959591560055741102451677 3359846835020902913419379)
    ·
      refine ⟨5039770252531354370129069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3359846835020902913419379 5039770252531354370129069)
      ·
        refine ⟨1889913844699257888798401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5039770252531354370129069 1889913844699257888798401)
        ·
          refine ⟨1417435383524443416598801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1889913844699257888798401 1417435383524443416598801)
          ·
            refine ⟨1063076537643332562449101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1417435383524443416598801 1063076537643332562449101)
            ·
              refine ⟨398653701616249710918413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1063076537643332562449101 398653701616249710918413)
              ·
                refine ⟨149495138106093641594405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 398653701616249710918413 149495138106093641594405)
                ·
                  rfl

theorem cell19_491300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 3, 3].length) (baseStart_491300 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_491300 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_491300 prefixEnd_491300 := by exact prefixLift 491300
  have htrace : WordTrace (prefixWord ++ tailWord_491300) baseStart_491300 baseEnd_491300 := by
    simpa [prefixWord, tailWord_491300, baseEnd_491300] using wordTrace_append hprefix tailTrace_491300
  have hstable : (prefixWord ++ tailWord_491300).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491300).length < 2 ^ (prefixWord ++ tailWord_491300).sum := by decide
  have hdescent : baseEnd_491300 < baseStart_491300 := by decide
  rcases family_descends (prefixWord ++ tailWord_491300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491359 : List Nat := [1, 1, 2, 3, 1, 4, 4, 3]
def baseStart_491359 : Nat := 118140960795 + 491359 * 2 ^ 59
def prefixEnd_491359 : Nat := 4983230072969 + 3 ^ 40 * 491359 * 2
def baseEnd_491359 : Nat := 149513090911198986283133

theorem tailTrace_491359 : CollatzResearch.WordTrace tailWord_491359 prefixEnd_491359 149513090911198986283133 := by
  unfold tailWord_491359
  simp only [CollatzResearch.WordTrace]
  refine ⟨17921335026897735281301131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11947556684598490187534087 17921335026897735281301131)
  ·
    refine ⟨26882002540346602921951697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17921335026897735281301131 26882002540346602921951697)
    ·
      refine ⟨20161501905259952191463773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26882002540346602921951697 20161501905259952191463773)
      ·
        refine ⟨7560563214472482071798915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20161501905259952191463773 7560563214472482071798915)
        ·
          refine ⟨11340844821708723107698373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7560563214472482071798915 11340844821708723107698373)
          ·
            refine ⟨2126408404070385582693445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11340844821708723107698373 2126408404070385582693445)
            ·
              refine ⟨398701575763197296755021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2126408404070385582693445 398701575763197296755021)
              ·
                refine ⟨149513090911198986283133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 398701575763197296755021 149513090911198986283133)
                ·
                  rfl

theorem cell19_491359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 4, 3].length) (baseStart_491359 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_491359 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_491359 prefixEnd_491359 := by exact prefixLift 491359
  have htrace : WordTrace (prefixWord ++ tailWord_491359) baseStart_491359 baseEnd_491359 := by
    simpa [prefixWord, tailWord_491359, baseEnd_491359] using wordTrace_append hprefix tailTrace_491359
  have hstable : (prefixWord ++ tailWord_491359).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491359).length < 2 ^ (prefixWord ++ tailWord_491359).sum := by decide
  have hdescent : baseEnd_491359 < baseStart_491359 := by decide
  rcases family_descends (prefixWord ++ tailWord_491359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491361 : List Nat := [1, 2, 3, 1, 1, 1, 5, 5]
def baseStart_491361 : Nat := 118140960795 + 491361 * 2 ^ 59
def prefixEnd_491361 : Nat := 4983230072969 + 3 ^ 40 * 491361 * 2
def baseEnd_491361 : Nat := 149513699480863574238683

theorem tailTrace_491361 : CollatzResearch.WordTrace tailWord_491361 prefixEnd_491361 149513699480863574238683 := by
  unfold tailWord_491361
  simp only [CollatzResearch.WordTrace]
  refine ⟨17921407972890489622873937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11947605315260326415249291 17921407972890489622873937)
  ·
    refine ⟨13441055979667867217155453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17921407972890489622873937 13441055979667867217155453)
    ·
      refine ⟨5040395992375450206433295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13441055979667867217155453 5040395992375450206433295)
      ·
        refine ⟨7560593988563175309649943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5040395992375450206433295 7560593988563175309649943)
        ·
          refine ⟨11340890982844762964474915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7560593988563175309649943 11340890982844762964474915)
          ·
            refine ⟨17011336474267144446712373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11340890982844762964474915 17011336474267144446712373)
            ·
              refine ⟨1594812794462544791879285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17011336474267144446712373 1594812794462544791879285)
              ·
                refine ⟨149513699480863574238683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1594812794462544791879285 149513699480863574238683)
                ·
                  rfl

theorem cell19_491361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 5].length) (baseStart_491361 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_491361 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_491361 prefixEnd_491361 := by exact prefixLift 491361
  have htrace : WordTrace (prefixWord ++ tailWord_491361) baseStart_491361 baseEnd_491361 := by
    simpa [prefixWord, tailWord_491361, baseEnd_491361] using wordTrace_append hprefix tailTrace_491361
  have hstable : (prefixWord ++ tailWord_491361).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491361).length < 2 ^ (prefixWord ++ tailWord_491361).sum := by decide
  have hdescent : baseEnd_491361 < baseStart_491361 := by decide
  rcases family_descends (prefixWord ++ tailWord_491361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491437 : List Nat := [1, 5, 2, 11]
def baseStart_491437 : Nat := 118140960795 + 491437 * 2 ^ 59
def prefixEnd_491437 : Nat := 4983230072969 + 3 ^ 40 * 491437 * 2
def baseEnd_491437 : Nat := 1846133643557011315427

theorem tailTrace_491437 : CollatzResearch.WordTrace tailWord_491437 prefixEnd_491437 1846133643557011315427 := by
  unfold tailWord_491437
  simp only [CollatzResearch.WordTrace]
  refine ⟨17924179920615154602640565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11949453280410103068427043 17924179920615154602640565)
  ·
    refine ⟨1680391867557670743997553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17924179920615154602640565 1680391867557670743997553)
    ·
      refine ⟨1260293900668253057998165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1680391867557670743997553 1260293900668253057998165)
      ·
        refine ⟨1846133643557011315427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 11 1260293900668253057998165 1846133643557011315427)
        ·
          rfl

theorem cell19_491437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 11].length) (baseStart_491437 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_491437 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_491437 prefixEnd_491437 := by exact prefixLift 491437
  have htrace : WordTrace (prefixWord ++ tailWord_491437) baseStart_491437 baseEnd_491437 := by
    simpa [prefixWord, tailWord_491437, baseEnd_491437] using wordTrace_append hprefix tailTrace_491437
  have hstable : (prefixWord ++ tailWord_491437).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491437).length < 2 ^ (prefixWord ++ tailWord_491437).sum := by decide
  have hdescent : baseEnd_491437 < baseStart_491437 := by decide
  rcases family_descends (prefixWord ++ tailWord_491437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491454 : List Nat := [4, 2, 1, 1, 1, 3, 3, 4]
def baseStart_491454 : Nat := 118140960795 + 491454 * 2 ^ 59
def prefixEnd_491454 : Nat := 4983230072969 + 3 ^ 40 * 491454 * 2
def baseEnd_491454 : Nat := 149541997970266914171763

theorem tailTrace_491454 : CollatzResearch.WordTrace tailWord_491454 prefixEnd_491454 149541997970266914171763 := by
  unfold tailWord_491454
  simp only [CollatzResearch.WordTrace]
  refine ⟨2240599995194195813251177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11949866641035711004006277 2240599995194195813251177)
  ·
    refine ⟨1680449996395646859938383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2240599995194195813251177 1680449996395646859938383)
    ·
      refine ⟨2520674994593470289907575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1680449996395646859938383 2520674994593470289907575)
      ·
        refine ⟨3781012491890205434861363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2520674994593470289907575 3781012491890205434861363)
        ·
          refine ⟨5671518737835308152292045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3781012491890205434861363 5671518737835308152292045)
          ·
            refine ⟨2126819526688240557109517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5671518737835308152292045 2126819526688240557109517)
            ·
              refine ⟨797557322508090208916069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2126819526688240557109517 797557322508090208916069)
              ·
                refine ⟨149541997970266914171763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 797557322508090208916069 149541997970266914171763)
                ·
                  rfl

theorem cell19_491454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_491454 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_491454 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_491454 prefixEnd_491454 := by exact prefixLift 491454
  have htrace : WordTrace (prefixWord ++ tailWord_491454) baseStart_491454 baseEnd_491454 := by
    simpa [prefixWord, tailWord_491454, baseEnd_491454] using wordTrace_append hprefix tailTrace_491454
  have hstable : (prefixWord ++ tailWord_491454).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491454).length < 2 ^ (prefixWord ++ tailWord_491454).sum := by decide
  have hdescent : baseEnd_491454 < baseStart_491454 := by decide
  rcases family_descends (prefixWord ++ tailWord_491454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan19Incremental
