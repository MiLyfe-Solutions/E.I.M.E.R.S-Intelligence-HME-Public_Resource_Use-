import V185TrunkScan23Chunk0894

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5297520 : List Nat := [2, 1, 1, 1, 4, 2, 3, 3, 1, 2, 3]
def baseStart_5297520 : Nat := 118140960795 + 5297520 * 2 ^ 59
def prefixEnd_5297520 : Nat := 4983230072969 + 3 ^ 40 * 5297520 * 2
def baseEnd_5297520 : Nat := 2720174036806218662337155

theorem tailTrace_5297520 : CollatzResearch.WordTrace tailWord_5297520 prefixEnd_5297520 2720174036806218662337155 := by
  unfold tailWord_5297520
  simp only [CollatzResearch.WordTrace]
  refine ⟨96608213883998629615365007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128810951845331506153820009 96608213883998629615365007)
  ·
    refine ⟨144912320825997944423047511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96608213883998629615365007 144912320825997944423047511)
    ·
      refine ⟨217368481238996916634571267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144912320825997944423047511 217368481238996916634571267)
      ·
        refine ⟨326052721858495374951856901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217368481238996916634571267 326052721858495374951856901)
        ·
          refine ⟨61134885348467882803473169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 326052721858495374951856901 61134885348467882803473169)
          ·
            refine ⟨45851164011350912102604877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61134885348467882803473169 45851164011350912102604877)
            ·
              refine ⟨17194186504256592038476829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45851164011350912102604877 17194186504256592038476829)
              ·
                refine ⟨6447819939096222014428811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17194186504256592038476829 6447819939096222014428811)
                ·
                  refine ⟨9671729908644333021643217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6447819939096222014428811 9671729908644333021643217)
                  ·
                    refine ⟨7253797431483249766232413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9671729908644333021643217 7253797431483249766232413)
                    ·
                      refine ⟨2720174036806218662337155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7253797431483249766232413 2720174036806218662337155)
                      ·
                        rfl

theorem cell23_5297520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 3, 1, 2, 3].length) (baseStart_5297520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5297520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5297520 prefixEnd_5297520 := by exact prefixLift 5297520
  have htrace : WordTrace (prefixWord ++ tailWord_5297520) baseStart_5297520 baseEnd_5297520 := by
    simpa [prefixWord, tailWord_5297520, baseEnd_5297520] using wordTrace_append hprefix tailTrace_5297520
  have hstable : (prefixWord ++ tailWord_5297520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5297520).length < 2 ^ (prefixWord ++ tailWord_5297520).sum := by decide
  have hdescent : baseEnd_5297520 < baseStart_5297520 := by decide
  rcases family_descends (prefixWord ++ tailWord_5297520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5297536 : List Nat := [2, 1, 1, 2, 1, 2, 1, 3, 1, 9]
def baseStart_5297536 : Nat := 118140960795 + 5297536 * 2 ^ 59
def prefixEnd_5297536 : Nat := 4983230072969 + 3 ^ 40 * 5297536 * 2
def baseEnd_5297536 : Nat := 906727417498896866579027

theorem tailTrace_5297536 : CollatzResearch.WordTrace tailWord_5297536 prefixEnd_5297536 906727417498896866579027 := by
  unfold tailWord_5297536
  simp only [CollatzResearch.WordTrace]
  refine ⟨96608505667969646981656231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128811340890626195975541641 96608505667969646981656231)
  ·
    refine ⟨144912758501954470472484347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96608505667969646981656231 144912758501954470472484347)
    ·
      refine ⟨217369137752931705708726521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144912758501954470472484347 217369137752931705708726521)
      ·
        refine ⟨163026853314698779281544891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 217369137752931705708726521 163026853314698779281544891)
        ·
          refine ⟨244540279972048168922317337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163026853314698779281544891 244540279972048168922317337)
          ·
            refine ⟨183405209979036126691738003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 244540279972048168922317337 183405209979036126691738003)
            ·
              refine ⟨275107814968554190037607005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 183405209979036126691738003 275107814968554190037607005)
              ·
                refine ⟨103165430613207821264102627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 275107814968554190037607005 103165430613207821264102627)
                ·
                  refine ⟨154748145919811731896153941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 103165430613207821264102627 154748145919811731896153941)
                  ·
                    refine ⟨906727417498896866579027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 154748145919811731896153941 906727417498896866579027)
                    ·
                      rfl

theorem cell23_5297536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 1, 9].length) (baseStart_5297536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5297536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5297536 prefixEnd_5297536 := by exact prefixLift 5297536
  have htrace : WordTrace (prefixWord ++ tailWord_5297536) baseStart_5297536 baseEnd_5297536 := by
    simpa [prefixWord, tailWord_5297536, baseEnd_5297536] using wordTrace_append hprefix tailTrace_5297536
  have hstable : (prefixWord ++ tailWord_5297536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5297536).length < 2 ^ (prefixWord ++ tailWord_5297536).sum := by decide
  have hdescent : baseEnd_5297536 < baseStart_5297536 := by decide
  rcases family_descends (prefixWord ++ tailWord_5297536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5297603 : List Nat := [1, 1, 1, 3, 1, 1, 4, 3, 2, 2, 4]
def baseStart_5297603 : Nat := 118140960795 + 5297603 * 2 ^ 59
def prefixEnd_5297603 : Nat := 4983230072969 + 3 ^ 40 * 5297603 * 2
def baseEnd_5297603 : Nat := 2720216655700541837599273

theorem tailTrace_5297603 : CollatzResearch.WordTrace tailWord_5297603 prefixEnd_5297603 2720216655700541837599273 := by
  unfold tailWord_5297603
  simp only [CollatzResearch.WordTrace]
  refine ⟨193219455026696564406001463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128812970017797709604000975 193219455026696564406001463)
  ·
    refine ⟨289829182540044846609002195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193219455026696564406001463 289829182540044846609002195)
    ·
      refine ⟨434743773810067269913503293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289829182540044846609002195 434743773810067269913503293)
      ·
        refine ⟨163028915178775226217563735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 434743773810067269913503293 163028915178775226217563735)
        ·
          refine ⟨244543372768162839326345603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163028915178775226217563735 244543372768162839326345603)
          ·
            refine ⟨366815059152244258989518405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 244543372768162839326345603 366815059152244258989518405)
            ·
              refine ⟨68777823591045798560534701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 366815059152244258989518405 68777823591045798560534701)
              ·
                refine ⟨25791683846642174460200513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68777823591045798560534701 25791683846642174460200513)
                ·
                  refine ⟨19343762884981630845150385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25791683846642174460200513 19343762884981630845150385)
                  ·
                    refine ⟨14507822163736223133862789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19343762884981630845150385 14507822163736223133862789)
                    ·
                      refine ⟨2720216655700541837599273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14507822163736223133862789 2720216655700541837599273)
                      ·
                        rfl

theorem cell23_5297603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 3, 2, 2, 4].length) (baseStart_5297603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5297603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5297603 prefixEnd_5297603 := by exact prefixLift 5297603
  have htrace : WordTrace (prefixWord ++ tailWord_5297603) baseStart_5297603 baseEnd_5297603 := by
    simpa [prefixWord, tailWord_5297603, baseEnd_5297603] using wordTrace_append hprefix tailTrace_5297603
  have hstable : (prefixWord ++ tailWord_5297603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5297603).length < 2 ^ (prefixWord ++ tailWord_5297603).sum := by decide
  have hdescent : baseEnd_5297603 < baseStart_5297603 := by decide
  rcases family_descends (prefixWord ++ tailWord_5297603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5297640 : List Nat := [2, 1, 4, 1, 1, 2, 2, 2, 2, 3, 3]
def baseStart_5297640 : Nat := 118140960795 + 5297640 * 2 ^ 59
def prefixEnd_5297640 : Nat := 4983230072969 + 3 ^ 40 * 5297640 * 2
def baseEnd_5297640 : Nat := 2720235654484758192836603

theorem tailTrace_5297640 : CollatzResearch.WordTrace tailWord_5297640 prefixEnd_5297640 2720235654484758192836603 := by
  unfold tailWord_5297640
  simp only [CollatzResearch.WordTrace]
  refine ⟨96610402263781259862549187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128813869685041679816732249 96610402263781259862549187)
  ·
    refine ⟨144915603395671889793823781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96610402263781259862549187 144915603395671889793823781)
    ·
      refine ⟨27171675636688479336341959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 144915603395671889793823781 27171675636688479336341959)
      ·
        refine ⟨40757513455032719004512939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27171675636688479336341959 40757513455032719004512939)
        ·
          refine ⟨61136270182549078506769409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40757513455032719004512939 61136270182549078506769409)
          ·
            refine ⟨45852202636911808880077057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61136270182549078506769409 45852202636911808880077057)
            ·
              refine ⟨34389151977683856660057793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45852202636911808880077057 34389151977683856660057793)
              ·
                refine ⟨25791863983262892495043345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34389151977683856660057793 25791863983262892495043345)
                ·
                  refine ⟨19343897987447169371282509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25791863983262892495043345 19343897987447169371282509)
                  ·
                    refine ⟨7253961745292688514230941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19343897987447169371282509 7253961745292688514230941)
                    ·
                      refine ⟨2720235654484758192836603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7253961745292688514230941 2720235654484758192836603)
                      ·
                        rfl

theorem cell23_5297640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 2, 2, 3, 3].length) (baseStart_5297640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5297640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5297640 prefixEnd_5297640 := by exact prefixLift 5297640
  have htrace : WordTrace (prefixWord ++ tailWord_5297640) baseStart_5297640 baseEnd_5297640 := by
    simpa [prefixWord, tailWord_5297640, baseEnd_5297640] using wordTrace_append hprefix tailTrace_5297640
  have hstable : (prefixWord ++ tailWord_5297640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5297640).length < 2 ^ (prefixWord ++ tailWord_5297640).sum := by decide
  have hdescent : baseEnd_5297640 < baseStart_5297640 := by decide
  rcases family_descends (prefixWord ++ tailWord_5297640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5297643 : List Nat := [1, 1, 1, 1, 2, 3, 2, 3, 4, 5]
def baseStart_5297643 : Nat := 118140960795 + 5297643 * 2 ^ 59
def prefixEnd_5297643 : Nat := 4983230072969 + 3 ^ 40 * 5297643 * 2
def baseEnd_5297643 : Nat := 906745731642240560366363

theorem tailTrace_5297643 : CollatzResearch.WordTrace tailWord_5297643 prefixEnd_5297643 906745731642240560366363 := by
  unfold tailWord_5297643
  simp only [CollatzResearch.WordTrace]
  refine ⟨193220913946551651237457583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128813942631034434158305055 193220913946551651237457583)
  ·
    refine ⟨289831370919827476856186375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193220913946551651237457583 289831370919827476856186375)
    ·
      refine ⟨434747056379741215284279563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289831370919827476856186375 434747056379741215284279563)
      ·
        refine ⟨652120584569611822926419345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 434747056379741215284279563 652120584569611822926419345)
        ·
          refine ⟨489090438427208867194814509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 652120584569611822926419345 489090438427208867194814509)
          ·
            refine ⟨183408914410203325198055441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 489090438427208867194814509 183408914410203325198055441)
            ·
              refine ⟨137556685807652493898541581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 183408914410203325198055441 137556685807652493898541581)
              ·
                refine ⟨51583757177869685211953093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 137556685807652493898541581 51583757177869685211953093)
                ·
                  refine ⟨9671954470850565977241205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51583757177869685211953093 9671954470850565977241205)
                  ·
                    refine ⟨906745731642240560366363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9671954470850565977241205 906745731642240560366363)
                    ·
                      rfl

theorem cell23_5297643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 4, 5].length) (baseStart_5297643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5297643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5297643 prefixEnd_5297643 := by exact prefixLift 5297643
  have htrace : WordTrace (prefixWord ++ tailWord_5297643) baseStart_5297643 baseEnd_5297643 := by
    simpa [prefixWord, tailWord_5297643, baseEnd_5297643] using wordTrace_append hprefix tailTrace_5297643
  have hstable : (prefixWord ++ tailWord_5297643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5297643).length < 2 ^ (prefixWord ++ tailWord_5297643).sum := by decide
  have hdescent : baseEnd_5297643 < baseStart_5297643 := by decide
  rcases family_descends (prefixWord ++ tailWord_5297643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5297647 : List Nat := [1, 1, 2, 1, 4, 1, 6, 2, 5]
def baseStart_5297647 : Nat := 118140960795 + 5297647 * 2 ^ 59
def prefixEnd_5297647 : Nat := 4983230072969 + 3 ^ 40 * 5297647 * 2
def baseEnd_5297647 : Nat := 302248805427704407272119

theorem tailTrace_5297647 : CollatzResearch.WordTrace tailWord_5297647 prefixEnd_5297647 302248805427704407272119 := by
  unfold tailWord_5297647
  simp only [CollatzResearch.WordTrace]
  refine ⟨193221059838537159920603195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128814039892358106613735463 193221059838537159920603195)
  ·
    refine ⟨289831589757805739880904793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193221059838537159920603195 289831589757805739880904793)
    ·
      refine ⟨217373692318354304910678595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 289831589757805739880904793 217373692318354304910678595)
      ·
        refine ⟨326060538477531457366017893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217373692318354304910678595 326060538477531457366017893)
        ·
          refine ⟨61136350964537148256128355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 326060538477531457366017893 61136350964537148256128355)
          ·
            refine ⟨91704526446805722384192533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61136350964537148256128355 91704526446805722384192533)
            ·
              refine ⟨4298649677194018236759025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 91704526446805722384192533 4298649677194018236759025)
              ·
                refine ⟨3223987257895513677569269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4298649677194018236759025 3223987257895513677569269)
                ·
                  refine ⟨302248805427704407272119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3223987257895513677569269 302248805427704407272119)
                  ·
                    rfl

theorem cell23_5297647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 6, 2, 5].length) (baseStart_5297647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5297647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5297647 prefixEnd_5297647 := by exact prefixLift 5297647
  have htrace : WordTrace (prefixWord ++ tailWord_5297647) baseStart_5297647 baseEnd_5297647 := by
    simpa [prefixWord, tailWord_5297647, baseEnd_5297647] using wordTrace_append hprefix tailTrace_5297647
  have hstable : (prefixWord ++ tailWord_5297647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5297647).length < 2 ^ (prefixWord ++ tailWord_5297647).sum := by decide
  have hdescent : baseEnd_5297647 < baseStart_5297647 := by decide
  rcases family_descends (prefixWord ++ tailWord_5297647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5297690 : List Nat := [3, 1, 1, 3, 1, 1, 1, 1, 7, 4]
def baseStart_5297690 : Nat := 118140960795 + 5297690 * 2 ^ 59
def prefixEnd_5297690 : Nat := 4983230072969 + 3 ^ 40 * 5297690 * 2
def baseEnd_5297690 : Nat := 906753776172494332403791

theorem tailTrace_5297690 : CollatzResearch.WordTrace tailWord_5297690 prefixEnd_5297690 906753776172494332403791 := by
  unfold tailWord_5297690
  simp only [CollatzResearch.WordTrace]
  refine ⟨48305657044345344566104631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128815085451587585509612349 48305657044345344566104631)
  ·
    refine ⟨72458485566518016849156947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48305657044345344566104631 72458485566518016849156947)
    ·
      refine ⟨108687728349777025273735421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72458485566518016849156947 108687728349777025273735421)
      ·
        refine ⟨40757898131166384477650783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108687728349777025273735421 40757898131166384477650783)
        ·
          refine ⟨61136847196749576716476175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40757898131166384477650783 61136847196749576716476175)
          ·
            refine ⟨91705270795124365074714263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61136847196749576716476175 91705270795124365074714263)
            ·
              refine ⟨137557906192686547612071395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91705270795124365074714263 137557906192686547612071395)
              ·
                refine ⟨206336859289029821418107093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 137557906192686547612071395 206336859289029821418107093)
                ·
                  refine ⟨4836020139586636439486885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 206336859289029821418107093 4836020139586636439486885)
                  ·
                    refine ⟨906753776172494332403791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4836020139586636439486885 906753776172494332403791)
                    ·
                      rfl

theorem cell23_5297690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 7, 4].length) (baseStart_5297690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5297690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5297690 prefixEnd_5297690 := by exact prefixLift 5297690
  have htrace : WordTrace (prefixWord ++ tailWord_5297690) baseStart_5297690 baseEnd_5297690 := by
    simpa [prefixWord, tailWord_5297690, baseEnd_5297690] using wordTrace_append hprefix tailTrace_5297690
  have hstable : (prefixWord ++ tailWord_5297690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5297690).length < 2 ^ (prefixWord ++ tailWord_5297690).sum := by decide
  have hdescent : baseEnd_5297690 < baseStart_5297690 := by decide
  rcases family_descends (prefixWord ++ tailWord_5297690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5297697 : List Nat := [1, 2, 3, 2, 2, 2, 1, 2, 2, 4, 2]
def baseStart_5297697 : Nat := 118140960795 + 5297697 * 2 ^ 59
def prefixEnd_5297697 : Nat := 4983230072969 + 3 ^ 40 * 5297697 * 2
def baseEnd_5297697 : Nat := 2720264922882064469823841

theorem tailTrace_5297697 : CollatzResearch.WordTrace tailWord_5297697 prefixEnd_5297697 2720264922882064469823841 := by
  unfold tailWord_5297697
  simp only [CollatzResearch.WordTrace]
  refine ⟨193222883488356018459923345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128815255658904012306615563 193222883488356018459923345)
  ·
    refine ⟨144917162616267013844942509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193222883488356018459923345 144917162616267013844942509)
    ·
      refine ⟨54343935981100130191853441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144917162616267013844942509 54343935981100130191853441)
      ·
        refine ⟨40757951985825097643890081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54343935981100130191853441 40757951985825097643890081)
        ·
          refine ⟨30568463989368823232917561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40757951985825097643890081 30568463989368823232917561)
          ·
            refine ⟨22926347992026617424688171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30568463989368823232917561 22926347992026617424688171)
            ·
              refine ⟨34389521988039926137032257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22926347992026617424688171 34389521988039926137032257)
              ·
                refine ⟨25792141491029944602774193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34389521988039926137032257 25792141491029944602774193)
                ·
                  refine ⟨19344106118272458452080645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25792141491029944602774193 19344106118272458452080645)
                  ·
                    refine ⟨3627019897176085959765121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19344106118272458452080645 3627019897176085959765121)
                    ·
                      refine ⟨2720264922882064469823841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3627019897176085959765121 2720264922882064469823841)
                      ·
                        rfl

theorem cell23_5297697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 2, 2, 4, 2].length) (baseStart_5297697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5297697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5297697 prefixEnd_5297697 := by exact prefixLift 5297697
  have htrace : WordTrace (prefixWord ++ tailWord_5297697) baseStart_5297697 baseEnd_5297697 := by
    simpa [prefixWord, tailWord_5297697, baseEnd_5297697] using wordTrace_append hprefix tailTrace_5297697
  have hstable : (prefixWord ++ tailWord_5297697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5297697).length < 2 ^ (prefixWord ++ tailWord_5297697).sum := by decide
  have hdescent : baseEnd_5297697 < baseStart_5297697 := by decide
  rcases family_descends (prefixWord ++ tailWord_5297697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5297764 : List Nat := [2, 3, 1, 1, 2, 3, 3, 1, 3, 1, 3]
def baseStart_5297764 : Nat := 118140960795 + 5297764 * 2 ^ 59
def prefixEnd_5297764 : Nat := 4983230072969 + 3 ^ 40 * 5297764 * 2
def baseEnd_5297764 : Nat := 2720299326085915707686033

theorem tailTrace_5297764 : CollatzResearch.WordTrace tailWord_5297764 prefixEnd_5297764 2720299326085915707686033 := by
  unfold tailWord_5297764
  simp only [CollatzResearch.WordTrace]
  refine ⟨96612663589556644451306173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128816884786075525935074897 96612663589556644451306173)
  ·
    refine ⟨36229748846083741669239815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96612663589556644451306173 36229748846083741669239815)
    ·
      refine ⟨54344623269125612503859723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36229748846083741669239815 54344623269125612503859723)
      ·
        refine ⟨81516934903688418755789585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54344623269125612503859723 81516934903688418755789585)
        ·
          refine ⟨61137701177766314066842189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81516934903688418755789585 61137701177766314066842189)
          ·
            refine ⟨22926637941662367775065821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61137701177766314066842189 22926637941662367775065821)
            ·
              refine ⟨8597489228123387915649683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22926637941662367775065821 8597489228123387915649683)
              ·
                refine ⟨12896233842185081873474525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8597489228123387915649683 12896233842185081873474525)
                ·
                  refine ⟨4836087690819405702552947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12896233842185081873474525 4836087690819405702552947)
                  ·
                    refine ⟨7254131536229108553829421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4836087690819405702552947 7254131536229108553829421)
                    ·
                      refine ⟨2720299326085915707686033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7254131536229108553829421 2720299326085915707686033)
                      ·
                        rfl

theorem cell23_5297764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 1, 3, 1, 3].length) (baseStart_5297764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5297764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5297764 prefixEnd_5297764 := by exact prefixLift 5297764
  have htrace : WordTrace (prefixWord ++ tailWord_5297764) baseStart_5297764 baseEnd_5297764 := by
    simpa [prefixWord, tailWord_5297764, baseEnd_5297764] using wordTrace_append hprefix tailTrace_5297764
  have hstable : (prefixWord ++ tailWord_5297764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5297764).length < 2 ^ (prefixWord ++ tailWord_5297764).sum := by decide
  have hdescent : baseEnd_5297764 < baseStart_5297764 := by decide
  rcases family_descends (prefixWord ++ tailWord_5297764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5297804 : List Nat := [2, 2, 1, 2, 1, 1, 7, 1, 1, 1, 4]
def baseStart_5297804 : Nat := 118140960795 + 5297804 * 2 ^ 59
def prefixEnd_5297804 : Nat := 4983230072969 + 3 ^ 40 * 5297804 * 2
def baseEnd_5297804 : Nat := 2720319865312095551185849

theorem tailTrace_5297804 : CollatzResearch.WordTrace tailWord_5297804 prefixEnd_5297804 2720319865312095551185849 := by
  unfold tailWord_5297804
  simp only [CollatzResearch.WordTrace]
  refine ⟨96613393049484187867034233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128817857399312250489378977 96613393049484187867034233)
  ·
    refine ⟨72460044787113140900275675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96613393049484187867034233 72460044787113140900275675)
    ·
      refine ⟨108690067180669711350413513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72460044787113140900275675 108690067180669711350413513)
      ·
        refine ⟨81517550385502283512810135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108690067180669711350413513 81517550385502283512810135)
        ·
          refine ⟨122276325578253425269215203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81517550385502283512810135 122276325578253425269215203)
          ·
            refine ⟨183414488367380137903822805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122276325578253425269215203 183414488367380137903822805)
            ·
              refine ⟨4298777071110471982120847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 183414488367380137903822805 4298777071110471982120847)
              ·
                refine ⟨6448165606665707973181271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4298777071110471982120847 6448165606665707973181271)
                ·
                  refine ⟨9672248409998561959771907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6448165606665707973181271 9672248409998561959771907)
                  ·
                    refine ⟨14508372614997842939657861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9672248409998561959771907 14508372614997842939657861)
                    ·
                      refine ⟨2720319865312095551185849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14508372614997842939657861 2720319865312095551185849)
                      ·
                        rfl

theorem cell23_5297804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 7, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 7, 1, 1, 1, 4].length) (baseStart_5297804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5297804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5297804 prefixEnd_5297804 := by exact prefixLift 5297804
  have htrace : WordTrace (prefixWord ++ tailWord_5297804) baseStart_5297804 baseEnd_5297804 := by
    simpa [prefixWord, tailWord_5297804, baseEnd_5297804] using wordTrace_append hprefix tailTrace_5297804
  have hstable : (prefixWord ++ tailWord_5297804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5297804).length < 2 ^ (prefixWord ++ tailWord_5297804).sum := by decide
  have hdescent : baseEnd_5297804 < baseStart_5297804 := by decide
  rcases family_descends (prefixWord ++ tailWord_5297804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5297810 : List Nat := [3, 2, 3, 1, 14]
def baseStart_5297810 : Nat := 118140960795 + 5297810 * 2 ^ 59
def prefixEnd_5297810 : Nat := 4983230072969 + 3 ^ 40 * 5297810 * 2
def baseEnd_5297810 : Nat := 3731581544850511011949

theorem tailTrace_5297810 : CollatzResearch.WordTrace tailWord_5297810 prefixEnd_5297810 3731581544850511011949 := by
  unfold tailWord_5297810
  simp only [CollatzResearch.WordTrace]
  refine ⟨48306751234236659689696721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128818003291297759172524589 48306751234236659689696721)
  ·
    refine ⟨36230063425677494767272541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48306751234236659689696721 36230063425677494767272541)
    ·
      refine ⟨13586273784629060537727203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36230063425677494767272541 13586273784629060537727203)
      ·
        refine ⟨20379410676943590806590805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13586273784629060537727203 20379410676943590806590805)
        ·
          refine ⟨3731581544850511011949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 20379410676943590806590805 3731581544850511011949)
          ·
            rfl

theorem cell23_5297810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 14].length) (baseStart_5297810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5297810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5297810 prefixEnd_5297810 := by exact prefixLift 5297810
  have htrace : WordTrace (prefixWord ++ tailWord_5297810) baseStart_5297810 baseEnd_5297810 := by
    simpa [prefixWord, tailWord_5297810, baseEnd_5297810] using wordTrace_append hprefix tailTrace_5297810
  have hstable : (prefixWord ++ tailWord_5297810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5297810).length < 2 ^ (prefixWord ++ tailWord_5297810).sum := by decide
  have hdescent : baseEnd_5297810 < baseStart_5297810 := by decide
  rcases family_descends (prefixWord ++ tailWord_5297810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5297854 : List Nat := [4, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3]
def baseStart_5297854 : Nat := 118140960795 + 5297854 * 2 ^ 59
def prefixEnd_5297854 : Nat := 4983230072969 + 3 ^ 40 * 5297854 * 2
def baseEnd_5297854 : Nat := 2720345539344820355560619

theorem tailTrace_5297854 : CollatzResearch.WordTrace tailWord_5297854 prefixEnd_5297854 2720345539344820355560619 := by
  unfold tailWord_5297854
  simp only [CollatzResearch.WordTrace]
  refine ⟨24153576218598404284173577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128819073165858156182259077 24153576218598404284173577)
  ·
    refine ⟨18115182163948803213130183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24153576218598404284173577 18115182163948803213130183)
    ·
      refine ⟨27172773245923204819695275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18115182163948803213130183 27172773245923204819695275)
      ·
        refine ⟨40759159868884807229542913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27172773245923204819695275 40759159868884807229542913)
        ·
          refine ⟨30569369901663605422157185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40759159868884807229542913 30569369901663605422157185)
          ·
            refine ⟨22927027426247704066617889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30569369901663605422157185 22927027426247704066617889)
            ·
              refine ⟨17195270569685778049963417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22927027426247704066617889 17195270569685778049963417)
              ·
                refine ⟨12896452927264333537472563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17195270569685778049963417 12896452927264333537472563)
                ·
                  refine ⟨19344679390896500306208845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12896452927264333537472563 19344679390896500306208845)
                  ·
                    refine ⟨7254254771586187614828317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19344679390896500306208845 7254254771586187614828317)
                    ·
                      refine ⟨2720345539344820355560619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7254254771586187614828317 2720345539344820355560619)
                      ·
                        rfl

theorem cell23_5297854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3].length) (baseStart_5297854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5297854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5297854 prefixEnd_5297854 := by exact prefixLift 5297854
  have htrace : WordTrace (prefixWord ++ tailWord_5297854) baseStart_5297854 baseEnd_5297854 := by
    simpa [prefixWord, tailWord_5297854, baseEnd_5297854] using wordTrace_append hprefix tailTrace_5297854
  have hstable : (prefixWord ++ tailWord_5297854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5297854).length < 2 ^ (prefixWord ++ tailWord_5297854).sum := by decide
  have hdescent : baseEnd_5297854 < baseStart_5297854 := by decide
  rcases family_descends (prefixWord ++ tailWord_5297854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5297934 : List Nat := [4, 1, 1, 2, 1, 1, 2, 6, 5]
def baseStart_5297934 : Nat := 118140960795 + 5297934 * 2 ^ 59
def prefixEnd_5297934 : Nat := 4983230072969 + 3 ^ 40 * 5297934 * 2
def baseEnd_5297934 : Nat := 302265179755242226951139

theorem tailTrace_5297934 : CollatzResearch.WordTrace tailWord_5297934 prefixEnd_5297934 302265179755242226951139 := by
  unfold tailWord_5297934
  simp only [CollatzResearch.WordTrace]
  refine ⟨24153940948562175992037607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128821018392331605290867237 24153940948562175992037607)
  ·
    refine ⟨36230911422843263988056411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24153940948562175992037607 36230911422843263988056411)
    ·
      refine ⟨54346367134264895982084617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36230911422843263988056411 54346367134264895982084617)
      ·
        refine ⟨40759775350698671986563463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54346367134264895982084617 40759775350698671986563463)
        ·
          refine ⟨61139663026048007979845195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40759775350698671986563463 61139663026048007979845195)
          ·
            refine ⟨91709494539072011969767793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61139663026048007979845195 91709494539072011969767793)
            ·
              refine ⟨68782120904304008977325845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91709494539072011969767793 68782120904304008977325845)
              ·
                refine ⟨3224161917389250420812149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 68782120904304008977325845 3224161917389250420812149)
                ·
                  refine ⟨302265179755242226951139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3224161917389250420812149 302265179755242226951139)
                  ·
                    rfl

theorem cell23_5297934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 6, 5].length) (baseStart_5297934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5297934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5297934 prefixEnd_5297934 := by exact prefixLift 5297934
  have htrace : WordTrace (prefixWord ++ tailWord_5297934) baseStart_5297934 baseEnd_5297934 := by
    simpa [prefixWord, tailWord_5297934, baseEnd_5297934] using wordTrace_append hprefix tailTrace_5297934
  have hstable : (prefixWord ++ tailWord_5297934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5297934).length < 2 ^ (prefixWord ++ tailWord_5297934).sum := by decide
  have hdescent : baseEnd_5297934 < baseStart_5297934 := by decide
  rcases family_descends (prefixWord ++ tailWord_5297934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5297964 : List Nat := [2, 2, 1, 1, 1, 6, 2, 1, 2, 5]
def baseStart_5297964 : Nat := 118140960795 + 5297964 * 2 ^ 59
def prefixEnd_5297964 : Nat := 4983230072969 + 3 ^ 40 * 5297964 * 2
def baseEnd_5297964 : Nat := 906800674072271641728371

theorem tailTrace_5297964 : CollatzResearch.WordTrace tailWord_5297964 prefixEnd_5297964 906800674072271641728371 := by
  unfold tailWord_5297964
  simp only [CollatzResearch.WordTrace]
  refine ⟨96616310889194361529946473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128821747852259148706595297 96616310889194361529946473)
  ·
    refine ⟨72462233166895771147459855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96616310889194361529946473 72462233166895771147459855)
    ·
      refine ⟨108693349750343656721189783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72462233166895771147459855 108693349750343656721189783)
      ·
        refine ⟨163040024625515485081784675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108693349750343656721189783 163040024625515485081784675)
        ·
          refine ⟨244560036938273227622677013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163040024625515485081784675 244560036938273227622677013)
          ·
            refine ⟨11463751731481557544812985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 244560036938273227622677013 11463751731481557544812985)
            ·
              refine ⟨8597813798611168158609739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11463751731481557544812985 8597813798611168158609739)
              ·
                refine ⟨12896720697916752237914609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8597813798611168158609739 12896720697916752237914609)
                ·
                  refine ⟨9672540523437564178435957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12896720697916752237914609 9672540523437564178435957)
                  ·
                    refine ⟨906800674072271641728371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9672540523437564178435957 906800674072271641728371)
                    ·
                      rfl

theorem cell23_5297964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 5].length) (baseStart_5297964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5297964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5297964 prefixEnd_5297964 := by exact prefixLift 5297964
  have htrace : WordTrace (prefixWord ++ tailWord_5297964) baseStart_5297964 baseEnd_5297964 := by
    simpa [prefixWord, tailWord_5297964, baseEnd_5297964] using wordTrace_append hprefix tailTrace_5297964
  have hstable : (prefixWord ++ tailWord_5297964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5297964).length < 2 ^ (prefixWord ++ tailWord_5297964).sum := by decide
  have hdescent : baseEnd_5297964 < baseStart_5297964 := by decide
  rcases family_descends (prefixWord ++ tailWord_5297964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5297967 : List Nat := [1, 1, 2, 1, 2, 1, 2, 2, 6, 1, 4]
def baseStart_5297967 : Nat := 118140960795 + 5297967 * 2 ^ 59
def prefixEnd_5297967 : Nat := 4983230072969 + 3 ^ 40 * 5297967 * 2
def baseEnd_5297967 : Nat := 2720403562658778413447599

theorem tailTrace_5297967 : CollatzResearch.WordTrace tailWord_5297967 prefixEnd_5297967 2720403562658778413447599 := by
  unfold tailWord_5297967
  simp only [CollatzResearch.WordTrace]
  refine ⟨193232731197377854572252155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128821820798251903048168103 193232731197377854572252155)
  ·
    refine ⟨289849096796066781858378233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193232731197377854572252155 289849096796066781858378233)
    ·
      refine ⟨217386822597050086393783675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 289849096796066781858378233 217386822597050086393783675)
      ·
        refine ⟨326080233895575129590675513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217386822597050086393783675 326080233895575129590675513)
        ·
          refine ⟨244560175421681347193006635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 326080233895575129590675513 244560175421681347193006635)
          ·
            refine ⟨366840263132522020789509953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 244560175421681347193006635 366840263132522020789509953)
            ·
              refine ⟨275130197349391515592132465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 366840263132522020789509953 275130197349391515592132465)
              ·
                refine ⟨206347648012043636694099349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 275130197349391515592132465 206347648012043636694099349)
                ·
                  refine ⟨9672546000564545470035907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 206347648012043636694099349 9672546000564545470035907)
                  ·
                    refine ⟨14508819000846818205053861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9672546000564545470035907 14508819000846818205053861)
                    ·
                      refine ⟨2720403562658778413447599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14508819000846818205053861 2720403562658778413447599)
                      ·
                        rfl

theorem cell23_5297967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 6, 1, 4].length) (baseStart_5297967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5297967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5297967 prefixEnd_5297967 := by exact prefixLift 5297967
  have htrace : WordTrace (prefixWord ++ tailWord_5297967) baseStart_5297967 baseEnd_5297967 := by
    simpa [prefixWord, tailWord_5297967, baseEnd_5297967] using wordTrace_append hprefix tailTrace_5297967
  have hstable : (prefixWord ++ tailWord_5297967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5297967).length < 2 ^ (prefixWord ++ tailWord_5297967).sum := by decide
  have hdescent : baseEnd_5297967 < baseStart_5297967 := by decide
  rcases family_descends (prefixWord ++ tailWord_5297967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5297994 : List Nat := [3, 1, 2, 1, 1, 1, 4, 3, 3, 4]
def baseStart_5297994 : Nat := 118140960795 + 5297994 * 2 ^ 59
def prefixEnd_5297994 : Nat := 4983230072969 + 3 ^ 40 * 5297994 * 2
def baseEnd_5297994 : Nat := 906805808878816602603325

theorem tailTrace_5297994 : CollatzResearch.WordTrace tailWord_5297994 prefixEnd_5297994 906805808878816602603325 := by
  unfold tailWord_5297994
  simp only [CollatzResearch.WordTrace]
  refine ⟨48308428992070009545871259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128822477312186692122323357 48308428992070009545871259)
  ·
    refine ⟨72462643488105014318806889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48308428992070009545871259 72462643488105014318806889)
    ·
      refine ⟨54346982616078760739105167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72462643488105014318806889 54346982616078760739105167)
      ·
        refine ⟨81520473924118141108657751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54346982616078760739105167 81520473924118141108657751)
        ·
          refine ⟨122280710886177211662986627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81520473924118141108657751 122280710886177211662986627)
          ·
            refine ⟨183421066329265817494479941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122280710886177211662986627 183421066329265817494479941)
            ·
              refine ⟨34391449936737340780214989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 183421066329265817494479941 34391449936737340780214989)
              ·
                refine ⟨12896793726276502792580621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34391449936737340780214989 12896793726276502792580621)
                ·
                  refine ⟨4836297647353688547217733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12896793726276502792580621 4836297647353688547217733)
                  ·
                    refine ⟨906805808878816602603325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4836297647353688547217733 906805808878816602603325)
                    ·
                      rfl

theorem cell23_5297994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 3, 3, 4].length) (baseStart_5297994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5297994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5297994 prefixEnd_5297994 := by exact prefixLift 5297994
  have htrace : WordTrace (prefixWord ++ tailWord_5297994) baseStart_5297994 baseEnd_5297994 := by
    simpa [prefixWord, tailWord_5297994, baseEnd_5297994] using wordTrace_append hprefix tailTrace_5297994
  have hstable : (prefixWord ++ tailWord_5297994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5297994).length < 2 ^ (prefixWord ++ tailWord_5297994).sum := by decide
  have hdescent : baseEnd_5297994 < baseStart_5297994 := by decide
  rcases family_descends (prefixWord ++ tailWord_5297994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5298001 : List Nat := [1, 2, 2, 1, 5, 2, 1, 1, 2, 4, 2]
def baseStart_5298001 : Nat := 118140960795 + 5298001 * 2 ^ 59
def prefixEnd_5298001 : Nat := 4983230072969 + 3 ^ 40 * 5298001 * 2
def baseEnd_5298001 : Nat := 2720421021001031280422443

theorem tailTrace_5298001 : CollatzResearch.WordTrace tailWord_5298001 prefixEnd_5298001 2720421021001031280422443 := by
  unfold tailWord_5298001
  simp only [CollatzResearch.WordTrace]
  refine ⟨193233971279254678378989857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128822647519503118919326571 193233971279254678378989857)
  ·
    refine ⟨144925478459441008784242393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193233971279254678378989857 144925478459441008784242393)
    ·
      refine ⟨108694108844580756588181795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144925478459441008784242393 108694108844580756588181795)
      ·
        refine ⟨163041163266871134882272693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108694108844580756588181795 163041163266871134882272693)
        ·
          refine ⟨15285109056269168895213065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 163041163266871134882272693 15285109056269168895213065)
          ·
            refine ⟨11463831792201876671409799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15285109056269168895213065 11463831792201876671409799)
            ·
              refine ⟨17195747688302815007114699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11463831792201876671409799 17195747688302815007114699)
              ·
                refine ⟨25793621532454222510672049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17195747688302815007114699 25793621532454222510672049)
                ·
                  refine ⟨19345216149340666883004037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25793621532454222510672049 19345216149340666883004037)
                  ·
                    refine ⟨3627228028001375040563257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19345216149340666883004037 3627228028001375040563257)
                    ·
                      refine ⟨2720421021001031280422443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3627228028001375040563257 2720421021001031280422443)
                      ·
                        rfl

theorem cell23_5298001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 1, 2, 4, 2].length) (baseStart_5298001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5298001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5298001 prefixEnd_5298001 := by exact prefixLift 5298001
  have htrace : WordTrace (prefixWord ++ tailWord_5298001) baseStart_5298001 baseEnd_5298001 := by
    simpa [prefixWord, tailWord_5298001, baseEnd_5298001] using wordTrace_append hprefix tailTrace_5298001
  have hstable : (prefixWord ++ tailWord_5298001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5298001).length < 2 ^ (prefixWord ++ tailWord_5298001).sum := by decide
  have hdescent : baseEnd_5298001 < baseStart_5298001 := by decide
  rcases family_descends (prefixWord ++ tailWord_5298001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5298018 : List Nat := [3, 3, 2, 1, 2, 3, 1, 1, 2, 1, 4]
def baseStart_5298018 : Nat := 118140960795 + 5298018 * 2 ^ 59
def prefixEnd_5298018 : Nat := 4983230072969 + 3 ^ 40 * 5298018 * 2
def baseEnd_5298018 : Nat := 2720429750172157713909865

theorem tailTrace_5298018 : CollatzResearch.WordTrace tailWord_5298018 prefixEnd_5298018 2720429750172157713909865 := by
  unfold tailWord_5298018
  simp only [CollatzResearch.WordTrace]
  refine ⟨48308647830048272570589677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128823060880128726854905805 48308647830048272570589677)
  ·
    refine ⟨18115742936268102213971129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48308647830048272570589677 18115742936268102213971129)
    ·
      refine ⟨13586807202201076660478347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18115742936268102213971129 13586807202201076660478347)
      ·
        refine ⟨20380210803301614990717521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13586807202201076660478347 20380210803301614990717521)
        ·
          refine ⟨15285158102476211243038141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20380210803301614990717521 15285158102476211243038141)
          ·
            refine ⟨5731934288428579216139303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15285158102476211243038141 5731934288428579216139303)
            ·
              refine ⟨8597901432642868824208955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5731934288428579216139303 8597901432642868824208955)
              ·
                refine ⟨12896852148964303236313433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8597901432642868824208955 12896852148964303236313433)
                ·
                  refine ⟨9672639111723227427235075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12896852148964303236313433 9672639111723227427235075)
                  ·
                    refine ⟨14508958667584841140852613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9672639111723227427235075 14508958667584841140852613)
                    ·
                      refine ⟨2720429750172157713909865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14508958667584841140852613 2720429750172157713909865)
                      ·
                        rfl

theorem cell23_5298018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 1, 2, 1, 4].length) (baseStart_5298018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5298018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5298018 prefixEnd_5298018 := by exact prefixLift 5298018
  have htrace : WordTrace (prefixWord ++ tailWord_5298018) baseStart_5298018 baseEnd_5298018 := by
    simpa [prefixWord, tailWord_5298018, baseEnd_5298018] using wordTrace_append hprefix tailTrace_5298018
  have hstable : (prefixWord ++ tailWord_5298018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5298018).length < 2 ^ (prefixWord ++ tailWord_5298018).sum := by decide
  have hdescent : baseEnd_5298018 < baseStart_5298018 := by decide
  rcases family_descends (prefixWord ++ tailWord_5298018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5298028 : List Nat := [2, 2, 1, 1, 4, 3, 2, 3, 1, 4]
def baseStart_5298028 : Nat := 118140960795 + 5298028 * 2 ^ 59
def prefixEnd_5298028 : Nat := 4983230072969 + 3 ^ 40 * 5298028 * 2
def baseEnd_5298028 : Nat := 906811628326234224928273

theorem tailTrace_5298028 : CollatzResearch.WordTrace tailWord_5298028 prefixEnd_5298028 906811628326234224928273 := by
  unfold tailWord_5298028
  simp only [CollatzResearch.WordTrace]
  refine ⟨96617478025078430995111369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128823304033437907993481825 96617478025078430995111369)
  ·
    refine ⟨72463108518808823246333527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96617478025078430995111369 72463108518808823246333527)
    ·
      refine ⟨108694662778213234869500291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72463108518808823246333527 108694662778213234869500291)
      ·
        refine ⟨163041994167319852304250437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108694662778213234869500291 163041994167319852304250437)
        ·
          refine ⟨30570373906372472307046957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 163041994167319852304250437 30570373906372472307046957)
          ·
            refine ⟨11463890214889677115142609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30570373906372472307046957 11463890214889677115142609)
            ·
              refine ⟨8597917661167257836356957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11463890214889677115142609 8597917661167257836356957)
              ·
                refine ⟨3224219122937721688633859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8597917661167257836356957 3224219122937721688633859)
                ·
                  refine ⟨4836328684406582532950789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3224219122937721688633859 4836328684406582532950789)
                  ·
                    refine ⟨906811628326234224928273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4836328684406582532950789 906811628326234224928273)
                    ·
                      rfl

theorem cell23_5298028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 3, 1, 4].length) (baseStart_5298028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5298028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5298028 prefixEnd_5298028 := by exact prefixLift 5298028
  have htrace : WordTrace (prefixWord ++ tailWord_5298028) baseStart_5298028 baseEnd_5298028 := by
    simpa [prefixWord, tailWord_5298028, baseEnd_5298028] using wordTrace_append hprefix tailTrace_5298028
  have hstable : (prefixWord ++ tailWord_5298028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5298028).length < 2 ^ (prefixWord ++ tailWord_5298028).sum := by decide
  have hdescent : baseEnd_5298028 < baseStart_5298028 := by decide
  rcases family_descends (prefixWord ++ tailWord_5298028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5298051 : List Nat := [1, 1, 1, 3, 4, 2, 1, 3, 3, 1, 3]
def baseStart_5298051 : Nat := 118140960795 + 5298051 * 2 ^ 59
def prefixEnd_5298051 : Nat := 4983230072969 + 3 ^ 40 * 5298051 * 2
def baseEnd_5298051 : Nat := 2720446695033756084797213

theorem tailTrace_5298051 : CollatzResearch.WordTrace tailWord_5298051 prefixEnd_5298051 2720446695033756084797213 := by
  unfold tailWord_5298051
  simp only [CollatzResearch.WordTrace]
  refine ⟨193235794929073536918310007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128823863286049024612206671 193235794929073536918310007)
  ·
    refine ⟨289853692393610305377465011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193235794929073536918310007 289853692393610305377465011)
    ·
      refine ⟨434780538590415458066197517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289853692393610305377465011 434780538590415458066197517)
      ·
        refine ⟨163042701971405796774824069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 434780538590415458066197517 163042701971405796774824069)
        ·
          refine ⟨30570506619638586895279513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 163042701971405796774824069 30570506619638586895279513)
          ·
            refine ⟨22927879964728940171459635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30570506619638586895279513 22927879964728940171459635)
            ·
              refine ⟨34391819947093410257189453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22927879964728940171459635 34391819947093410257189453)
              ·
                refine ⟨12896932480160028846446045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34391819947093410257189453 12896932480160028846446045)
                ·
                  refine ⟨4836349680060010817417267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12896932480160028846446045 4836349680060010817417267)
                  ·
                    refine ⟨7254524520090016226125901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4836349680060010817417267 7254524520090016226125901)
                    ·
                      refine ⟨2720446695033756084797213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7254524520090016226125901 2720446695033756084797213)
                      ·
                        rfl

theorem cell23_5298051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 3, 3, 1, 3].length) (baseStart_5298051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5298051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5298051 prefixEnd_5298051 := by exact prefixLift 5298051
  have htrace : WordTrace (prefixWord ++ tailWord_5298051) baseStart_5298051 baseEnd_5298051 := by
    simpa [prefixWord, tailWord_5298051, baseEnd_5298051] using wordTrace_append hprefix tailTrace_5298051
  have hstable : (prefixWord ++ tailWord_5298051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5298051).length < 2 ^ (prefixWord ++ tailWord_5298051).sum := by decide
  have hdescent : baseEnd_5298051 < baseStart_5298051 := by decide
  rcases family_descends (prefixWord ++ tailWord_5298051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5298058 : List Nat := [3, 1, 2, 4, 2, 1, 3, 1, 6]
def baseStart_5298058 : Nat := 118140960795 + 5298058 * 2 ^ 59
def prefixEnd_5298058 : Nat := 4983230072969 + 3 ^ 40 * 5298058 * 2
def baseEnd_5298058 : Nat := 302272254377593061934409

theorem tailTrace_5298058 : CollatzResearch.WordTrace tailWord_5298058 prefixEnd_5298058 302272254377593061934409 := by
  unfold tailWord_5298058
  simp only [CollatzResearch.WordTrace]
  refine ⟨48309012560012044278453707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128824033493365451409209885 48309012560012044278453707)
  ·
    refine ⟨72463518840018066417680561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48309012560012044278453707 72463518840018066417680561)
    ·
      refine ⟨54347639130013549813260421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72463518840018066417680561 54347639130013549813260421)
      ·
        refine ⟨10190182336877540589986329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54347639130013549813260421 10190182336877540589986329)
        ·
          refine ⟨7642636752658155442489747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10190182336877540589986329 7642636752658155442489747)
          ·
            refine ⟨11463955128987233163734621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7642636752658155442489747 11463955128987233163734621)
            ·
              refine ⟨4298983173370212436400483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11463955128987233163734621 4298983173370212436400483)
              ·
                refine ⟨6448474760055318654600725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4298983173370212436400483 6448474760055318654600725)
                ·
                  refine ⟨302272254377593061934409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6448474760055318654600725 302272254377593061934409)
                  ·
                    rfl

theorem cell23_5298058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 3, 1, 6].length) (baseStart_5298058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5298058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5298058 prefixEnd_5298058 := by exact prefixLift 5298058
  have htrace : WordTrace (prefixWord ++ tailWord_5298058) baseStart_5298058 baseEnd_5298058 := by
    simpa [prefixWord, tailWord_5298058, baseEnd_5298058] using wordTrace_append hprefix tailTrace_5298058
  have hstable : (prefixWord ++ tailWord_5298058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5298058).length < 2 ^ (prefixWord ++ tailWord_5298058).sum := by decide
  have hdescent : baseEnd_5298058 < baseStart_5298058 := by decide
  rcases family_descends (prefixWord ++ tailWord_5298058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5298068 : List Nat := [2, 4, 2, 1, 1, 2, 2, 2, 3, 1, 3]
def baseStart_5298068 : Nat := 118140960795 + 5298068 * 2 ^ 59
def prefixEnd_5298068 : Nat := 4983230072969 + 3 ^ 40 * 5298068 * 2
def baseEnd_5298068 : Nat := 2720455424204882518284635

theorem tailTrace_5298068 : CollatzResearch.WordTrace tailWord_5298068 prefixEnd_5298068 2720455424204882518284635 := by
  unfold tailWord_5298068
  simp only [CollatzResearch.WordTrace]
  refine ⟨96618207485005974410839429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128824276646674632547785905 96618207485005974410839429)
  ·
    refine ⟨18115913903438620202032393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96618207485005974410839429 18115913903438620202032393)
    ·
      refine ⟨13586935427578965151524295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18115913903438620202032393 13586935427578965151524295)
      ·
        refine ⟨20380403141368447727286443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13586935427578965151524295 20380403141368447727286443)
        ·
          refine ⟨30570604712052671590929665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20380403141368447727286443 30570604712052671590929665)
          ·
            refine ⟨22927953534039503693197249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30570604712052671590929665 22927953534039503693197249)
            ·
              refine ⟨17195965150529627769897937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22927953534039503693197249 17195965150529627769897937)
              ·
                refine ⟨12896973862897220827423453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17195965150529627769897937 12896973862897220827423453)
                ·
                  refine ⟨4836365198586457810283795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12896973862897220827423453 4836365198586457810283795)
                  ·
                    refine ⟨7254547797879686715425693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4836365198586457810283795 7254547797879686715425693)
                    ·
                      refine ⟨2720455424204882518284635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7254547797879686715425693 2720455424204882518284635)
                      ·
                        rfl

theorem cell23_5298068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 2, 3, 1, 3].length) (baseStart_5298068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5298068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5298068 prefixEnd_5298068 := by exact prefixLift 5298068
  have htrace : WordTrace (prefixWord ++ tailWord_5298068) baseStart_5298068 baseEnd_5298068 := by
    simpa [prefixWord, tailWord_5298068, baseEnd_5298068] using wordTrace_append hprefix tailTrace_5298068
  have hstable : (prefixWord ++ tailWord_5298068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5298068).length < 2 ^ (prefixWord ++ tailWord_5298068).sum := by decide
  have hdescent : baseEnd_5298068 < baseStart_5298068 := by decide
  rcases family_descends (prefixWord ++ tailWord_5298068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5298071 : List Nat := [1, 1, 3, 3, 1, 4, 2, 2, 1, 5]
def baseStart_5298071 : Nat := 118140960795 + 5298071 * 2 ^ 59
def prefixEnd_5298071 : Nat := 4983230072969 + 3 ^ 40 * 5298071 * 2
def baseEnd_5298071 : Nat := 906818988215615335515707

theorem tailTrace_5298071 : CollatzResearch.WordTrace tailWord_5298071 prefixEnd_5298071 906818988215615335515707 := by
  unfold tailWord_5298071
  simp only [CollatzResearch.WordTrace]
  refine ⟨193236524389001080334038067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128824349592667386889358711 193236524389001080334038067)
  ·
    refine ⟨289854786583501620501057101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193236524389001080334038067 289854786583501620501057101)
    ·
      refine ⟨108695544968813107687896413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 289854786583501620501057101 108695544968813107687896413)
      ·
        refine ⟨40760829363304915382961155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108695544968813107687896413 40760829363304915382961155)
        ·
          refine ⟨61141244044957373074441733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40760829363304915382961155 61141244044957373074441733)
          ·
            refine ⟨11463983258429507451457825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61141244044957373074441733 11463983258429507451457825)
            ·
              refine ⟨8597987443822130588593369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11463983258429507451457825 8597987443822130588593369)
              ·
                refine ⟨6448490582866597941445027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8597987443822130588593369 6448490582866597941445027)
                ·
                  refine ⟨9672735874299896912167541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6448490582866597941445027 9672735874299896912167541)
                  ·
                    refine ⟨906818988215615335515707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9672735874299896912167541 906818988215615335515707)
                    ·
                      rfl

theorem cell23_5298071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 2, 1, 5].length) (baseStart_5298071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5298071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5298071 prefixEnd_5298071 := by exact prefixLift 5298071
  have htrace : WordTrace (prefixWord ++ tailWord_5298071) baseStart_5298071 baseEnd_5298071 := by
    simpa [prefixWord, tailWord_5298071, baseEnd_5298071] using wordTrace_append hprefix tailTrace_5298071
  have hstable : (prefixWord ++ tailWord_5298071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5298071).length < 2 ^ (prefixWord ++ tailWord_5298071).sum := by decide
  have hdescent : baseEnd_5298071 < baseStart_5298071 := by decide
  rcases family_descends (prefixWord ++ tailWord_5298071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5298101 : List Nat := [1, 3, 3, 2, 1, 2, 2, 1, 4, 4]
def baseStart_5298101 : Nat := 118140960795 + 5298101 * 2 ^ 59
def prefixEnd_5298101 : Nat := 4983230072969 + 3 ^ 40 * 5298101 * 2
def baseEnd_5298101 : Nat := 906824123022160296390661

theorem tailTrace_5298101 : CollatzResearch.WordTrace tailWord_5298101 prefixEnd_5298101 906824123022160296390661 := by
  unfold tailWord_5298101
  simp only [CollatzResearch.WordTrace]
  refine ⟨193237618578892395457630157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128825079052594930305086771 193237618578892395457630157)
  ·
    refine ⟨72464106967084648296611309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 193237618578892395457630157 72464106967084648296611309)
    ·
      refine ⟨27174040112656743111229241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72464106967084648296611309 27174040112656743111229241)
      ·
        refine ⟨20380530084492557333421931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27174040112656743111229241 20380530084492557333421931)
        ·
          refine ⟨30570795126738836000132897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20380530084492557333421931 30570795126738836000132897)
          ·
            refine ⟨22928096345054127000099673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30570795126738836000132897 22928096345054127000099673)
            ·
              refine ⟨17196072258790595250074755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22928096345054127000099673 17196072258790595250074755)
              ·
                refine ⟨25794108388185892875112133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17196072258790595250074755 25794108388185892875112133)
                ·
                  refine ⟨4836395322784854914083525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25794108388185892875112133 4836395322784854914083525)
                  ·
                    refine ⟨906824123022160296390661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4836395322784854914083525 906824123022160296390661)
                    ·
                      rfl

theorem cell23_5298101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 1, 4, 4].length) (baseStart_5298101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5298101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5298101 prefixEnd_5298101 := by exact prefixLift 5298101
  have htrace : WordTrace (prefixWord ++ tailWord_5298101) baseStart_5298101 baseEnd_5298101 := by
    simpa [prefixWord, tailWord_5298101, baseEnd_5298101] using wordTrace_append hprefix tailTrace_5298101
  have hstable : (prefixWord ++ tailWord_5298101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5298101).length < 2 ^ (prefixWord ++ tailWord_5298101).sum := by decide
  have hdescent : baseEnd_5298101 < baseStart_5298101 := by decide
  rcases family_descends (prefixWord ++ tailWord_5298101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5298107 : List Nat := [1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 7]
def baseStart_5298107 : Nat := 118140960795 + 5298107 * 2 ^ 59
def prefixEnd_5298107 : Nat := 4983230072969 + 3 ^ 40 * 5298107 * 2
def baseEnd_5298107 : Nat := 2720475449950407865696955

theorem tailTrace_5298107 : CollatzResearch.WordTrace tailWord_5298107 prefixEnd_5298107 2720475449950407865696955 := by
  unfold tailWord_5298107
  simp only [CollatzResearch.WordTrace]
  refine ⟨193237837416870658482348575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128825224944580438988232383 193237837416870658482348575)
  ·
    refine ⟨289856756125305987723522863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193237837416870658482348575 289856756125305987723522863)
    ·
      refine ⟨434785134187958981585284295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289856756125305987723522863 434785134187958981585284295)
      ·
        refine ⟨652177701281938472377926443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 434785134187958981585284295 652177701281938472377926443)
        ·
          refine ⟨978266551922907708566889665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 652177701281938472377926443 978266551922907708566889665)
          ·
            refine ⟨733699913942180781425167249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 978266551922907708566889665 733699913942180781425167249)
            ·
              refine ⟨550274935456635586068875437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 733699913942180781425167249 550274935456635586068875437)
              ·
                refine ⟨206353100796238344775828289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 550274935456635586068875437 206353100796238344775828289)
                ·
                  refine ⟨154764825597178758581871217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 206353100796238344775828289 154764825597178758581871217)
                  ·
                    refine ⟨116073619197884068936403413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 154764825597178758581871217 116073619197884068936403413)
                    ·
                      refine ⟨2720475449950407865696955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 116073619197884068936403413 2720475449950407865696955)
                      ·
                        rfl

theorem cell23_5298107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 7].length) (baseStart_5298107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5298107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5298107 prefixEnd_5298107 := by exact prefixLift 5298107
  have htrace : WordTrace (prefixWord ++ tailWord_5298107) baseStart_5298107 baseEnd_5298107 := by
    simpa [prefixWord, tailWord_5298107, baseEnd_5298107] using wordTrace_append hprefix tailTrace_5298107
  have hstable : (prefixWord ++ tailWord_5298107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5298107).length < 2 ^ (prefixWord ++ tailWord_5298107).sum := by decide
  have hdescent : baseEnd_5298107 < baseStart_5298107 := by decide
  rcases family_descends (prefixWord ++ tailWord_5298107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5298196 : List Nat := [2, 4, 3, 2, 2, 1, 2, 1, 1, 2, 3]
def baseStart_5298196 : Nat := 118140960795 + 5298196 * 2 ^ 59
def prefixEnd_5298196 : Nat := 4983230072969 + 3 ^ 40 * 5298196 * 2
def baseEnd_5298196 : Nat := 2720521149728658017484047

theorem tailTrace_5298196 : CollatzResearch.WordTrace tailWord_5298196 prefixEnd_5298196 2720521149728658017484047 := by
  unfold tailWord_5298196
  simp only [CollatzResearch.WordTrace]
  refine ⟨96620541756774113341169221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128827389009032151121558961 96620541756774113341169221)
  ·
    refine ⟨18116351579395146251469229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96620541756774113341169221 18116351579395146251469229)
    ·
      refine ⟨6793631842273179844300961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18116351579395146251469229 6793631842273179844300961)
      ·
        refine ⟨5095223881704884883225721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6793631842273179844300961 5095223881704884883225721)
        ·
          refine ⟨3821417911278663662419291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5095223881704884883225721 3821417911278663662419291)
          ·
            refine ⟨5732126866917995493628937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3821417911278663662419291 5732126866917995493628937)
            ·
              refine ⟨4299095150188496620221703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5732126866917995493628937 4299095150188496620221703)
              ·
                refine ⟨6448642725282744930332555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4299095150188496620221703 6448642725282744930332555)
                ·
                  refine ⟨9672964087924117395498833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6448642725282744930332555 9672964087924117395498833)
                  ·
                    refine ⟨7254723065943088046624125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9672964087924117395498833 7254723065943088046624125)
                    ·
                      refine ⟨2720521149728658017484047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7254723065943088046624125 2720521149728658017484047)
                      ·
                        rfl

theorem cell23_5298196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_5298196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5298196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5298196 prefixEnd_5298196 := by exact prefixLift 5298196
  have htrace : WordTrace (prefixWord ++ tailWord_5298196) baseStart_5298196 baseEnd_5298196 := by
    simpa [prefixWord, tailWord_5298196, baseEnd_5298196] using wordTrace_append hprefix tailTrace_5298196
  have hstable : (prefixWord ++ tailWord_5298196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5298196).length < 2 ^ (prefixWord ++ tailWord_5298196).sum := by decide
  have hdescent : baseEnd_5298196 < baseStart_5298196 := by decide
  rcases family_descends (prefixWord ++ tailWord_5298196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5298202 : List Nat := [3, 1, 1, 3, 1, 5, 2, 1, 1, 3, 2]
def baseStart_5298202 : Nat := 118140960795 + 5298202 * 2 ^ 59
def prefixEnd_5298202 : Nat := 4983230072969 + 3 ^ 40 * 5298202 * 2
def baseEnd_5298202 : Nat := 2720524230612584994009019

theorem tailTrace_5298202 : CollatzResearch.WordTrace tailWord_5298202 prefixEnd_5298202 2720524230612584994009019 := by
  unfold tailWord_5298202
  simp only [CollatzResearch.WordTrace]
  refine ⟨48310325587881622426764215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128827534901017659804704573 48310325587881622426764215)
  ·
    refine ⟨72465488381822433640146323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48310325587881622426764215 72465488381822433640146323)
    ·
      refine ⟨108698232572733650460219485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72465488381822433640146323 108698232572733650460219485)
      ·
        refine ⟨40761837214775118922582307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108698232572733650460219485 40761837214775118922582307)
        ·
          refine ⟨61142755822162678383873461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40761837214775118922582307 61142755822162678383873461)
          ·
            refine ⟨5732133358327751098488137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 61142755822162678383873461 5732133358327751098488137)
            ·
              refine ⟨4299100018745813323866103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5732133358327751098488137 4299100018745813323866103)
              ·
                refine ⟨6448650028118719985799155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4299100018745813323866103 6448650028118719985799155)
                ·
                  refine ⟨9672975042178079978698733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6448650028118719985799155 9672975042178079978698733)
                  ·
                    refine ⟨3627365640816779992012025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9672975042178079978698733 3627365640816779992012025)
                    ·
                      refine ⟨2720524230612584994009019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3627365640816779992012025 2720524230612584994009019)
                      ·
                        rfl

theorem cell23_5298202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 2, 1, 1, 3, 2].length) (baseStart_5298202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5298202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5298202 prefixEnd_5298202 := by exact prefixLift 5298202
  have htrace : WordTrace (prefixWord ++ tailWord_5298202) baseStart_5298202 baseEnd_5298202 := by
    simpa [prefixWord, tailWord_5298202, baseEnd_5298202] using wordTrace_append hprefix tailTrace_5298202
  have hstable : (prefixWord ++ tailWord_5298202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5298202).length < 2 ^ (prefixWord ++ tailWord_5298202).sum := by decide
  have hdescent : baseEnd_5298202 < baseStart_5298202 := by decide
  rcases family_descends (prefixWord ++ tailWord_5298202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5298231 : List Nat := [1, 1, 3, 1, 2, 2, 4, 1, 2, 3, 3]
def baseStart_5298231 : Nat := 118140960795 + 5298231 * 2 ^ 59
def prefixEnd_5298231 : Nat := 4983230072969 + 3 ^ 40 * 5298231 * 2
def baseEnd_5298231 : Nat := 2720539121551565380546385

theorem tailTrace_5298231 : CollatzResearch.WordTrace tailWord_5298231 prefixEnd_5298231 2720539121551565380546385 := by
  unfold tailWord_5298231
  simp only [CollatzResearch.WordTrace]
  refine ⟨193242360068421427659862547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128828240045614285106575031 193242360068421427659862547)
  ·
    refine ⟨289863540102632141489793821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193242360068421427659862547 289863540102632141489793821)
    ·
      refine ⟨108698827538487053058672683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 289863540102632141489793821 108698827538487053058672683)
      ·
        refine ⟨163048241307730579588009025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108698827538487053058672683 163048241307730579588009025)
        ·
          refine ⟨122286180980797934691006769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163048241307730579588009025 122286180980797934691006769)
          ·
            refine ⟨91714635735598451018255077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122286180980797934691006769 91714635735598451018255077)
            ·
              refine ⟨17196494200424709565922827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91714635735598451018255077 17196494200424709565922827)
              ·
                refine ⟨25794741300637064348884241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17196494200424709565922827 25794741300637064348884241)
                ·
                  refine ⟨19346055975477798261663181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25794741300637064348884241 19346055975477798261663181)
                  ·
                    refine ⟨7254770990804174348123693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19346055975477798261663181 7254770990804174348123693)
                    ·
                      refine ⟨2720539121551565380546385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7254770990804174348123693 2720539121551565380546385)
                      ·
                        rfl

theorem cell23_5298231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 1, 2, 3, 3].length) (baseStart_5298231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5298231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5298231 prefixEnd_5298231 := by exact prefixLift 5298231
  have htrace : WordTrace (prefixWord ++ tailWord_5298231) baseStart_5298231 baseEnd_5298231 := by
    simpa [prefixWord, tailWord_5298231, baseEnd_5298231] using wordTrace_append hprefix tailTrace_5298231
  have hstable : (prefixWord ++ tailWord_5298231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5298231).length < 2 ^ (prefixWord ++ tailWord_5298231).sum := by decide
  have hdescent : baseEnd_5298231 < baseStart_5298231 := by decide
  rcases family_descends (prefixWord ++ tailWord_5298231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5298232 : List Nat := [2, 1, 2, 1, 7, 1, 1, 1, 1, 4, 2]
def baseStart_5298232 : Nat := 118140960795 + 5298232 * 2 ^ 59
def prefixEnd_5298232 : Nat := 4983230072969 + 3 ^ 40 * 5298232 * 2
def baseEnd_5298232 : Nat := 2720539635032219876633881

theorem tailTrace_5298232 : CollatzResearch.WordTrace tailWord_5298232 prefixEnd_5298232 2720539635032219876633881 := by
  unfold tailWord_5298232
  simp only [CollatzResearch.WordTrace]
  refine ⟨96621198270708902415324475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128828264360945203220432633 96621198270708902415324475)
  ·
    refine ⟨144931797406063353622986713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96621198270708902415324475 144931797406063353622986713)
    ·
      refine ⟨108698848054547515217240035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144931797406063353622986713 108698848054547515217240035)
      ·
        refine ⟨163048272081821272825860053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108698848054547515217240035 163048272081821272825860053)
        ·
          refine ⟨3821443876917686081856095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 163048272081821272825860053 3821443876917686081856095)
          ·
            refine ⟨5732165815376529122784143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3821443876917686081856095 5732165815376529122784143)
            ·
              refine ⟨8598248723064793684176215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5732165815376529122784143 8598248723064793684176215)
              ·
                refine ⟨12897373084597190526264323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8598248723064793684176215 12897373084597190526264323)
                ·
                  refine ⟨19346059626895785789396485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12897373084597190526264323 19346059626895785789396485)
                  ·
                    refine ⟨3627386180042959835511841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19346059626895785789396485 3627386180042959835511841)
                    ·
                      refine ⟨2720539635032219876633881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3627386180042959835511841 2720539635032219876633881)
                      ·
                        rfl

theorem cell23_5298232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 1, 1, 4, 2].length) (baseStart_5298232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5298232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5298232 prefixEnd_5298232 := by exact prefixLift 5298232
  have htrace : WordTrace (prefixWord ++ tailWord_5298232) baseStart_5298232 baseEnd_5298232 := by
    simpa [prefixWord, tailWord_5298232, baseEnd_5298232] using wordTrace_append hprefix tailTrace_5298232
  have hstable : (prefixWord ++ tailWord_5298232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5298232).length < 2 ^ (prefixWord ++ tailWord_5298232).sum := by decide
  have hdescent : baseEnd_5298232 < baseStart_5298232 := by decide
  rcases family_descends (prefixWord ++ tailWord_5298232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5298268 : List Nat := [2, 2, 4, 1, 1, 3, 1, 2, 2, 5]
def baseStart_5298268 : Nat := 118140960795 + 5298268 * 2 ^ 59
def prefixEnd_5298268 : Nat := 4983230072969 + 3 ^ 40 * 5298268 * 2
def baseEnd_5298268 : Nat := 906852706778593911927905

theorem tailTrace_5298268 : CollatzResearch.WordTrace tailWord_5298268 prefixEnd_5298268 906852706778593911927905 := by
  unfold tailWord_5298268
  simp only [CollatzResearch.WordTrace]
  refine ⟨96621854784643691489479729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128829139712858255319306305 96621854784643691489479729)
  ·
    refine ⟨72466391088482768617109797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96621854784643691489479729 72466391088482768617109797)
    ·
      refine ⟨13587448329090519115708087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72466391088482768617109797 13587448329090519115708087)
      ·
        refine ⟨20381172493635778673562131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13587448329090519115708087 20381172493635778673562131)
        ·
          refine ⟨30571758740453668010343197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20381172493635778673562131 30571758740453668010343197)
          ·
            refine ⟨11464409527670125503878699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30571758740453668010343197 11464409527670125503878699)
            ·
              refine ⟨17196614291505188255818049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11464409527670125503878699 17196614291505188255818049)
              ·
                refine ⟨12897460718628891191863537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17196614291505188255818049 12897460718628891191863537)
                ·
                  refine ⟨9673095538971668393897653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12897460718628891191863537 9673095538971668393897653)
                  ·
                    refine ⟨906852706778593911927905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9673095538971668393897653 906852706778593911927905)
                    ·
                      rfl

theorem cell23_5298268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_5298268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5298268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5298268 prefixEnd_5298268 := by exact prefixLift 5298268
  have htrace : WordTrace (prefixWord ++ tailWord_5298268) baseStart_5298268 baseEnd_5298268 := by
    simpa [prefixWord, tailWord_5298268, baseEnd_5298268] using wordTrace_append hprefix tailTrace_5298268
  have hstable : (prefixWord ++ tailWord_5298268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5298268).length < 2 ^ (prefixWord ++ tailWord_5298268).sum := by decide
  have hdescent : baseEnd_5298268 < baseStart_5298268 := by decide
  rcases family_descends (prefixWord ++ tailWord_5298268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5298305 : List Nat := [1, 2, 4, 2, 3, 1, 2, 1, 2, 1, 4]
def baseStart_5298305 : Nat := 118140960795 + 5298305 * 2 ^ 59
def prefixEnd_5298305 : Nat := 4983230072969 + 3 ^ 40 * 5298305 * 2
def baseEnd_5298305 : Nat := 2720577119119998091021045

theorem tailTrace_5298305 : CollatzResearch.WordTrace tailWord_5298305 prefixEnd_5298305 2720577119119998091021045 := by
  unfold tailWord_5298305
  simp only [CollatzResearch.WordTrace]
  refine ⟨193245059070153338298056369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128830039380102225532037579 193245059070153338298056369)
  ·
    refine ⟨144933794302615003723542277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193245059070153338298056369 144933794302615003723542277)
    ·
      refine ⟨27175086431740313198164177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 144933794302615003723542277 27175086431740313198164177)
      ·
        refine ⟨20381314823805234898623133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27175086431740313198164177 20381314823805234898623133)
        ·
          refine ⟨7642993058926963086983675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20381314823805234898623133 7642993058926963086983675)
          ·
            refine ⟨11464489588390444630475513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7642993058926963086983675 11464489588390444630475513)
            ·
              refine ⟨8598367191292833472856635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11464489588390444630475513 8598367191292833472856635)
              ·
                refine ⟨12897550786939250209284953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8598367191292833472856635 12897550786939250209284953)
                ·
                  refine ⟨9673163090204437656963715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12897550786939250209284953 9673163090204437656963715)
                  ·
                    refine ⟨14509744635306656485445573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9673163090204437656963715 14509744635306656485445573)
                    ·
                      refine ⟨2720577119119998091021045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14509744635306656485445573 2720577119119998091021045)
                      ·
                        rfl

theorem cell23_5298305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_5298305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5298305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5298305 prefixEnd_5298305 := by exact prefixLift 5298305
  have htrace : WordTrace (prefixWord ++ tailWord_5298305) baseStart_5298305 baseEnd_5298305 := by
    simpa [prefixWord, tailWord_5298305, baseEnd_5298305] using wordTrace_append hprefix tailTrace_5298305
  have hstable : (prefixWord ++ tailWord_5298305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5298305).length < 2 ^ (prefixWord ++ tailWord_5298305).sum := by decide
  have hdescent : baseEnd_5298305 < baseStart_5298305 := by decide
  rcases family_descends (prefixWord ++ tailWord_5298305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5298341 : List Nat := [1, 3, 1, 2, 1, 3, 1, 1, 5, 5]
def baseStart_5298341 : Nat := 118140960795 + 5298341 * 2 ^ 59
def prefixEnd_5298341 : Nat := 4983230072969 + 3 ^ 40 * 5298341 * 2
def baseEnd_5298341 : Nat := 906865201474519983390293

theorem tailTrace_5298341 : CollatzResearch.WordTrace tailWord_5298341 prefixEnd_5298341 906865201474519983390293 := by
  unfold tailWord_5298341
  simp only [CollatzResearch.WordTrace]
  refine ⟨193246372098022916446366877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128830914732015277630911251 193246372098022916446366877)
  ·
    refine ⟨72467389536758593667387579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 193246372098022916446366877 72467389536758593667387579)
    ·
      refine ⟨108701084305137890501081369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72467389536758593667387579 108701084305137890501081369)
      ·
        refine ⟨81525813228853417875811027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108701084305137890501081369 81525813228853417875811027)
        ·
          refine ⟨122288719843280126813716541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81525813228853417875811027 122288719843280126813716541)
          ·
            refine ⟨45858269941230047555143703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 122288719843280126813716541 45858269941230047555143703)
            ·
              refine ⟨68787404911845071332715555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45858269941230047555143703 68787404911845071332715555)
              ·
                refine ⟨103181107367767606999073333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68787404911845071332715555 103181107367767606999073333)
                ·
                  refine ⟨9673228815728213156163125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 103181107367767606999073333 9673228815728213156163125)
                  ·
                    refine ⟨906865201474519983390293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9673228815728213156163125 906865201474519983390293)
                    ·
                      rfl

theorem cell23_5298341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 5, 5].length) (baseStart_5298341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5298341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5298341 prefixEnd_5298341 := by exact prefixLift 5298341
  have htrace : WordTrace (prefixWord ++ tailWord_5298341) baseStart_5298341 baseEnd_5298341 := by
    simpa [prefixWord, tailWord_5298341, baseEnd_5298341] using wordTrace_append hprefix tailTrace_5298341
  have hstable : (prefixWord ++ tailWord_5298341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5298341).length < 2 ^ (prefixWord ++ tailWord_5298341).sum := by decide
  have hdescent : baseEnd_5298341 < baseStart_5298341 := by decide
  rcases family_descends (prefixWord ++ tailWord_5298341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5298356 : List Nat := [2, 5, 3, 1, 1, 2, 1, 1, 2, 1, 4]
def baseStart_5298356 : Nat := 118140960795 + 5298356 * 2 ^ 59
def prefixEnd_5298356 : Nat := 4983230072969 + 3 ^ 40 * 5298356 * 2
def baseEnd_5298356 : Nat := 2720603306633377391483311

theorem tailTrace_5298356 : CollatzResearch.WordTrace tailWord_5298356 prefixEnd_5298356 2720603306633377391483311 := by
  unfold tailWord_5298356
  simp only [CollatzResearch.WordTrace]
  refine ⟨96623459596484287004081461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128831279461979049338775281 96623459596484287004081461)
  ·
    refine ⟨9058449337170401906632637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 96623459596484287004081461 9058449337170401906632637)
    ·
      refine ⟨3396918501438900714987239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9058449337170401906632637 3396918501438900714987239)
      ·
        refine ⟨5095377752158351072480859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3396918501438900714987239 5095377752158351072480859)
        ·
          refine ⟨7643066628237526608721289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5095377752158351072480859 7643066628237526608721289)
          ·
            refine ⟨5732299971178144956540967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7643066628237526608721289 5732299971178144956540967)
            ·
              refine ⟨8598449956767217434811451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5732299971178144956540967 8598449956767217434811451)
              ·
                refine ⟨12897674935150826152217177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8598449956767217434811451 12897674935150826152217177)
                ·
                  refine ⟨9673256201363119614162883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12897674935150826152217177 9673256201363119614162883)
                  ·
                    refine ⟨14509884302044679421244325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9673256201363119614162883 14509884302044679421244325)
                    ·
                      refine ⟨2720603306633377391483311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14509884302044679421244325 2720603306633377391483311)
                      ·
                        rfl

theorem cell23_5298356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_5298356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5298356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5298356 prefixEnd_5298356 := by exact prefixLift 5298356
  have htrace : WordTrace (prefixWord ++ tailWord_5298356) baseStart_5298356 baseEnd_5298356 := by
    simpa [prefixWord, tailWord_5298356, baseEnd_5298356] using wordTrace_append hprefix tailTrace_5298356
  have hstable : (prefixWord ++ tailWord_5298356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5298356).length < 2 ^ (prefixWord ++ tailWord_5298356).sum := by decide
  have hdescent : baseEnd_5298356 < baseStart_5298356 := by decide
  rcases family_descends (prefixWord ++ tailWord_5298356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5298391 : List Nat := [1, 1, 3, 2, 1, 2, 1, 4, 1, 1, 6]
def baseStart_5298391 : Nat := 118140960795 + 5298391 * 2 ^ 59
def prefixEnd_5298391 : Nat := 4983230072969 + 3 ^ 40 * 5298391 * 2
def baseEnd_5298391 : Nat := 2720621278456284754545649

theorem tailTrace_5298391 : CollatzResearch.WordTrace tailWord_5298391 prefixEnd_5298391 2720621278456284754545649 := by
  unfold tailWord_5298391
  simp only [CollatzResearch.WordTrace]
  refine ⟨193248195747841774985687027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128832130498561183323791351 193248195747841774985687027)
  ·
    refine ⟨289872293621762662478530541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193248195747841774985687027 289872293621762662478530541)
    ·
      refine ⟨108702110108160998429448953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 289872293621762662478530541 108702110108160998429448953)
      ·
        refine ⟨81526582581120748822086715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108702110108160998429448953 81526582581120748822086715)
        ·
          refine ⟨122289873871681123233130073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81526582581120748822086715 122289873871681123233130073)
          ·
            refine ⟨91717405403760842424847555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122289873871681123233130073 91717405403760842424847555)
            ·
              refine ⟨137576108105641263637271333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91717405403760842424847555 137576108105641263637271333)
              ·
                refine ⟨25795520269807736931988375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 137576108105641263637271333 25795520269807736931988375)
                ·
                  refine ⟨38693280404711605397982563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25795520269807736931988375 38693280404711605397982563)
                  ·
                    refine ⟨58039920607067408096973845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38693280404711605397982563 58039920607067408096973845)
                    ·
                      refine ⟨2720621278456284754545649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58039920607067408096973845 2720621278456284754545649)
                      ·
                        rfl

theorem cell23_5298391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 4, 1, 1, 6].length) (baseStart_5298391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5298391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5298391 prefixEnd_5298391 := by exact prefixLift 5298391
  have htrace : WordTrace (prefixWord ++ tailWord_5298391) baseStart_5298391 baseEnd_5298391 := by
    simpa [prefixWord, tailWord_5298391, baseEnd_5298391] using wordTrace_append hprefix tailTrace_5298391
  have hstable : (prefixWord ++ tailWord_5298391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5298391).length < 2 ^ (prefixWord ++ tailWord_5298391).sum := by decide
  have hdescent : baseEnd_5298391 < baseStart_5298391 := by decide
  rcases family_descends (prefixWord ++ tailWord_5298391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5298395 : List Nat := [1, 1, 1, 1, 1, 1, 1, 9, 3, 2, 2]
def baseStart_5298395 : Nat := 118140960795 + 5298395 * 2 ^ 59
def prefixEnd_5298395 : Nat := 4983230072969 + 3 ^ 40 * 5298395 * 2
def baseEnd_5298395 : Nat := 2720623332378902738895631

theorem tailTrace_5298395 : CollatzResearch.WordTrace tailWord_5298395 prefixEnd_5298395 2720623332378902738895631 := by
  unfold tailWord_5298395
  simp only [CollatzResearch.WordTrace]
  refine ⟨193248341639827283668832639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128832227759884855779221759 193248341639827283668832639)
  ·
    refine ⟨289872512459740925503248959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193248341639827283668832639 289872512459740925503248959)
    ·
      refine ⟨434808768689611388254873439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289872512459740925503248959 434808768689611388254873439)
      ·
        refine ⟨652213153034417082382310159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 434808768689611388254873439 652213153034417082382310159)
        ·
          refine ⟨978319729551625623573465239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 652213153034417082382310159 978319729551625623573465239)
          ·
            refine ⟨1467479594327438435360197859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 978319729551625623573465239 1467479594327438435360197859)
            ·
              refine ⟨2201219391491157653040296789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1467479594327438435360197859 2201219391491157653040296789)
              ·
                refine ⟨12897769872018501873282989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2201219391491157653040296789 12897769872018501873282989)
                ·
                  refine ⟨4836663702006938202481121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12897769872018501873282989 4836663702006938202481121)
                  ·
                    refine ⟨3627497776505203651860841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4836663702006938202481121 3627497776505203651860841)
                    ·
                      refine ⟨2720623332378902738895631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3627497776505203651860841 2720623332378902738895631)
                      ·
                        rfl

theorem cell23_5298395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9, 3, 2, 2].length) (baseStart_5298395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5298395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5298395 prefixEnd_5298395 := by exact prefixLift 5298395
  have htrace : WordTrace (prefixWord ++ tailWord_5298395) baseStart_5298395 baseEnd_5298395 := by
    simpa [prefixWord, tailWord_5298395, baseEnd_5298395] using wordTrace_append hprefix tailTrace_5298395
  have hstable : (prefixWord ++ tailWord_5298395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5298395).length < 2 ^ (prefixWord ++ tailWord_5298395).sum := by decide
  have hdescent : baseEnd_5298395 < baseStart_5298395 := by decide
  rcases family_descends (prefixWord ++ tailWord_5298395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5298401 : List Nat := [1, 2, 3, 1, 3, 1, 2, 10]
def baseStart_5298401 : Nat := 118140960795 + 5298401 * 2 ^ 59
def prefixEnd_5298401 : Nat := 4983230072969 + 3 ^ 40 * 5298401 * 2
def baseEnd_5298401 : Nat := 100763941231956656126689

theorem tailTrace_5298401 : CollatzResearch.WordTrace tailWord_5298401 prefixEnd_5298401 100763941231956656126689 := by
  unfold tailWord_5298401
  simp only [CollatzResearch.WordTrace]
  refine ⟨193248560477805546693551057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128832373651870364462367371 193248560477805546693551057)
  ·
    refine ⟨144936420358354160020163293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193248560477805546693551057 144936420358354160020163293)
    ·
      refine ⟨54351157634382810007561235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144936420358354160020163293 54351157634382810007561235)
      ·
        refine ⟨81526736451574215011341853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54351157634382810007561235 81526736451574215011341853)
        ·
          refine ⟨30572526169340330629253195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81526736451574215011341853 30572526169340330629253195)
          ·
            refine ⟨45858789254010495943879793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30572526169340330629253195 45858789254010495943879793)
            ·
              refine ⟨34394091940507871957909845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45858789254010495943879793 34394091940507871957909845)
              ·
                refine ⟨100763941231956656126689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 34394091940507871957909845 100763941231956656126689)
                ·
                  rfl

theorem cell23_5298401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 10].length) (baseStart_5298401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5298401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5298401 prefixEnd_5298401 := by exact prefixLift 5298401
  have htrace : WordTrace (prefixWord ++ tailWord_5298401) baseStart_5298401 baseEnd_5298401 := by
    simpa [prefixWord, tailWord_5298401, baseEnd_5298401] using wordTrace_append hprefix tailTrace_5298401
  have hstable : (prefixWord ++ tailWord_5298401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5298401).length < 2 ^ (prefixWord ++ tailWord_5298401).sum := by decide
  have hdescent : baseEnd_5298401 < baseStart_5298401 := by decide
  rcases family_descends (prefixWord ++ tailWord_5298401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5298405 : List Nat := [1, 3, 1, 4, 2, 3, 1, 1, 1, 6]
def baseStart_5298405 : Nat := 118140960795 + 5298405 * 2 ^ 59
def prefixEnd_5298405 : Nat := 4983230072969 + 3 ^ 40 * 5298405 * 2
def baseEnd_5298405 : Nat := 906876155728482566590195

theorem tailTrace_5298405 : CollatzResearch.WordTrace tailWord_5298405 prefixEnd_5298405 906876155728482566590195 := by
  unfold tailWord_5298405
  simp only [CollatzResearch.WordTrace]
  refine ⟨193248706369791055376696669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128832470913194036917797779 193248706369791055376696669)
  ·
    refine ⟨72468264888671645766261251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 193248706369791055376696669 72468264888671645766261251)
    ·
      refine ⟨108702397333007468649391877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72468264888671645766261251 108702397333007468649391877)
      ·
        refine ⟨20381699499938900371760977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 108702397333007468649391877 20381699499938900371760977)
        ·
          refine ⟨15286274624954175278820733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20381699499938900371760977 15286274624954175278820733)
          ·
            refine ⟨5732352984357815729557775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15286274624954175278820733 5732352984357815729557775)
            ·
              refine ⟨8598529476536723594336663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5732352984357815729557775 8598529476536723594336663)
              ·
                refine ⟨12897794214805085391504995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8598529476536723594336663 12897794214805085391504995)
                ·
                  refine ⟨19346691322207628087257493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12897794214805085391504995 19346691322207628087257493)
                  ·
                    refine ⟨906876155728482566590195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19346691322207628087257493 906876155728482566590195)
                    ·
                      rfl

theorem cell23_5298405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 1, 1, 6].length) (baseStart_5298405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5298405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5298405 prefixEnd_5298405 := by exact prefixLift 5298405
  have htrace : WordTrace (prefixWord ++ tailWord_5298405) baseStart_5298405 baseEnd_5298405 := by
    simpa [prefixWord, tailWord_5298405, baseEnd_5298405] using wordTrace_append hprefix tailTrace_5298405
  have hstable : (prefixWord ++ tailWord_5298405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5298405).length < 2 ^ (prefixWord ++ tailWord_5298405).sum := by decide
  have hdescent : baseEnd_5298405 < baseStart_5298405 := by decide
  rcases family_descends (prefixWord ++ tailWord_5298405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5298408 : List Nat := [2, 1, 4, 1, 2, 3, 1, 1, 1, 1, 6]
def baseStart_5298408 : Nat := 118140960795 + 5298408 * 2 ^ 59
def prefixEnd_5298408 : Nat := 4983230072969 + 3 ^ 40 * 5298408 * 2
def baseEnd_5298408 : Nat := 2720630007627411188033071

theorem tailTrace_5298408 : CollatzResearch.WordTrace tailWord_5298408 prefixEnd_5298408 2720630007627411188033071 := by
  unfold tailWord_5298408
  simp only [CollatzResearch.WordTrace]
  refine ⟨96624407894390093444527939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128832543859186791259370585 96624407894390093444527939)
  ·
    refine ⟨144936611841585140166791909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96624407894390093444527939 144936611841585140166791909)
    ·
      refine ⟨27175614720297213781273483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 144936611841585140166791909 27175614720297213781273483)
      ·
        refine ⟨40763422080445820671910225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27175614720297213781273483 40763422080445820671910225)
        ·
          refine ⟨30572566560334365503932669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40763422080445820671910225 30572566560334365503932669)
          ·
            refine ⟨11464712460125387063974751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30572566560334365503932669 11464712460125387063974751)
            ·
              refine ⟨17197068690188080595962127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11464712460125387063974751 17197068690188080595962127)
              ·
                refine ⟨25795603035282120893943191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17197068690188080595962127 25795603035282120893943191)
                ·
                  refine ⟨38693404552923181340914787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25795603035282120893943191 38693404552923181340914787)
                  ·
                    refine ⟨58040106829384772011372181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38693404552923181340914787 58040106829384772011372181)
                    ·
                      refine ⟨2720630007627411188033071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58040106829384772011372181 2720630007627411188033071)
                      ·
                        rfl

theorem cell23_5298408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 1, 1, 1, 6].length) (baseStart_5298408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5298408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5298408 prefixEnd_5298408 := by exact prefixLift 5298408
  have htrace : WordTrace (prefixWord ++ tailWord_5298408) baseStart_5298408 baseEnd_5298408 := by
    simpa [prefixWord, tailWord_5298408, baseEnd_5298408] using wordTrace_append hprefix tailTrace_5298408
  have hstable : (prefixWord ++ tailWord_5298408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5298408).length < 2 ^ (prefixWord ++ tailWord_5298408).sum := by decide
  have hdescent : baseEnd_5298408 < baseStart_5298408 := by decide
  rcases family_descends (prefixWord ++ tailWord_5298408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5298415 : List Nat := [1, 1, 2, 1, 6, 1, 1, 4, 1, 2, 3]
def baseStart_5298415 : Nat := 118140960795 + 5298415 * 2 ^ 59
def prefixEnd_5298415 : Nat := 4983230072969 + 3 ^ 40 * 5298415 * 2
def baseEnd_5298415 : Nat := 2720633601991992660645539

theorem tailTrace_5298415 : CollatzResearch.WordTrace tailWord_5298415 prefixEnd_5298415 2720633601991992660645539 := by
  unfold tailWord_5298415
  simp only [CollatzResearch.WordTrace]
  refine ⟨193249071099754827084560699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128832714066503218056373799 193249071099754827084560699)
  ·
    refine ⟨289873606649632240626841049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193249071099754827084560699 289873606649632240626841049)
    ·
      refine ⟨217405204987224180470130787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 289873606649632240626841049 217405204987224180470130787)
      ·
        refine ⟨326107807480836270705196181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217405204987224180470130787 326107807480836270705196181)
        ·
          refine ⟨15286303475664200189306071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 326107807480836270705196181 15286303475664200189306071)
          ·
            refine ⟨22929455213496300283959107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15286303475664200189306071 22929455213496300283959107)
            ·
              refine ⟨34394182820244450425938661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22929455213496300283959107 34394182820244450425938661)
              ·
                refine ⟨6448909278795834454863499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34394182820244450425938661 6448909278795834454863499)
                ·
                  refine ⟨9673363918193751682295249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6448909278795834454863499 9673363918193751682295249)
                  ·
                    refine ⟨7255022938645313761721437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9673363918193751682295249 7255022938645313761721437)
                    ·
                      refine ⟨2720633601991992660645539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7255022938645313761721437 2720633601991992660645539)
                      ·
                        rfl

theorem cell23_5298415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 4, 1, 2, 3].length) (baseStart_5298415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5298415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5298415 prefixEnd_5298415 := by exact prefixLift 5298415
  have htrace : WordTrace (prefixWord ++ tailWord_5298415) baseStart_5298415 baseEnd_5298415 := by
    simpa [prefixWord, tailWord_5298415, baseEnd_5298415] using wordTrace_append hprefix tailTrace_5298415
  have hstable : (prefixWord ++ tailWord_5298415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5298415).length < 2 ^ (prefixWord ++ tailWord_5298415).sum := by decide
  have hdescent : baseEnd_5298415 < baseStart_5298415 := by decide
  rcases family_descends (prefixWord ++ tailWord_5298415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5298418 : List Nat := [3, 2, 1, 3, 2, 2, 1, 9]
def baseStart_5298418 : Nat := 118140960795 + 5298418 * 2 ^ 59
def prefixEnd_5298418 : Nat := 4983230072969 + 3 ^ 40 * 5298418 * 2
def baseEnd_5298418 : Nat := 100764264534590968478075

theorem tailTrace_5298418 : CollatzResearch.WordTrace tailWord_5298418 prefixEnd_5298418 100764264534590968478075 := by
  unfold tailWord_5298418
  simp only [CollatzResearch.WordTrace]
  refine ⟨48312295129685989649229977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128832787012495972397946605 48312295129685989649229977)
  ·
    refine ⟨36234221347264492236922483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48312295129685989649229977 36234221347264492236922483)
    ·
      refine ⟨54351332020896738355383725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36234221347264492236922483 54351332020896738355383725)
      ·
        refine ⟨20381749507836276883268897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54351332020896738355383725 20381749507836276883268897)
        ·
          refine ⟨15286312130877207662451673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20381749507836276883268897 15286312130877207662451673)
          ·
            refine ⟨11464734098157905746838755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15286312130877207662451673 11464734098157905746838755)
            ·
              refine ⟨17197101147236858620258133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11464734098157905746838755 17197101147236858620258133)
              ·
                refine ⟨100764264534590968478075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17197101147236858620258133 100764264534590968478075)
                ·
                  rfl

theorem cell23_5298418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 9].length) (baseStart_5298418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5298418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5298418 prefixEnd_5298418 := by exact prefixLift 5298418
  have htrace : WordTrace (prefixWord ++ tailWord_5298418) baseStart_5298418 baseEnd_5298418 := by
    simpa [prefixWord, tailWord_5298418, baseEnd_5298418] using wordTrace_append hprefix tailTrace_5298418
  have hstable : (prefixWord ++ tailWord_5298418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5298418).length < 2 ^ (prefixWord ++ tailWord_5298418).sum := by decide
  have hdescent : baseEnd_5298418 < baseStart_5298418 := by decide
  rcases family_descends (prefixWord ++ tailWord_5298418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5298446 : List Nat := [4, 1, 1, 2, 1, 2, 5, 2, 1, 2, 2]
def baseStart_5298446 : Nat := 118140960795 + 5298446 * 2 ^ 59
def prefixEnd_5298446 : Nat := 4983230072969 + 3 ^ 40 * 5298446 * 2
def baseEnd_5298446 : Nat := 2720649519892282039357897

theorem tailTrace_5298446 : CollatzResearch.WordTrace tailWord_5298446 prefixEnd_5298446 2720649519892282039357897 := by
  unfold tailWord_5298446
  simp only [CollatzResearch.WordTrace]
  refine ⟨24156275220330314922367399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128833467841761679585959461 24156275220330314922367399)
  ·
    refine ⟨36234412830495472383551099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24156275220330314922367399 36234412830495472383551099)
    ·
      refine ⟨54351619245743208575326649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36234412830495472383551099 54351619245743208575326649)
      ·
        refine ⟨40763714434307406431494987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54351619245743208575326649 40763714434307406431494987)
        ·
          refine ⟨61145571651461109647242481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40763714434307406431494987 61145571651461109647242481)
          ·
            refine ⟨45859178738595832235431861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61145571651461109647242481 45859178738595832235431861)
            ·
              refine ⟨4299298006743359272071737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45859178738595832235431861 4299298006743359272071737)
              ·
                refine ⟨3224473505057519454053803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4299298006743359272071737 3224473505057519454053803)
                ·
                  refine ⟨4836710257586279181080705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3224473505057519454053803 4836710257586279181080705)
                  ·
                    refine ⟨3627532693189709385810529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4836710257586279181080705 3627532693189709385810529)
                    ·
                      refine ⟨2720649519892282039357897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3627532693189709385810529 2720649519892282039357897)
                      ·
                        rfl

theorem cell23_5298446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 5, 2, 1, 2, 2].length) (baseStart_5298446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5298446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5298446 prefixEnd_5298446 := by exact prefixLift 5298446
  have htrace : WordTrace (prefixWord ++ tailWord_5298446) baseStart_5298446 baseEnd_5298446 := by
    simpa [prefixWord, tailWord_5298446, baseEnd_5298446] using wordTrace_append hprefix tailTrace_5298446
  have hstable : (prefixWord ++ tailWord_5298446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5298446).length < 2 ^ (prefixWord ++ tailWord_5298446).sum := by decide
  have hdescent : baseEnd_5298446 < baseStart_5298446 := by decide
  rcases family_descends (prefixWord ++ tailWord_5298446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5298488 : List Nat := [2, 1, 2, 1, 3, 1, 4, 1, 2, 1, 5]
def baseStart_5298488 : Nat := 118140960795 + 5298488 * 2 ^ 59
def prefixEnd_5298488 : Nat := 4983230072969 + 3 ^ 40 * 5298488 * 2
def baseEnd_5298488 : Nat := 2720671086079770875032703

theorem tailTrace_5298488 : CollatzResearch.WordTrace tailWord_5298488 prefixEnd_5298488 2720671086079770875032703 := by
  unfold tailWord_5298488
  simp only [CollatzResearch.WordTrace]
  refine ⟨96625866814245180275984059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128834489085660240367978745 96625866814245180275984059)
  ·
    refine ⟨144938800221367770413976089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96625866814245180275984059 144938800221367770413976089)
    ·
      refine ⟨108704100166025827810482067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144938800221367770413976089 108704100166025827810482067)
      ·
        refine ⟨163056150249038741715723101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108704100166025827810482067 163056150249038741715723101)
        ·
          refine ⟨61146056343389528143396163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 163056150249038741715723101 61146056343389528143396163)
          ·
            refine ⟨91719084515084292215094245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61146056343389528143396163 91719084515084292215094245)
            ·
              refine ⟨17197328346578304790330171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91719084515084292215094245 17197328346578304790330171)
              ·
                refine ⟨25795992519867457185495257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17197328346578304790330171 25795992519867457185495257)
                ·
                  refine ⟨19346994389900592889121443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25795992519867457185495257 19346994389900592889121443)
                  ·
                    refine ⟨29020491584850889333682165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19346994389900592889121443 29020491584850889333682165)
                    ·
                      refine ⟨2720671086079770875032703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29020491584850889333682165 2720671086079770875032703)
                      ·
                        rfl

theorem cell23_5298488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 1, 2, 1, 5].length) (baseStart_5298488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5298488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5298488 prefixEnd_5298488 := by exact prefixLift 5298488
  have htrace : WordTrace (prefixWord ++ tailWord_5298488) baseStart_5298488 baseEnd_5298488 := by
    simpa [prefixWord, tailWord_5298488, baseEnd_5298488] using wordTrace_append hprefix tailTrace_5298488
  have hstable : (prefixWord ++ tailWord_5298488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5298488).length < 2 ^ (prefixWord ++ tailWord_5298488).sum := by decide
  have hdescent : baseEnd_5298488 < baseStart_5298488 := by decide
  rcases family_descends (prefixWord ++ tailWord_5298488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5298508 : List Nat := [2, 2, 1, 3, 2, 1, 2, 3, 7]
def baseStart_5298508 : Nat := 118140960795 + 5298508 * 2 ^ 59
def prefixEnd_5298508 : Nat := 4983230072969 + 3 ^ 40 * 5298508 * 2
def baseEnd_5298508 : Nat := 302297928410317866309179

theorem tailTrace_5298508 : CollatzResearch.WordTrace tailWord_5298508 prefixEnd_5298508 302297928410317866309179 := by
  unfold tailWord_5298508
  simp only [CollatzResearch.WordTrace]
  refine ⟨96626231544208951983848089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128834975392278602645130785 96626231544208951983848089)
  ·
    refine ⟨72469673658156713987886067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96626231544208951983848089 72469673658156713987886067)
    ·
      refine ⟨108704510487235070981829101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72469673658156713987886067 108704510487235070981829101)
      ·
        refine ⟨40764191432713151618185913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108704510487235070981829101 40764191432713151618185913)
        ·
          refine ⟨30573143574534863713639435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40764191432713151618185913 30573143574534863713639435)
          ·
            refine ⟨45859715361802295570459153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30573143574534863713639435 45859715361802295570459153)
            ·
              refine ⟨34394786521351721677844365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45859715361802295570459153 34394786521351721677844365)
              ·
                refine ⟨12898044945506895629191637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34394786521351721677844365 12898044945506895629191637)
                ·
                  refine ⟨302297928410317866309179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12898044945506895629191637 302297928410317866309179)
                  ·
                    rfl

theorem cell23_5298508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 3, 7].length) (baseStart_5298508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5298508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5298508 prefixEnd_5298508 := by exact prefixLift 5298508
  have htrace : WordTrace (prefixWord ++ tailWord_5298508) baseStart_5298508 baseEnd_5298508 := by
    simpa [prefixWord, tailWord_5298508, baseEnd_5298508] using wordTrace_append hprefix tailTrace_5298508
  have hstable : (prefixWord ++ tailWord_5298508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5298508).length < 2 ^ (prefixWord ++ tailWord_5298508).sum := by decide
  have hdescent : baseEnd_5298508 < baseStart_5298508 := by decide
  rcases family_descends (prefixWord ++ tailWord_5298508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5298585 : List Nat := [1, 2, 1, 2, 1, 4, 1, 4, 3, 4]
def baseStart_5298585 : Nat := 118140960795 + 5298585 * 2 ^ 59
def prefixEnd_5298585 : Nat := 4983230072969 + 3 ^ 40 * 5298585 * 2
def baseEnd_5298585 : Nat := 906906964567752331839919

theorem tailTrace_5298585 : CollatzResearch.WordTrace tailWord_5298585 prefixEnd_5298585 906906964567752331839919 := by
  unfold tailWord_5298585
  simp only [CollatzResearch.WordTrace]
  refine ⟨193255271509138946118249209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128836847672759297412166139 193255271509138946118249209)
  ·
    refine ⟨144941453631854209588686907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193255271509138946118249209 144941453631854209588686907)
    ·
      refine ⟨217412180447781314383030361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144941453631854209588686907 217412180447781314383030361)
      ·
        refine ⟨163059135335835985787272771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 217412180447781314383030361 163059135335835985787272771)
        ·
          refine ⟨244588703003753978680909157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163059135335835985787272771 244588703003753978680909157)
          ·
            refine ⟨45860381813203871002670467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 244588703003753978680909157 45860381813203871002670467)
            ·
              refine ⟨68790572719805806504005701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45860381813203871002670467 68790572719805806504005701)
              ·
                refine ⟨12898232384963588719501069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68790572719805806504005701 12898232384963588719501069)
                ·
                  refine ⟨4836837144361345769812901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12898232384963588719501069 4836837144361345769812901)
                  ·
                    refine ⟨906906964567752331839919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4836837144361345769812901 906906964567752331839919)
                    ·
                      rfl

theorem cell23_5298585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 4, 3, 4].length) (baseStart_5298585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5298585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5298585 prefixEnd_5298585 := by exact prefixLift 5298585
  have htrace : WordTrace (prefixWord ++ tailWord_5298585) baseStart_5298585 baseEnd_5298585 := by
    simpa [prefixWord, tailWord_5298585, baseEnd_5298585] using wordTrace_append hprefix tailTrace_5298585
  have hstable : (prefixWord ++ tailWord_5298585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5298585).length < 2 ^ (prefixWord ++ tailWord_5298585).sum := by decide
  have hdescent : baseEnd_5298585 < baseStart_5298585 := by decide
  rcases family_descends (prefixWord ++ tailWord_5298585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5298595 : List Nat := [1, 1, 1, 4, 1, 4, 2, 1, 1, 4, 3]
def baseStart_5298595 : Nat := 118140960795 + 5298595 * 2 ^ 59
def prefixEnd_5298595 : Nat := 4983230072969 + 3 ^ 40 * 5298595 * 2
def baseEnd_5298595 : Nat := 2720726028509801956394711

theorem tailTrace_5298595 : CollatzResearch.WordTrace tailWord_5298595 prefixEnd_5298595 2720726028509801956394711 := by
  unfold tailWord_5298595
  simp only [CollatzResearch.WordTrace]
  refine ⟨193255636239102717826113239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128837090826068478550742159 193255636239102717826113239)
  ·
    refine ⟨289883454358654076739169859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193255636239102717826113239 289883454358654076739169859)
    ·
      refine ⟨434825181537981115108754789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289883454358654076739169859 434825181537981115108754789)
      ·
        refine ⟨81529721538371459082891523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 434825181537981115108754789 81529721538371459082891523)
        ·
          refine ⟨122294582307557188624337285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81529721538371459082891523 122294582307557188624337285)
          ·
            refine ⟨22930234182666972867063241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 122294582307557188624337285 22930234182666972867063241)
            ·
              refine ⟨17197675637000229650297431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22930234182666972867063241 17197675637000229650297431)
              ·
                refine ⟨25796513455500344475446147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17197675637000229650297431 25796513455500344475446147)
                ·
                  refine ⟨38694770183250516713169221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25796513455500344475446147 38694770183250516713169221)
                  ·
                    refine ⟨7255269409359471883719229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38694770183250516713169221 7255269409359471883719229)
                    ·
                      refine ⟨2720726028509801956394711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7255269409359471883719229 2720726028509801956394711)
                      ·
                        rfl

theorem cell23_5298595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 1, 1, 4, 3].length) (baseStart_5298595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5298595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5298595 prefixEnd_5298595 := by exact prefixLift 5298595
  have htrace : WordTrace (prefixWord ++ tailWord_5298595) baseStart_5298595 baseEnd_5298595 := by
    simpa [prefixWord, tailWord_5298595, baseEnd_5298595] using wordTrace_append hprefix tailTrace_5298595
  have hstable : (prefixWord ++ tailWord_5298595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5298595).length < 2 ^ (prefixWord ++ tailWord_5298595).sum := by decide
  have hdescent : baseEnd_5298595 < baseStart_5298595 := by decide
  rcases family_descends (prefixWord ++ tailWord_5298595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5298618 : List Nat := [3, 1, 1, 1, 2, 1, 1, 3, 1, 1, 8]
def baseStart_5298618 : Nat := 118140960795 + 5298618 * 2 ^ 59
def prefixEnd_5298618 : Nat := 4983230072969 + 3 ^ 40 * 5298618 * 2
def baseEnd_5298618 : Nat := 2720737838564855366407105

theorem tailTrace_5298618 : CollatzResearch.WordTrace tailWord_5298618 prefixEnd_5298618 2720737838564855366407105 := by
  unfold tailWord_5298618
  simp only [CollatzResearch.WordTrace]
  refine ⟨48314118779504848188550127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128837650078679595169467005 48314118779504848188550127)
  ·
    refine ⟨72471178169257272282825191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48314118779504848188550127 72471178169257272282825191)
    ·
      refine ⟨108706767253885908424237787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72471178169257272282825191 108706767253885908424237787)
      ·
        refine ⟨163060150880828862636356681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108706767253885908424237787 163060150880828862636356681)
        ·
          refine ⟨122295113160621646977267511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163060150880828862636356681 122295113160621646977267511)
          ·
            refine ⟨183442669740932470465901267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122295113160621646977267511 183442669740932470465901267)
            ·
              refine ⟨275164004611398705698851901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 183442669740932470465901267 275164004611398705698851901)
              ·
                refine ⟨103186501729274514637069463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 275164004611398705698851901 103186501729274514637069463)
                ·
                  refine ⟨154779752593911771955604195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 103186501729274514637069463 154779752593911771955604195)
                  ·
                    refine ⟨232169628890867657933406293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 154779752593911771955604195 232169628890867657933406293)
                    ·
                      refine ⟨2720737838564855366407105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 232169628890867657933406293 2720737838564855366407105)
                      ·
                        rfl

theorem cell23_5298618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 1, 1, 8].length) (baseStart_5298618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5298618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5298618 prefixEnd_5298618 := by exact prefixLift 5298618
  have htrace : WordTrace (prefixWord ++ tailWord_5298618) baseStart_5298618 baseEnd_5298618 := by
    simpa [prefixWord, tailWord_5298618, baseEnd_5298618] using wordTrace_append hprefix tailTrace_5298618
  have hstable : (prefixWord ++ tailWord_5298618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5298618).length < 2 ^ (prefixWord ++ tailWord_5298618).sum := by decide
  have hdescent : baseEnd_5298618 < baseStart_5298618 := by decide
  rcases family_descends (prefixWord ++ tailWord_5298618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5298632 : List Nat := [2, 1, 3, 1, 3, 2, 4, 1, 6]
def baseStart_5298632 : Nat := 118140960795 + 5298632 * 2 ^ 59
def prefixEnd_5298632 : Nat := 4983230072969 + 3 ^ 40 * 5298632 * 2
def baseEnd_5298632 : Nat := 302305003032668701292449

theorem tailTrace_5298632 : CollatzResearch.WordTrace tailWord_5298632 prefixEnd_5298632 302305003032668701292449 := by
  unfold tailWord_5298632
  simp only [CollatzResearch.WordTrace]
  refine ⟨96628492869984336572605075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128837990493312448763473433 96628492869984336572605075)
  ·
    refine ⟨144942739304976504858907613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96628492869984336572605075 144942739304976504858907613)
    ·
      refine ⟨54353527239366189322090355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144942739304976504858907613 54353527239366189322090355)
      ·
        refine ⟨81530290859049283983135533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54353527239366189322090355 81530290859049283983135533)
        ·
          refine ⟨30573859072143481493675825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81530290859049283983135533 30573859072143481493675825)
          ·
            refine ⟨22930394304107611120256869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30573859072143481493675825 22930394304107611120256869)
            ·
              refine ⟨4299448932020177085048163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22930394304107611120256869 4299448932020177085048163)
              ·
                refine ⟨6449173398030265627572245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4299448932020177085048163 6449173398030265627572245)
                ·
                  refine ⟨302305003032668701292449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6449173398030265627572245 302305003032668701292449)
                  ·
                    rfl

theorem cell23_5298632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 4, 1, 6].length) (baseStart_5298632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5298632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5298632 prefixEnd_5298632 := by exact prefixLift 5298632
  have htrace : WordTrace (prefixWord ++ tailWord_5298632) baseStart_5298632 baseEnd_5298632 := by
    simpa [prefixWord, tailWord_5298632, baseEnd_5298632] using wordTrace_append hprefix tailTrace_5298632
  have hstable : (prefixWord ++ tailWord_5298632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5298632).length < 2 ^ (prefixWord ++ tailWord_5298632).sum := by decide
  have hdescent : baseEnd_5298632 < baseStart_5298632 := by decide
  rcases family_descends (prefixWord ++ tailWord_5298632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5298685 : List Nat := [1, 4, 1, 1, 1, 3, 2, 1, 3, 1, 5]
def baseStart_5298685 : Nat := 118140960795 + 5298685 * 2 ^ 59
def prefixEnd_5298685 : Nat := 4983230072969 + 3 ^ 40 * 5298685 * 2
def baseEnd_5298685 : Nat := 2720772241768706604269297

theorem tailTrace_5298685 : CollatzResearch.WordTrace tailWord_5298685 prefixEnd_5298685 2720772241768706604269297 := by
  unfold tailWord_5298685
  simp only [CollatzResearch.WordTrace]
  refine ⟨193258918808776663196889509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128839279205851108797926339 193258918808776663196889509)
  ·
    refine ⟨36236047276645624349416783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 193258918808776663196889509 36236047276645624349416783)
    ·
      refine ⟨54354070914968436524125175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36236047276645624349416783 54354070914968436524125175)
      ·
        refine ⟨81531106372452654786187763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54354070914968436524125175 81531106372452654786187763)
        ·
          refine ⟨122296659558678982179281645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81531106372452654786187763 122296659558678982179281645)
          ·
            refine ⟨45861247334504618317230617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 122296659558678982179281645 45861247334504618317230617)
            ·
              refine ⟨34395935500878463737922963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45861247334504618317230617 34395935500878463737922963)
              ·
                refine ⟨51593903251317695606884445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34395935500878463737922963 51593903251317695606884445)
                ·
                  refine ⟨19347713719244135852581667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51593903251317695606884445 19347713719244135852581667)
                  ·
                    refine ⟨29021570578866203778872501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19347713719244135852581667 29021570578866203778872501)
                    ·
                      refine ⟨2720772241768706604269297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29021570578866203778872501 2720772241768706604269297)
                      ·
                        rfl

theorem cell23_5298685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 3, 1, 5].length) (baseStart_5298685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5298685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5298685 prefixEnd_5298685 := by exact prefixLift 5298685
  have htrace : WordTrace (prefixWord ++ tailWord_5298685) baseStart_5298685 baseEnd_5298685 := by
    simpa [prefixWord, tailWord_5298685, baseEnd_5298685] using wordTrace_append hprefix tailTrace_5298685
  have hstable : (prefixWord ++ tailWord_5298685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5298685).length < 2 ^ (prefixWord ++ tailWord_5298685).sum := by decide
  have hdescent : baseEnd_5298685 < baseStart_5298685 := by decide
  rcases family_descends (prefixWord ++ tailWord_5298685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5298692 : List Nat := [2, 3, 2, 3, 1, 1, 1, 3, 1, 6]
def baseStart_5298692 : Nat := 118140960795 + 5298692 * 2 ^ 59
def prefixEnd_5298692 : Nat := 4983230072969 + 3 ^ 40 * 5298692 * 2
def baseEnd_5298692 : Nat := 906925278711096025627255

theorem tailTrace_5298692 : CollatzResearch.WordTrace tailWord_5298692 prefixEnd_5298692 906925278711096025627255 := by
  unfold tailWord_5298692
  simp only [CollatzResearch.WordTrace]
  refine ⟨96629587059875651696197165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128839449413167535594929553 96629587059875651696197165)
  ·
    refine ⟨36236095147453369386073937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96629587059875651696197165 36236095147453369386073937)
    ·
      refine ⟨27177071360590027039555453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36236095147453369386073937 27177071360590027039555453)
      ·
        refine ⟨10191401760221260139833295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27177071360590027039555453 10191401760221260139833295)
        ·
          refine ⟨15287102640331890209749943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10191401760221260139833295 15287102640331890209749943)
          ·
            refine ⟨22930653960497835314624915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15287102640331890209749943 22930653960497835314624915)
            ·
              refine ⟨34395980940746752971937373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22930653960497835314624915 34395980940746752971937373)
              ·
                refine ⟨12898492852780032364476515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34395980940746752971937373 12898492852780032364476515)
                ·
                  refine ⟨19347739279170048546714773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12898492852780032364476515 19347739279170048546714773)
                  ·
                    refine ⟨906925278711096025627255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19347739279170048546714773 906925278711096025627255)
                    ·
                      rfl

theorem cell23_5298692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 3, 1, 6].length) (baseStart_5298692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5298692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5298692 prefixEnd_5298692 := by exact prefixLift 5298692
  have htrace : WordTrace (prefixWord ++ tailWord_5298692) baseStart_5298692 baseEnd_5298692 := by
    simpa [prefixWord, tailWord_5298692, baseEnd_5298692] using wordTrace_append hprefix tailTrace_5298692
  have hstable : (prefixWord ++ tailWord_5298692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5298692).length < 2 ^ (prefixWord ++ tailWord_5298692).sum := by decide
  have hdescent : baseEnd_5298692 < baseStart_5298692 := by decide
  rcases family_descends (prefixWord ++ tailWord_5298692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5298699 : List Nat := [1, 1, 1, 1, 7, 1, 1, 1, 5, 2, 2]
def baseStart_5298699 : Nat := 118140960795 + 5298699 * 2 ^ 59
def prefixEnd_5298699 : Nat := 4983230072969 + 3 ^ 40 * 5298699 * 2
def baseEnd_5298699 : Nat := 2720779430497869549494233

theorem tailTrace_5298699 : CollatzResearch.WordTrace tailWord_5298699 prefixEnd_5298699 2720779430497869549494233 := by
  unfold tailWord_5298699
  simp only [CollatzResearch.WordTrace]
  refine ⟨193259429430725943587899151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128839619620483962391932767 193259429430725943587899151)
  ·
    refine ⟨289889144146088915381848727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193259429430725943587899151 289889144146088915381848727)
    ·
      refine ⟨434833716219133373072773091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289889144146088915381848727 434833716219133373072773091)
      ·
        refine ⟨652250574328700059609159637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 434833716219133373072773091 652250574328700059609159637)
        ·
          refine ⟨15287122835828907647089679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 652250574328700059609159637 15287122835828907647089679)
          ·
            refine ⟨22930684253743361470634519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15287122835828907647089679 22930684253743361470634519)
            ·
              refine ⟨34396026380615042205951779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22930684253743361470634519 34396026380615042205951779)
              ·
                refine ⟨51594039570922563308927669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34396026380615042205951779 51594039570922563308927669)
                ·
                  refine ⟨4836941209773990310211969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51594039570922563308927669 4836941209773990310211969)
                  ·
                    refine ⟨3627705907330492732658977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4836941209773990310211969 3627705907330492732658977)
                    ·
                      refine ⟨2720779430497869549494233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3627705907330492732658977 2720779430497869549494233)
                      ·
                        rfl

theorem cell23_5298699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 5, 2, 2].length) (baseStart_5298699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5298699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5298699 prefixEnd_5298699 := by exact prefixLift 5298699
  have htrace : WordTrace (prefixWord ++ tailWord_5298699) baseStart_5298699 baseEnd_5298699 := by
    simpa [prefixWord, tailWord_5298699, baseEnd_5298699] using wordTrace_append hprefix tailTrace_5298699
  have hstable : (prefixWord ++ tailWord_5298699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5298699).length < 2 ^ (prefixWord ++ tailWord_5298699).sum := by decide
  have hdescent : baseEnd_5298699 < baseStart_5298699 := by decide
  rcases family_descends (prefixWord ++ tailWord_5298699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5298712 : List Nat := [2, 1, 2, 3, 3, 1, 2, 2, 1, 2, 4]
def baseStart_5298712 : Nat := 118140960795 + 5298712 * 2 ^ 59
def prefixEnd_5298712 : Nat := 4983230072969 + 3 ^ 40 * 5298712 * 2
def baseEnd_5298712 : Nat := 2720786105746377998631673

theorem tailTrace_5298712 : CollatzResearch.WordTrace tailWord_5298712 prefixEnd_5298712 2720786105746377998631673 := by
  unfold tailWord_5298712
  simp only [CollatzResearch.WordTrace]
  refine ⟨96629951789839423404061195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128839935719785897872081593 96629951789839423404061195)
  ·
    refine ⟨144944927684759135106091793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96629951789839423404061195 144944927684759135106091793)
    ·
      refine ⟨108708695763569351329568845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144944927684759135106091793 108708695763569351329568845)
      ·
        refine ⟨40765760911338506748588317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108708695763569351329568845 40765760911338506748588317)
        ·
          refine ⟨15287160341751940030720619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40765760911338506748588317 15287160341751940030720619)
          ·
            refine ⟨22930740512627910046080929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15287160341751940030720619 22930740512627910046080929)
            ·
              refine ⟨17198055384470932534560697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22930740512627910046080929 17198055384470932534560697)
              ·
                refine ⟨12898541538353199400920523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17198055384470932534560697 12898541538353199400920523)
                ·
                  refine ⟨19347812307529799101380785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12898541538353199400920523 19347812307529799101380785)
                  ·
                    refine ⟨14510859230647349326035589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19347812307529799101380785 14510859230647349326035589)
                    ·
                      refine ⟨2720786105746377998631673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14510859230647349326035589 2720786105746377998631673)
                      ·
                        rfl

theorem cell23_5298712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 2, 1, 2, 4].length) (baseStart_5298712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5298712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5298712 prefixEnd_5298712 := by exact prefixLift 5298712
  have htrace : WordTrace (prefixWord ++ tailWord_5298712) baseStart_5298712 baseEnd_5298712 := by
    simpa [prefixWord, tailWord_5298712, baseEnd_5298712] using wordTrace_append hprefix tailTrace_5298712
  have hstable : (prefixWord ++ tailWord_5298712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5298712).length < 2 ^ (prefixWord ++ tailWord_5298712).sum := by decide
  have hdescent : baseEnd_5298712 < baseStart_5298712 := by decide
  rcases family_descends (prefixWord ++ tailWord_5298712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5298716 : List Nat := [2, 2, 3, 1, 2, 4, 2, 1, 1, 1, 4]
def baseStart_5298716 : Nat := 118140960795 + 5298716 * 2 ^ 59
def prefixEnd_5298716 : Nat := 4983230072969 + 3 ^ 40 * 5298716 * 2
def baseEnd_5298716 : Nat := 2720788159668995982981655

theorem tailTrace_5298716 : CollatzResearch.WordTrace tailWord_5298716 prefixEnd_5298716 2720788159668995982981655 := by
  unfold tailWord_5298716
  simp only [CollatzResearch.WordTrace]
  refine ⟨96630024735832177745634001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128840032981109570327512001 96630024735832177745634001)
  ·
    refine ⟨72472518551874133309225501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96630024735832177745634001 72472518551874133309225501)
    ·
      refine ⟨27177194456952799990959563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72472518551874133309225501 27177194456952799990959563)
      ·
        refine ⟨40765791685429199986439345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27177194456952799990959563 40765791685429199986439345)
        ·
          refine ⟨30574343764071899989829509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40765791685429199986439345 30574343764071899989829509)
          ·
            refine ⟨5732689455763481248093033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30574343764071899989829509 5732689455763481248093033)
            ·
              refine ⟨4299517091822610936069775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5732689455763481248093033 4299517091822610936069775)
              ·
                refine ⟨6449275637733916404104663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4299517091822610936069775 6449275637733916404104663)
                ·
                  refine ⟨9673913456600874606156995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6449275637733916404104663 9673913456600874606156995)
                  ·
                    refine ⟨14510870184901311909235493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9673913456600874606156995 14510870184901311909235493)
                    ·
                      refine ⟨2720788159668995982981655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14510870184901311909235493 2720788159668995982981655)
                      ·
                        rfl

theorem cell23_5298716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 2, 1, 1, 1, 4].length) (baseStart_5298716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5298716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5298716 prefixEnd_5298716 := by exact prefixLift 5298716
  have htrace : WordTrace (prefixWord ++ tailWord_5298716) baseStart_5298716 baseEnd_5298716 := by
    simpa [prefixWord, tailWord_5298716, baseEnd_5298716] using wordTrace_append hprefix tailTrace_5298716
  have hstable : (prefixWord ++ tailWord_5298716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5298716).length < 2 ^ (prefixWord ++ tailWord_5298716).sum := by decide
  have hdescent : baseEnd_5298716 < baseStart_5298716 := by decide
  rcases family_descends (prefixWord ++ tailWord_5298716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5298749 : List Nat := [1, 4, 1, 3, 2, 1, 3, 1, 1, 3, 3]
def baseStart_5298749 : Nat := 118140960795 + 5298749 * 2 ^ 59
def prefixEnd_5298749 : Nat := 4983230072969 + 3 ^ 40 * 5298749 * 2
def baseEnd_5298749 : Nat := 2720805104530594353869003

theorem tailTrace_5298749 : CollatzResearch.WordTrace tailWord_5298749 prefixEnd_5298749 2720805104530594353869003 := by
  unfold tailWord_5298749
  simp only [CollatzResearch.WordTrace]
  refine ⟨193261253080544802127219301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128840835387029868084812867 193261253080544802127219301)
  ·
    refine ⟨36236484952602150398853619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 193261253080544802127219301 36236484952602150398853619)
    ·
      refine ⟨54354727428903225598280429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36236484952602150398853619 54354727428903225598280429)
      ·
        refine ⟨20383022785838709599355161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54354727428903225598280429 20383022785838709599355161)
        ·
          refine ⟨15287267089379032199516371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20383022785838709599355161 15287267089379032199516371)
          ·
            refine ⟨22930900634068548299274557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15287267089379032199516371 22930900634068548299274557)
            ·
              refine ⟨8599087737775705612227959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22930900634068548299274557 8599087737775705612227959)
              ·
                refine ⟨12898631606663558418341939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8599087737775705612227959 12898631606663558418341939)
                ·
                  refine ⟨19347947409995337627512909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12898631606663558418341939 19347947409995337627512909)
                  ·
                    refine ⟨7255480278748251610317341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19347947409995337627512909 7255480278748251610317341)
                    ·
                      refine ⟨2720805104530594353869003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7255480278748251610317341 2720805104530594353869003)
                      ·
                        rfl

theorem cell23_5298749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_5298749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5298749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5298749 prefixEnd_5298749 := by exact prefixLift 5298749
  have htrace : WordTrace (prefixWord ++ tailWord_5298749) baseStart_5298749 baseEnd_5298749 := by
    simpa [prefixWord, tailWord_5298749, baseEnd_5298749] using wordTrace_append hprefix tailTrace_5298749
  have hstable : (prefixWord ++ tailWord_5298749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5298749).length < 2 ^ (prefixWord ++ tailWord_5298749).sum := by decide
  have hdescent : baseEnd_5298749 < baseStart_5298749 := by decide
  rcases family_descends (prefixWord ++ tailWord_5298749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5298755 : List Nat := [1, 1, 1, 3, 1, 2, 1, 4, 2, 3, 4]
def baseStart_5298755 : Nat := 118140960795 + 5298755 * 2 ^ 59
def prefixEnd_5298755 : Nat := 4983230072969 + 3 ^ 40 * 5298755 * 2
def baseEnd_5298755 : Nat := 2720808185414521330393975

theorem tailTrace_5298755 : CollatzResearch.WordTrace tailWord_5298755 prefixEnd_5298755 2720808185414521330393975 := by
  unfold tailWord_5298755
  simp only [CollatzResearch.WordTrace]
  refine ⟨193261471918523065151937719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128840981279015376767958479 193261471918523065151937719)
  ·
    refine ⟨289892207877784597727906579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193261471918523065151937719 289892207877784597727906579)
    ·
      refine ⟨434838311816676896591859869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289892207877784597727906579 434838311816676896591859869)
      ·
        refine ⟨163064366931253836221947451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 434838311816676896591859869 163064366931253836221947451)
        ·
          refine ⟨244596550396880754332921177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163064366931253836221947451 244596550396880754332921177)
          ·
            refine ⟨183447412797660565749690883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 244596550396880754332921177 183447412797660565749690883)
            ·
              refine ⟨275171119196490848624536325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 183447412797660565749690883 275171119196490848624536325)
              ·
                refine ⟨51594584849342034117100561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 275171119196490848624536325 51594584849342034117100561)
                ·
                  refine ⟨38695938637006525587825421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51594584849342034117100561 38695938637006525587825421)
                  ·
                    refine ⟨14510976988877447095434533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38695938637006525587825421 14510976988877447095434533)
                    ·
                      refine ⟨2720808185414521330393975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14510976988877447095434533 2720808185414521330393975)
                      ·
                        rfl

theorem cell23_5298755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 2, 3, 4].length) (baseStart_5298755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5298755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5298755 prefixEnd_5298755 := by exact prefixLift 5298755
  have htrace : WordTrace (prefixWord ++ tailWord_5298755) baseStart_5298755 baseEnd_5298755 := by
    simpa [prefixWord, tailWord_5298755, baseEnd_5298755] using wordTrace_append hprefix tailTrace_5298755
  have hstable : (prefixWord ++ tailWord_5298755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5298755).length < 2 ^ (prefixWord ++ tailWord_5298755).sum := by decide
  have hdescent : baseEnd_5298755 < baseStart_5298755 := by decide
  rcases family_descends (prefixWord ++ tailWord_5298755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5298756 : List Nat := [2, 3, 5, 1, 1, 1, 1, 9]
def baseStart_5298756 : Nat := 118140960795 + 5298756 * 2 ^ 59
def prefixEnd_5298756 : Nat := 4983230072969 + 3 ^ 40 * 5298756 * 2
def baseEnd_5298756 : Nat := 100770692551673178758573

theorem tailTrace_5298756 : CollatzResearch.WordTrace tailWord_5298756 prefixEnd_5298756 100770692551673178758573 := by
  unfold tailWord_5298756
  simp only [CollatzResearch.WordTrace]
  refine ⟨96630754195759721161362061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128841005594346294881816081 96630754195759721161362061)
  ·
    refine ⟨36236532823409895435510773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96630754195759721161362061 36236532823409895435510773)
    ·
      refine ⟨3397174952194677697079135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36236532823409895435510773 3397174952194677697079135)
      ·
        refine ⟨5095762428292016545618703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3397174952194677697079135 5095762428292016545618703)
        ·
          refine ⟨7643643642438024818428055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5095762428292016545618703 7643643642438024818428055)
          ·
            refine ⟨11465465463657037227642083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7643643642438024818428055 11465465463657037227642083)
            ·
              refine ⟨17198198195485555841463125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11465465463657037227642083 17198198195485555841463125)
              ·
                refine ⟨100770692551673178758573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17198198195485555841463125 100770692551673178758573)
                ·
                  rfl

theorem cell23_5298756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 9].length) (baseStart_5298756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5298756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5298756 prefixEnd_5298756 := by exact prefixLift 5298756
  have htrace : WordTrace (prefixWord ++ tailWord_5298756) baseStart_5298756 baseEnd_5298756 := by
    simpa [prefixWord, tailWord_5298756, baseEnd_5298756] using wordTrace_append hprefix tailTrace_5298756
  have hstable : (prefixWord ++ tailWord_5298756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5298756).length < 2 ^ (prefixWord ++ tailWord_5298756).sum := by decide
  have hdescent : baseEnd_5298756 < baseStart_5298756 := by decide
  rcases family_descends (prefixWord ++ tailWord_5298756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5298795 : List Nat := [1, 1, 1, 1, 2, 2, 1, 7, 7]
def baseStart_5298795 : Nat := 118140960795 + 5298795 * 2 ^ 59
def prefixEnd_5298795 : Nat := 4983230072969 + 3 ^ 40 * 5298795 * 2
def baseEnd_5298795 : Nat := 302314302737855685988199

theorem tailTrace_5298795 : CollatzResearch.WordTrace tailWord_5298795 prefixEnd_5298795 302314302737855685988199 := by
  unfold tailWord_5298795
  simp only [CollatzResearch.WordTrace]
  refine ⟨193262930838378151983393839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128841953892252101322262559 193262930838378151983393839)
  ·
    refine ⟨289894396257567227975090759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193262930838378151983393839 289894396257567227975090759)
    ·
      refine ⟨434841594386350841962636139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289894396257567227975090759 434841594386350841962636139)
      ·
        refine ⟨652262391579526262943954209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 434841594386350841962636139 652262391579526262943954209)
        ·
          refine ⟨489196793684644697207965657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 652262391579526262943954209 489196793684644697207965657)
          ·
            refine ⟨366897595263483522905974243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 489196793684644697207965657 366897595263483522905974243)
            ·
              refine ⟨550346392895225284358961365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 366897595263483522905974243 550346392895225284358961365)
              ·
                refine ⟨12898743583481842602163157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 550346392895225284358961365 12898743583481842602163157)
                ·
                  refine ⟨302314302737855685988199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12898743583481842602163157 302314302737855685988199)
                  ·
                    rfl

theorem cell23_5298795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 7, 7].length) (baseStart_5298795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5298795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5298795 prefixEnd_5298795 := by exact prefixLift 5298795
  have htrace : WordTrace (prefixWord ++ tailWord_5298795) baseStart_5298795 baseEnd_5298795 := by
    simpa [prefixWord, tailWord_5298795, baseEnd_5298795] using wordTrace_append hprefix tailTrace_5298795
  have hstable : (prefixWord ++ tailWord_5298795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5298795).length < 2 ^ (prefixWord ++ tailWord_5298795).sum := by decide
  have hdescent : baseEnd_5298795 < baseStart_5298795 := by decide
  rcases family_descends (prefixWord ++ tailWord_5298795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5298800 : List Nat := [2, 1, 1, 1, 8, 1, 2, 1, 2, 1, 3]
def baseStart_5298800 : Nat := 118140960795 + 5298800 * 2 ^ 59
def prefixEnd_5298800 : Nat := 4983230072969 + 3 ^ 40 * 5298800 * 2
def baseEnd_5298800 : Nat := 2720831292043973654331269

theorem tailTrace_5298800 : CollatzResearch.WordTrace tailWord_5298800 prefixEnd_5298800 2720831292043973654331269 := by
  unfold tailWord_5298800
  simp only [CollatzResearch.WordTrace]
  refine ⟨96631556601680018918662927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128842075468906691891550569 96631556601680018918662927)
  ·
    refine ⟨144947334902520028377994391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96631556601680018918662927 144947334902520028377994391)
    ·
      refine ⟨217421002353780042566991587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144947334902520028377994391 217421002353780042566991587)
      ·
        refine ⟨326131503530670063850487381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217421002353780042566991587 326131503530670063850487381)
        ·
          refine ⟨3821853557000039810747899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 326131503530670063850487381 3821853557000039810747899)
          ·
            refine ⟨5732780335500059716121849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3821853557000039810747899 5732780335500059716121849)
            ·
              refine ⟨4299585251625044787091387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5732780335500059716121849 4299585251625044787091387)
              ·
                refine ⟨6449377877437567180637081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4299585251625044787091387 6449377877437567180637081)
                ·
                  refine ⟨4837033408078175385477811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6449377877437567180637081 4837033408078175385477811)
                  ·
                    refine ⟨7255550112117263078216717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4837033408078175385477811 7255550112117263078216717)
                    ·
                      refine ⟨2720831292043973654331269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7255550112117263078216717 2720831292043973654331269)
                      ·
                        rfl

theorem cell23_5298800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 2, 1, 2, 1, 3].length) (baseStart_5298800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5298800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5298800 prefixEnd_5298800 := by exact prefixLift 5298800
  have htrace : WordTrace (prefixWord ++ tailWord_5298800) baseStart_5298800 baseEnd_5298800 := by
    simpa [prefixWord, tailWord_5298800, baseEnd_5298800] using wordTrace_append hprefix tailTrace_5298800
  have hstable : (prefixWord ++ tailWord_5298800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5298800).length < 2 ^ (prefixWord ++ tailWord_5298800).sum := by decide
  have hdescent : baseEnd_5298800 < baseStart_5298800 := by decide
  rcases family_descends (prefixWord ++ tailWord_5298800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5298835 : List Nat := [1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 7]
def baseStart_5298835 : Nat := 118140960795 + 5298835 * 2 ^ 59
def prefixEnd_5298835 : Nat := 4983230072969 + 3 ^ 40 * 5298835 * 2
def baseEnd_5298835 : Nat := 2720849263866881017393607

theorem tailTrace_5298835 : CollatzResearch.WordTrace tailWord_5298835 prefixEnd_5298835 2720849263866881017393607 := by
  unfold tailWord_5298835
  simp only [CollatzResearch.WordTrace]
  refine ⟨193264389758233238814849959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128842926505488825876566639 193264389758233238814849959)
  ·
    refine ⟨289896584637349858222274939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193264389758233238814849959 289896584637349858222274939)
    ·
      refine ⟨434844876956024787333412409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289896584637349858222274939 434844876956024787333412409)
      ·
        refine ⟨326133657717018590500059307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 434844876956024787333412409 326133657717018590500059307)
        ·
          refine ⟨489200486575527885750088961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 326133657717018590500059307 489200486575527885750088961)
          ·
            refine ⟨366900364931645914312566721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 489200486575527885750088961 366900364931645914312566721)
            ·
              refine ⟨275175273698734435734425041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 366900364931645914312566721 275175273698734435734425041)
              ·
                refine ⟨206381455274050826800818781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 275175273698734435734425041 206381455274050826800818781)
                ·
                  refine ⟨77393045727769060050307043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 206381455274050826800818781 77393045727769060050307043)
                  ·
                    refine ⟨116089568591653590075460565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 77393045727769060050307043 116089568591653590075460565)
                    ·
                      refine ⟨2720849263866881017393607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 116089568591653590075460565 2720849263866881017393607)
                      ·
                        rfl

theorem cell23_5298835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 7].length) (baseStart_5298835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5298835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5298835 prefixEnd_5298835 := by exact prefixLift 5298835
  have htrace : WordTrace (prefixWord ++ tailWord_5298835) baseStart_5298835 baseEnd_5298835 := by
    simpa [prefixWord, tailWord_5298835, baseEnd_5298835] using wordTrace_append hprefix tailTrace_5298835
  have hstable : (prefixWord ++ tailWord_5298835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5298835).length < 2 ^ (prefixWord ++ tailWord_5298835).sum := by decide
  have hdescent : baseEnd_5298835 < baseStart_5298835 := by decide
  rcases family_descends (prefixWord ++ tailWord_5298835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5298846 : List Nat := [4, 3, 1, 1, 1, 1, 3, 4, 5]
def baseStart_5298846 : Nat := 118140960795 + 5298846 * 2 ^ 59
def prefixEnd_5298846 : Nat := 4983230072969 + 3 ^ 40 * 5298846 * 2
def baseEnd_5298846 : Nat := 302317212461564497150673

theorem tailTrace_5298846 : CollatzResearch.WordTrace tailWord_5298846 prefixEnd_5298846 302317212461564497150673 := by
  unfold tailWord_5298846
  simp only [CollatzResearch.WordTrace]
  refine ⟨24158098870149173461687549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128843193974128925129000261 24158098870149173461687549)
  ·
    refine ⟨9059287076305940048132831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24158098870149173461687549 9059287076305940048132831)
    ·
      refine ⟨13588930614458910072199247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9059287076305940048132831 13588930614458910072199247)
      ·
        refine ⟨20383395921688365108298871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13588930614458910072199247 20383395921688365108298871)
        ·
          refine ⟨30575093882532547662448307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20383395921688365108298871 30575093882532547662448307)
          ·
            refine ⟨45862640823798821493672461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30575093882532547662448307 45862640823798821493672461)
            ·
              refine ⟨17198490308924558060127173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45862640823798821493672461 17198490308924558060127173)
              ·
                refine ⟨3224716932923354636273845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17198490308924558060127173 3224716932923354636273845)
                ·
                  refine ⟨302317212461564497150673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3224716932923354636273845 302317212461564497150673)
                  ·
                    rfl

theorem cell23_5298846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 4, 5].length) (baseStart_5298846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5298846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5298846 prefixEnd_5298846 := by exact prefixLift 5298846
  have htrace : WordTrace (prefixWord ++ tailWord_5298846) baseStart_5298846 baseEnd_5298846 := by
    simpa [prefixWord, tailWord_5298846, baseEnd_5298846] using wordTrace_append hprefix tailTrace_5298846
  have hstable : (prefixWord ++ tailWord_5298846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5298846).length < 2 ^ (prefixWord ++ tailWord_5298846).sum := by decide
  have hdescent : baseEnd_5298846 < baseStart_5298846 := by decide
  rcases family_descends (prefixWord ++ tailWord_5298846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5298852 : List Nat := [2, 3, 1, 2, 2, 1, 1, 3, 1, 2, 5]
def baseStart_5298852 : Nat := 118140960795 + 5298852 * 2 ^ 59
def prefixEnd_5298852 : Nat := 4983230072969 + 3 ^ 40 * 5298852 * 2
def baseEnd_5298852 : Nat := 2720857993038007450881029

theorem tailTrace_5298852 : CollatzResearch.WordTrace tailWord_5298852 prefixEnd_5298852 2720857993038007450881029 := by
  unfold tailWord_5298852
  simp only [CollatzResearch.WordTrace]
  refine ⟨96632504899585825359109405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128843339866114433812145873 96632504899585825359109405)
  ·
    refine ⟨36237189337344684509666027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96632504899585825359109405 36237189337344684509666027)
    ·
      refine ⟨54355784006017026764499041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36237189337344684509666027 54355784006017026764499041)
      ·
        refine ⟨40766838004512770073374281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54355784006017026764499041 40766838004512770073374281)
        ·
          refine ⟨30575128503384577555030711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40766838004512770073374281 30575128503384577555030711)
          ·
            refine ⟨45862692755076866332546067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30575128503384577555030711 45862692755076866332546067)
            ·
              refine ⟨68794039132615299498819101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45862692755076866332546067 68794039132615299498819101)
              ·
                refine ⟨25797764674730737312057163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68794039132615299498819101 25797764674730737312057163)
                ·
                  refine ⟨38696647012096105968085745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25797764674730737312057163 38696647012096105968085745)
                  ·
                    refine ⟨29022485259072079476064309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38696647012096105968085745 29022485259072079476064309)
                    ·
                      refine ⟨2720857993038007450881029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29022485259072079476064309 2720857993038007450881029)
                      ·
                        rfl

theorem cell23_5298852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_5298852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5298852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5298852 prefixEnd_5298852 := by exact prefixLift 5298852
  have htrace : WordTrace (prefixWord ++ tailWord_5298852) baseStart_5298852 baseEnd_5298852 := by
    simpa [prefixWord, tailWord_5298852, baseEnd_5298852] using wordTrace_append hprefix tailTrace_5298852
  have hstable : (prefixWord ++ tailWord_5298852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5298852).length < 2 ^ (prefixWord ++ tailWord_5298852).sum := by decide
  have hdescent : baseEnd_5298852 < baseStart_5298852 := by decide
  rcases family_descends (prefixWord ++ tailWord_5298852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5298879 : List Nat := [1, 1, 2, 2, 2, 4, 3, 1, 2, 1, 4]
def baseStart_5298879 : Nat := 118140960795 + 5298879 * 2 ^ 59
def prefixEnd_5298879 : Nat := 4983230072969 + 3 ^ 40 * 5298879 * 2
def baseEnd_5298879 : Nat := 2720871857015678845243405

theorem tailTrace_5298879 : CollatzResearch.WordTrace tailWord_5298879 prefixEnd_5298879 2720871857015678845243405 := by
  unfold tailWord_5298879
  simp only [CollatzResearch.WordTrace]
  refine ⟨193265994570073834329451691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128843996380049222886301127 193265994570073834329451691)
  ·
    refine ⟨289898991855110751494177537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193265994570073834329451691 289898991855110751494177537)
    ·
      refine ⟨217424243891333063620633153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 289898991855110751494177537 217424243891333063620633153)
      ·
        refine ⟨163068182918499797715474865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 217424243891333063620633153 163068182918499797715474865)
        ·
          refine ⟨122301137188874848286606149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163068182918499797715474865 122301137188874848286606149)
          ·
            refine ⟨22931463222914034053738653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 122301137188874848286606149 22931463222914034053738653)
            ·
              refine ⟨8599298708592762770151995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22931463222914034053738653 8599298708592762770151995)
              ·
                refine ⟨12898948062889144155227993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8599298708592762770151995 12898948062889144155227993)
                ·
                  refine ⟨9674211047166858116420995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12898948062889144155227993 9674211047166858116420995)
                  ·
                    refine ⟨14511316570750287174631493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9674211047166858116420995 14511316570750287174631493)
                    ·
                      refine ⟨2720871857015678845243405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14511316570750287174631493 2720871857015678845243405)
                      ·
                        rfl

theorem cell23_5298879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 1, 2, 1, 4].length) (baseStart_5298879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5298879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5298879 prefixEnd_5298879 := by exact prefixLift 5298879
  have htrace : WordTrace (prefixWord ++ tailWord_5298879) baseStart_5298879 baseEnd_5298879 := by
    simpa [prefixWord, tailWord_5298879, baseEnd_5298879] using wordTrace_append hprefix tailTrace_5298879
  have hstable : (prefixWord ++ tailWord_5298879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5298879).length < 2 ^ (prefixWord ++ tailWord_5298879).sum := by decide
  have hdescent : baseEnd_5298879 < baseStart_5298879 := by decide
  rcases family_descends (prefixWord ++ tailWord_5298879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5298906 : List Nat := [3, 1, 1, 2, 2, 2, 1, 6, 1, 4]
def baseStart_5298906 : Nat := 118140960795 + 5298906 * 2 ^ 59
def prefixEnd_5298906 : Nat := 4983230072969 + 3 ^ 40 * 5298906 * 2
def baseEnd_5298906 : Nat := 906961906997783413201927

theorem tailTrace_5298906 : CollatzResearch.WordTrace tailWord_5298906 prefixEnd_5298906 906961906997783413201927 := by
  unfold tailWord_5298906
  simp only [CollatzResearch.WordTrace]
  refine ⟨48316744835244004485171143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128844652893984011960456381 48316744835244004485171143)
  ·
    refine ⟨72475117252866006727756715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48316744835244004485171143 72475117252866006727756715)
    ·
      refine ⟨108712675879299010091635073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72475117252866006727756715 108712675879299010091635073)
      ·
        refine ⟨81534506909474257568726305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108712675879299010091635073 81534506909474257568726305)
        ·
          refine ⟨61150880182105693176544729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81534506909474257568726305 61150880182105693176544729)
          ·
            refine ⟨45863160136579269882408547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61150880182105693176544729 45863160136579269882408547)
            ·
              refine ⟨68794740204868904823612821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45863160136579269882408547 68794740204868904823612821)
              ·
                refine ⟨3224753447103229913606851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 68794740204868904823612821 3224753447103229913606851)
                ·
                  refine ⟨4837130170654844870410277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3224753447103229913606851 4837130170654844870410277)
                  ·
                    refine ⟨906961906997783413201927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4837130170654844870410277 906961906997783413201927)
                    ·
                      rfl

theorem cell23_5298906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 6, 1, 4].length) (baseStart_5298906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5298906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5298906 prefixEnd_5298906 := by exact prefixLift 5298906
  have htrace : WordTrace (prefixWord ++ tailWord_5298906) baseStart_5298906 baseEnd_5298906 := by
    simpa [prefixWord, tailWord_5298906, baseEnd_5298906] using wordTrace_append hprefix tailTrace_5298906
  have hstable : (prefixWord ++ tailWord_5298906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5298906).length < 2 ^ (prefixWord ++ tailWord_5298906).sum := by decide
  have hdescent : baseEnd_5298906 < baseStart_5298906 := by decide
  rcases family_descends (prefixWord ++ tailWord_5298906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5298922 : List Nat := [3, 1, 3, 1, 1, 1, 1, 1, 3, 2, 6]
def baseStart_5298922 : Nat := 118140960795 + 5298922 * 2 ^ 59
def prefixEnd_5298922 : Nat := 4983230072969 + 3 ^ 40 * 5298922 * 2
def baseEnd_5298922 : Nat := 2720893936683822177005707

theorem tailTrace_5298922 : CollatzResearch.WordTrace tailWord_5298922 prefixEnd_5298922 2720893936683822177005707 := by
  unfold tailWord_5298922
  simp only [CollatzResearch.WordTrace]
  refine ⟨48316890727229513168316755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128845041939278701782178013 48316890727229513168316755)
  ·
    refine ⟨72475336090844269752475133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48316890727229513168316755 72475336090844269752475133)
    ·
      refine ⟨27178251034066601157178175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72475336090844269752475133 27178251034066601157178175)
      ·
        refine ⟨40767376551099901735767263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27178251034066601157178175 40767376551099901735767263)
        ·
          refine ⟨61151064826649852603650895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40767376551099901735767263 61151064826649852603650895)
          ·
            refine ⟨91726597239974778905476343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61151064826649852603650895 91726597239974778905476343)
            ·
              refine ⟨137589895859962168358214515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91726597239974778905476343 137589895859962168358214515)
              ·
                refine ⟨206384843789943252537321773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 137589895859962168358214515 206384843789943252537321773)
                ·
                  refine ⟨77394316421228719701495665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 206384843789943252537321773 77394316421228719701495665)
                  ·
                    refine ⟨58045737315921539776121749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 77394316421228719701495665 58045737315921539776121749)
                    ·
                      refine ⟨2720893936683822177005707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58045737315921539776121749 2720893936683822177005707)
                      ·
                        rfl

theorem cell23_5298922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_5298922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5298922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5298922 prefixEnd_5298922 := by exact prefixLift 5298922
  have htrace : WordTrace (prefixWord ++ tailWord_5298922) baseStart_5298922 baseEnd_5298922 := by
    simpa [prefixWord, tailWord_5298922, baseEnd_5298922] using wordTrace_append hprefix tailTrace_5298922
  have hstable : (prefixWord ++ tailWord_5298922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5298922).length < 2 ^ (prefixWord ++ tailWord_5298922).sum := by decide
  have hdescent : baseEnd_5298922 < baseStart_5298922 := by decide
  rcases family_descends (prefixWord ++ tailWord_5298922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5298969 : List Nat := [1, 2, 1, 2, 1, 1, 1, 4, 2, 6, 2]
def baseStart_5298969 : Nat := 118140960795 + 5298969 * 2 ^ 59
def prefixEnd_5298969 : Nat := 4983230072969 + 3 ^ 40 * 5298969 * 2
def baseEnd_5298969 : Nat := 2720918070274583493117991

theorem tailTrace_5298969 : CollatzResearch.WordTrace tailWord_5298969 prefixEnd_5298969 2720918070274583493117991 := by
  unfold tailWord_5298969
  simp only [CollatzResearch.WordTrace]
  refine ⟨193269277139747779700227961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128846184759831853133485307 193269277139747779700227961)
  ·
    refine ⟨144951957854810834775170971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193269277139747779700227961 144951957854810834775170971)
    ·
      refine ⟨217427936782216252162756457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144951957854810834775170971 217427936782216252162756457)
      ·
        refine ⟨163070952586662189122067343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 217427936782216252162756457 163070952586662189122067343)
        ·
          refine ⟨244606428879993283683101015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163070952586662189122067343 244606428879993283683101015)
          ·
            refine ⟨366909643319989925524651523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 244606428879993283683101015 366909643319989925524651523)
            ·
              refine ⟨550364464979984888286977285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 366909643319989925524651523 550364464979984888286977285)
              ·
                refine ⟨103193337183747166553808241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 550364464979984888286977285 103193337183747166553808241)
                ·
                  refine ⟨77395002887810374915356181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 103193337183747166553808241 77395002887810374915356181)
                  ·
                    refine ⟨3627890760366111324157321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 77395002887810374915356181 3627890760366111324157321)
                    ·
                      refine ⟨2720918070274583493117991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3627890760366111324157321 2720918070274583493117991)
                      ·
                        rfl

theorem cell23_5298969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 6, 2].length) (baseStart_5298969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5298969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5298969 prefixEnd_5298969 := by exact prefixLift 5298969
  have htrace : WordTrace (prefixWord ++ tailWord_5298969) baseStart_5298969 baseEnd_5298969 := by
    simpa [prefixWord, tailWord_5298969, baseEnd_5298969] using wordTrace_append hprefix tailTrace_5298969
  have hstable : (prefixWord ++ tailWord_5298969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5298969).length < 2 ^ (prefixWord ++ tailWord_5298969).sum := by decide
  have hdescent : baseEnd_5298969 < baseStart_5298969 := by decide
  rcases family_descends (prefixWord ++ tailWord_5298969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5298990 : List Nat := [4, 1, 3, 2, 1, 2, 2, 1, 2, 3, 2]
def baseStart_5298990 : Nat := 118140960795 + 5298990 * 2 ^ 59
def prefixEnd_5298990 : Nat := 4983230072969 + 3 ^ 40 * 5298990 * 2
def baseEnd_5298990 : Nat := 2720928853368327910955395

theorem tailTrace_5298990 : CollatzResearch.WordTrace tailWord_5298990 prefixEnd_5298990 2720928853368327910955395 := by
  unfold tailWord_5298990
  simp only [CollatzResearch.WordTrace]
  refine ⟨24158755384083962535842803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128846695381781133524494949 24158755384083962535842803)
  ·
    refine ⟨36238133076125943803764205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24158755384083962535842803 36238133076125943803764205)
    ·
      refine ⟨13589299903547228926411577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36238133076125943803764205 13589299903547228926411577)
      ·
        refine ⟨10191974927660421694808683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13589299903547228926411577 10191974927660421694808683)
        ·
          refine ⟨15287962391490632542213025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10191974927660421694808683 15287962391490632542213025)
          ·
            refine ⟨11465971793617974406659769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15287962391490632542213025 11465971793617974406659769)
            ·
              refine ⟨8599478845213480804994827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11465971793617974406659769 8599478845213480804994827)
              ·
                refine ⟨12899218267820221207492241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8599478845213480804994827 12899218267820221207492241)
                ·
                  refine ⟨9674413700865165905619181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12899218267820221207492241 9674413700865165905619181)
                  ·
                    refine ⟨3627905137824437214607193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9674413700865165905619181 3627905137824437214607193)
                    ·
                      refine ⟨2720928853368327910955395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3627905137824437214607193 2720928853368327910955395)
                      ·
                        rfl

theorem cell23_5298990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_5298990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5298990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5298990 prefixEnd_5298990 := by exact prefixLift 5298990
  have htrace : WordTrace (prefixWord ++ tailWord_5298990) baseStart_5298990 baseEnd_5298990 := by
    simpa [prefixWord, tailWord_5298990, baseEnd_5298990] using wordTrace_append hprefix tailTrace_5298990
  have hstable : (prefixWord ++ tailWord_5298990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5298990).length < 2 ^ (prefixWord ++ tailWord_5298990).sum := by decide
  have hdescent : baseEnd_5298990 < baseStart_5298990 := by decide
  rcases family_descends (prefixWord ++ tailWord_5298990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5298999 : List Nat := [1, 1, 3, 1, 2, 1, 5, 2, 1, 2, 4]
def baseStart_5298999 : Nat := 118140960795 + 5298999 * 2 ^ 59
def prefixEnd_5298999 : Nat := 4983230072969 + 3 ^ 40 * 5298999 * 2
def baseEnd_5298999 : Nat := 2720933474694218375742853

theorem tailTrace_5298999 : CollatzResearch.WordTrace tailWord_5298999 prefixEnd_5298999 2720933474694218375742853 := by
  unfold tailWord_5298999
  simp only [CollatzResearch.WordTrace]
  refine ⟨193270371329639094823820051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128846914219759396549213367 193270371329639094823820051)
  ·
    refine ⟨289905556994458642235730077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193270371329639094823820051 289905556994458642235730077)
    ·
      refine ⟨108714583872921990838398779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 289905556994458642235730077 108714583872921990838398779)
      ·
        refine ⟨163071875809382986257598169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108714583872921990838398779 163071875809382986257598169)
        ·
          refine ⟨122303906857037239693198627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163071875809382986257598169 122303906857037239693198627)
          ·
            refine ⟨183455860285555859539797941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122303906857037239693198627 183455860285555859539797941)
            ·
              refine ⟨17198986901770861831856057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 183455860285555859539797941 17198986901770861831856057)
              ·
                refine ⟨12899240176328146373892043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17198986901770861831856057 12899240176328146373892043)
                ·
                  refine ⟨19348860264492219560838065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12899240176328146373892043 19348860264492219560838065)
                  ·
                    refine ⟨14511645198369164670628549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19348860264492219560838065 14511645198369164670628549)
                    ·
                      refine ⟨2720933474694218375742853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14511645198369164670628549 2720933474694218375742853)
                      ·
                        rfl

theorem cell23_5298999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 2, 1, 2, 4].length) (baseStart_5298999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5298999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5298999 prefixEnd_5298999 := by exact prefixLift 5298999
  have htrace : WordTrace (prefixWord ++ tailWord_5298999) baseStart_5298999 baseEnd_5298999 := by
    simpa [prefixWord, tailWord_5298999, baseEnd_5298999] using wordTrace_append hprefix tailTrace_5298999
  have hstable : (prefixWord ++ tailWord_5298999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5298999).length < 2 ^ (prefixWord ++ tailWord_5298999).sum := by decide
  have hdescent : baseEnd_5298999 < baseStart_5298999 := by decide
  rcases family_descends (prefixWord ++ tailWord_5298999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5299009 : List Nat := [1, 2, 5, 3, 12]
def baseStart_5299009 : Nat := 118140960795 + 5299009 * 2 ^ 59
def prefixEnd_5299009 : Nat := 4983230072969 + 3 ^ 40 * 5299009 * 2
def baseEnd_5299009 : Nat := 3732426076132734343783

theorem tailTrace_5299009 : CollatzResearch.WordTrace tailWord_5299009 prefixEnd_5299009 3732426076132734343783 := by
  unfold tailWord_5299009
  simp only [CollatzResearch.WordTrace]
  refine ⟨193270736059602866531684081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128847157373068577687789387 193270736059602866531684081)
  ·
    refine ⟨144953052044702149898763061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193270736059602866531684081 144953052044702149898763061)
    ·
      refine ⟨13589348629190826553009037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 144953052044702149898763061 13589348629190826553009037)
      ·
        refine ⟨5096005735946559957378389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13589348629190826553009037 5096005735946559957378389)
        ·
          refine ⟨3732426076132734343783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 5096005735946559957378389 3732426076132734343783)
          ·
            rfl

theorem cell23_5299009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 12].length) (baseStart_5299009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5299009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5299009 prefixEnd_5299009 := by exact prefixLift 5299009
  have htrace : WordTrace (prefixWord ++ tailWord_5299009) baseStart_5299009 baseEnd_5299009 := by
    simpa [prefixWord, tailWord_5299009, baseEnd_5299009] using wordTrace_append hprefix tailTrace_5299009
  have hstable : (prefixWord ++ tailWord_5299009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5299009).length < 2 ^ (prefixWord ++ tailWord_5299009).sum := by decide
  have hdescent : baseEnd_5299009 < baseStart_5299009 := by decide
  rcases family_descends (prefixWord ++ tailWord_5299009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5299014 : List Nat := [6, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3]
def baseStart_5299014 : Nat := 118140960795 + 5299014 * 2 ^ 59
def prefixEnd_5299014 : Nat := 4983230072969 + 3 ^ 40 * 5299014 * 2
def baseEnd_5299014 : Nat := 2720941176904035817055285

theorem tailTrace_5299014 : CollatzResearch.WordTrace tailWord_5299014 prefixEnd_5299014 2720941176904035817055285 := by
  unfold tailWord_5299014
  simp only [CollatzResearch.WordTrace]
  refine ⟨6039716200768273512050503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 128847278949723168257077397 6039716200768273512050503)
  ·
    refine ⟨9059574301152410268075755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6039716200768273512050503 9059574301152410268075755)
    ·
      refine ⟨13589361451728615402113633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9059574301152410268075755 13589361451728615402113633)
      ·
        refine ⟨10192021088796461551585225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13589361451728615402113633 10192021088796461551585225)
        ·
          refine ⟨7644015816597346163688919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10192021088796461551585225 7644015816597346163688919)
          ·
            refine ⟨11466023724896019245533379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7644015816597346163688919 11466023724896019245533379)
            ·
              refine ⟨17199035587344028868300069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11466023724896019245533379 17199035587344028868300069)
              ·
                refine ⟨3224819172627005412806263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17199035587344028868300069 3224819172627005412806263)
                ·
                  refine ⟨4837228758940508119209395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3224819172627005412806263 4837228758940508119209395)
                  ·
                    refine ⟨7255843138410762178814093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4837228758940508119209395 7255843138410762178814093)
                    ·
                      refine ⟨2720941176904035817055285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7255843138410762178814093 2720941176904035817055285)
                      ·
                        rfl

theorem cell23_5299014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3].length) (baseStart_5299014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5299014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5299014 prefixEnd_5299014 := by exact prefixLift 5299014
  have htrace : WordTrace (prefixWord ++ tailWord_5299014) baseStart_5299014 baseEnd_5299014 := by
    simpa [prefixWord, tailWord_5299014, baseEnd_5299014] using wordTrace_append hprefix tailTrace_5299014
  have hstable : (prefixWord ++ tailWord_5299014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5299014).length < 2 ^ (prefixWord ++ tailWord_5299014).sum := by decide
  have hdescent : baseEnd_5299014 < baseStart_5299014 := by decide
  rcases family_descends (prefixWord ++ tailWord_5299014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5299054 : List Nat := [4, 1, 2, 3, 2, 1, 2, 3, 1, 2, 2]
def baseStart_5299054 : Nat := 118140960795 + 5299054 * 2 ^ 59
def prefixEnd_5299054 : Nat := 4983230072969 + 3 ^ 40 * 5299054 * 2
def baseEnd_5299054 : Nat := 2720961716130215660555101

theorem tailTrace_5299054 : CollatzResearch.WordTrace tailWord_5299054 prefixEnd_5299054 2720961716130215660555101 := by
  unfold tailWord_5299054
  simp only [CollatzResearch.WordTrace]
  refine ⟨24159047168054979902134027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128848251562959892811381477 24159047168054979902134027)
  ·
    refine ⟨36238570752082469853201041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24159047168054979902134027 36238570752082469853201041)
    ·
      refine ⟨27178928064061852389900781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36238570752082469853201041 27178928064061852389900781)
      ·
        refine ⟨10192098024023194646212793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27178928064061852389900781 10192098024023194646212793)
        ·
          refine ⟨7644073518017395984659595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10192098024023194646212793 7644073518017395984659595)
          ·
            refine ⟨11466110277026093976989393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7644073518017395984659595 11466110277026093976989393)
            ·
              refine ⟨8599582707769570482742045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11466110277026093976989393 8599582707769570482742045)
              ·
                refine ⟨3224843515413588931028267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8599582707769570482742045 3224843515413588931028267)
                ·
                  refine ⟨4837265273120383396542401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3224843515413588931028267 4837265273120383396542401)
                  ·
                    refine ⟨3627948954840287547406801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4837265273120383396542401 3627948954840287547406801)
                    ·
                      refine ⟨2720961716130215660555101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3627948954840287547406801 2720961716130215660555101)
                      ·
                        rfl

theorem cell23_5299054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 3, 1, 2, 2].length) (baseStart_5299054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5299054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5299054 prefixEnd_5299054 := by exact prefixLift 5299054
  have htrace : WordTrace (prefixWord ++ tailWord_5299054) baseStart_5299054 baseEnd_5299054 := by
    simpa [prefixWord, tailWord_5299054, baseEnd_5299054] using wordTrace_append hprefix tailTrace_5299054
  have hstable : (prefixWord ++ tailWord_5299054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5299054).length < 2 ^ (prefixWord ++ tailWord_5299054).sum := by decide
  have hdescent : baseEnd_5299054 < baseStart_5299054 := by decide
  rcases family_descends (prefixWord ++ tailWord_5299054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5299069 : List Nat := [1, 4, 1, 1, 2, 1, 3, 2, 2, 6]
def baseStart_5299069 : Nat := 118140960795 + 5299069 * 2 ^ 59
def prefixEnd_5299069 : Nat := 4983230072969 + 3 ^ 40 * 5299069 * 2
def baseEnd_5299069 : Nat := 906989806113344367289177

theorem tailTrace_5299069 : CollatzResearch.WordTrace tailWord_5299069 prefixEnd_5299069 906989806113344367289177 := by
  unfold tailWord_5299069
  simp only [CollatzResearch.WordTrace]
  refine ⟨193272924439385496778868261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128848616292923664519245507 193272924439385496778868261)
  ·
    refine ⟨36238673332384780646037799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 193272924439385496778868261 36238673332384780646037799)
    ·
      refine ⟨54358009998577170969056699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36238673332384780646037799 54358009998577170969056699)
      ·
        refine ⟨81537014997865756453585049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54358009998577170969056699 81537014997865756453585049)
        ·
          refine ⟨61152761248399317340188787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81537014997865756453585049 61152761248399317340188787)
          ·
            refine ⟨91729141872598976010283181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61152761248399317340188787 91729141872598976010283181)
            ·
              refine ⟨34398428202224616003856193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91729141872598976010283181 34398428202224616003856193)
              ·
                refine ⟨25798821151668462002892145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34398428202224616003856193 25798821151668462002892145)
                ·
                  refine ⟨19349115863751346502169109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25798821151668462002892145 19349115863751346502169109)
                  ·
                    refine ⟨906989806113344367289177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19349115863751346502169109 906989806113344367289177)
                    ·
                      rfl

theorem cell23_5299069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 2, 2, 6].length) (baseStart_5299069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5299069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5299069 prefixEnd_5299069 := by exact prefixLift 5299069
  have htrace : WordTrace (prefixWord ++ tailWord_5299069) baseStart_5299069 baseEnd_5299069 := by
    simpa [prefixWord, tailWord_5299069, baseEnd_5299069] using wordTrace_append hprefix tailTrace_5299069
  have hstable : (prefixWord ++ tailWord_5299069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5299069).length < 2 ^ (prefixWord ++ tailWord_5299069).sum := by decide
  have hdescent : baseEnd_5299069 < baseStart_5299069 := by decide
  rcases family_descends (prefixWord ++ tailWord_5299069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5299093 : List Nat := [1, 3, 2, 1, 1, 4, 3, 1, 1, 4, 2]
def baseStart_5299093 : Nat := 118140960795 + 5299093 * 2 ^ 59
def prefixEnd_5299093 : Nat := 4983230072969 + 3 ^ 40 * 5299093 * 2
def baseEnd_5299093 : Nat := 2720981741875741007967421

theorem tailTrace_5299093 : CollatzResearch.WordTrace tailWord_5299093 prefixEnd_5299093 2720981741875741007967421 := by
  unfold tailWord_5299093
  simp only [CollatzResearch.WordTrace]
  refine ⟨193273799791298548877741933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128849199860865699251827955 193273799791298548877741933)
  ·
    refine ⟨72477674921736955829153225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 193273799791298548877741933 72477674921736955829153225)
    ·
      refine ⟨54358256191302716871864919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72477674921736955829153225 54358256191302716871864919)
      ·
        refine ⟨81537384286954075307797379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54358256191302716871864919 81537384286954075307797379)
        ·
          refine ⟨122306076430431112961696069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81537384286954075307797379 122306076430431112961696069)
          ·
            refine ⟨22932389330705833680318013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 122306076430431112961696069 22932389330705833680318013)
            ·
              refine ⟨8599645999014687630119255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22932389330705833680318013 8599645999014687630119255)
              ·
                refine ⟨12899468998522031445178883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8599645999014687630119255 12899468998522031445178883)
                ·
                  refine ⟨19349203497783047167768325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12899468998522031445178883 19349203497783047167768325)
                  ·
                    refine ⟨3627975655834321343956561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19349203497783047167768325 3627975655834321343956561)
                    ·
                      refine ⟨2720981741875741007967421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3627975655834321343956561 2720981741875741007967421)
                      ·
                        rfl

theorem cell23_5299093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 1, 1, 4, 2].length) (baseStart_5299093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5299093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5299093 prefixEnd_5299093 := by exact prefixLift 5299093
  have htrace : WordTrace (prefixWord ++ tailWord_5299093) baseStart_5299093 baseEnd_5299093 := by
    simpa [prefixWord, tailWord_5299093, baseEnd_5299093] using wordTrace_append hprefix tailTrace_5299093
  have hstable : (prefixWord ++ tailWord_5299093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5299093).length < 2 ^ (prefixWord ++ tailWord_5299093).sum := by decide
  have hdescent : baseEnd_5299093 < baseStart_5299093 := by decide
  rcases family_descends (prefixWord ++ tailWord_5299093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5299133 : List Nat := [1, 4, 1, 2, 4, 2, 1, 1, 7]
def baseStart_5299133 : Nat := 118140960795 + 5299133 * 2 ^ 59
def prefixEnd_5299133 : Nat := 4983230072969 + 3 ^ 40 * 5299133 * 2
def baseEnd_5299133 : Nat := 302333586789102316829693

theorem tailTrace_5299133 : CollatzResearch.WordTrace tailWord_5299133 prefixEnd_5299133 302333586789102316829693 := by
  unfold tailWord_5299133
  simp only [CollatzResearch.WordTrace]
  refine ⟨193275258711153635709198053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128850172474102423806132035 193275258711153635709198053)
  ·
    refine ⟨36239111008341306695474635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 193275258711153635709198053 36239111008341306695474635)
    ·
      refine ⟨54358666512511960043211953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36239111008341306695474635 54358666512511960043211953)
      ·
        refine ⟨40768999884383970032408965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54358666512511960043211953 40768999884383970032408965)
        ·
          refine ⟨7644187478321994381076681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40768999884383970032408965 7644187478321994381076681)
          ·
            refine ⟨5733140608741495785807511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7644187478321994381076681 5733140608741495785807511)
            ·
              refine ⟨8599710913112243678711267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5733140608741495785807511 8599710913112243678711267)
              ·
                refine ⟨12899566369668365518066901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8599710913112243678711267 12899566369668365518066901)
                ·
                  refine ⟨302333586789102316829693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12899566369668365518066901 302333586789102316829693)
                  ·
                    rfl

theorem cell23_5299133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 1, 7].length) (baseStart_5299133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5299133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5299133 prefixEnd_5299133 := by exact prefixLift 5299133
  have htrace : WordTrace (prefixWord ++ tailWord_5299133) baseStart_5299133 baseEnd_5299133 := by
    simpa [prefixWord, tailWord_5299133, baseEnd_5299133] using wordTrace_append hprefix tailTrace_5299133
  have hstable : (prefixWord ++ tailWord_5299133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5299133).length < 2 ^ (prefixWord ++ tailWord_5299133).sum := by decide
  have hdescent : baseEnd_5299133 < baseStart_5299133 := by decide
  rcases family_descends (prefixWord ++ tailWord_5299133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5299139 : List Nat := [1, 1, 1, 3, 1, 1, 2, 5, 1, 2, 5]
def baseStart_5299139 : Nat := 118140960795 + 5299139 * 2 ^ 59
def prefixEnd_5299139 : Nat := 4983230072969 + 3 ^ 40 * 5299139 * 2
def baseEnd_5299139 : Nat := 2721005361985847827992209

theorem tailTrace_5299139 : CollatzResearch.WordTrace tailWord_5299139 prefixEnd_5299139 2721005361985847827992209 := by
  unfold tailWord_5299139
  simp only [CollatzResearch.WordTrace]
  refine ⟨193275477549131898733916471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128850318366087932489277647 193275477549131898733916471)
  ·
    refine ⟨289913216323697848100874707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193275477549131898733916471 289913216323697848100874707)
    ·
      refine ⟨434869824485546772151312061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289913216323697848100874707 434869824485546772151312061)
      ·
        refine ⟨163076184182080039556742023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 434869824485546772151312061 163076184182080039556742023)
        ·
          refine ⟨244614276273120059335113035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163076184182080039556742023 244614276273120059335113035)
          ·
            refine ⟨366921414409680089002669553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 244614276273120059335113035 366921414409680089002669553)
            ·
              refine ⟨275191060807260066752002165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 366921414409680089002669553 275191060807260066752002165)
              ·
                refine ⟨25799161950680631258000203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 275191060807260066752002165 25799161950680631258000203)
                ·
                  refine ⟨38698742926020946887000305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25799161950680631258000203 38698742926020946887000305)
                  ·
                    refine ⟨29024057194515710165250229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38698742926020946887000305 29024057194515710165250229)
                    ·
                      refine ⟨2721005361985847827992209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29024057194515710165250229 2721005361985847827992209)
                      ·
                        rfl

theorem cell23_5299139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 5, 1, 2, 5].length) (baseStart_5299139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5299139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5299139 prefixEnd_5299139 := by exact prefixLift 5299139
  have htrace : WordTrace (prefixWord ++ tailWord_5299139) baseStart_5299139 baseEnd_5299139 := by
    simpa [prefixWord, tailWord_5299139, baseEnd_5299139] using wordTrace_append hprefix tailTrace_5299139
  have hstable : (prefixWord ++ tailWord_5299139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5299139).length < 2 ^ (prefixWord ++ tailWord_5299139).sum := by decide
  have hdescent : baseEnd_5299139 < baseStart_5299139 := by decide
  rcases family_descends (prefixWord ++ tailWord_5299139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5299144 : List Nat := [2, 1, 3, 1, 5, 2, 2, 1, 2, 2, 2]
def baseStart_5299144 : Nat := 118140960795 + 5299144 * 2 ^ 59
def prefixEnd_5299144 : Nat := 4983230072969 + 3 ^ 40 * 5299144 * 2
def baseEnd_5299144 : Nat := 2721007929389120308429687

theorem tailTrace_5299144 : CollatzResearch.WordTrace tailWord_5299144 prefixEnd_5299144 2721007929389120308429687 := by
  unfold tailWord_5299144
  simp only [CollatzResearch.WordTrace]
  refine ⟨96637829957056892293924243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128850439942742523058565657 96637829957056892293924243)
  ·
    refine ⟨144956744935585338440886365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96637829957056892293924243 144956744935585338440886365)
    ·
      refine ⟨54358779350844501915332387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144956744935585338440886365 54358779350844501915332387)
      ·
        refine ⟨81538169026266752872998581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54358779350844501915332387 81538169026266752872998581)
        ·
          refine ⟨7644203346212508081843617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 81538169026266752872998581 7644203346212508081843617)
          ·
            refine ⟨5733152509659381061382713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7644203346212508081843617 5733152509659381061382713)
            ·
              refine ⟨4299864382244535796037035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5733152509659381061382713 4299864382244535796037035)
              ·
                refine ⟨6449796573366803694055553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4299864382244535796037035 6449796573366803694055553)
                ·
                  refine ⟨4837347430025102770541665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6449796573366803694055553 4837347430025102770541665)
                  ·
                    refine ⟨3628010572518827077906249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4837347430025102770541665 3628010572518827077906249)
                    ·
                      refine ⟨2721007929389120308429687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3628010572518827077906249 2721007929389120308429687)
                      ·
                        rfl

theorem cell23_5299144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 2, 1, 2, 2, 2].length) (baseStart_5299144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5299144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5299144 prefixEnd_5299144 := by exact prefixLift 5299144
  have htrace : WordTrace (prefixWord ++ tailWord_5299144) baseStart_5299144 baseEnd_5299144 := by
    simpa [prefixWord, tailWord_5299144, baseEnd_5299144] using wordTrace_append hprefix tailTrace_5299144
  have hstable : (prefixWord ++ tailWord_5299144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5299144).length < 2 ^ (prefixWord ++ tailWord_5299144).sum := by decide
  have hdescent : baseEnd_5299144 < baseStart_5299144 := by decide
  rcases family_descends (prefixWord ++ tailWord_5299144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5299243 : List Nat := [1, 1, 1, 1, 2, 1, 6, 1, 4, 3, 2]
def baseStart_5299243 : Nat := 118140960795 + 5299243 * 2 ^ 59
def prefixEnd_5299243 : Nat := 4983230072969 + 3 ^ 40 * 5299243 * 2
def baseEnd_5299243 : Nat := 2721058763973915421091731

theorem tailTrace_5299243 : CollatzResearch.WordTrace tailWord_5299243 prefixEnd_5299243 2721058763973915421091731 := by
  unfold tailWord_5299243
  simp only [CollatzResearch.WordTrace]
  refine ⟨193279270740755124495702383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128852847160503416330468255 193279270740755124495702383)
  ·
    refine ⟨289918906111132686743553575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193279270740755124495702383 289918906111132686743553575)
    ·
      refine ⟨434878359166699030115330363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289918906111132686743553575 434878359166699030115330363)
      ·
        refine ⟨652317538750048545172995545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 434878359166699030115330363 652317538750048545172995545)
        ·
          refine ⟨489238154062536408879746659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 652317538750048545172995545 489238154062536408879746659)
          ·
            refine ⟨733857231093804613319619989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 489238154062536408879746659 733857231093804613319619989)
            ·
              refine ⟨34399557707522091249357187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 733857231093804613319619989 34399557707522091249357187)
              ·
                refine ⟨51599336561283136874035781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34399557707522091249357187 51599336561283136874035781)
                ·
                  refine ⟨9674875605240588163881709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51599336561283136874035781 9674875605240588163881709)
                  ·
                    refine ⟨3628078351965220561455641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9674875605240588163881709 3628078351965220561455641)
                    ·
                      refine ⟨2721058763973915421091731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3628078351965220561455641 2721058763973915421091731)
                      ·
                        rfl

theorem cell23_5299243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 4, 3, 2].length) (baseStart_5299243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5299243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5299243 prefixEnd_5299243 := by exact prefixLift 5299243
  have htrace : WordTrace (prefixWord ++ tailWord_5299243) baseStart_5299243 baseEnd_5299243 := by
    simpa [prefixWord, tailWord_5299243, baseEnd_5299243] using wordTrace_append hprefix tailTrace_5299243
  have hstable : (prefixWord ++ tailWord_5299243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5299243).length < 2 ^ (prefixWord ++ tailWord_5299243).sum := by decide
  have hdescent : baseEnd_5299243 < baseStart_5299243 := by decide
  rcases family_descends (prefixWord ++ tailWord_5299243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5299250 : List Nat := [3, 2, 1, 1, 2, 2, 4, 1, 3, 1, 3]
def baseStart_5299250 : Nat := 118140960795 + 5299250 * 2 ^ 59
def prefixEnd_5299250 : Nat := 4983230072969 + 3 ^ 40 * 5299250 * 2
def baseEnd_5299250 : Nat := 2721062358338496893704199

theorem tailTrace_5299250 : CollatzResearch.WordTrace tailWord_5299250 prefixEnd_5299250 2721062358338496893704199 := by
  unfold tailWord_5299250
  simp only [CollatzResearch.WordTrace]
  refine ⟨48319881512932441172801801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128853017367819843127471469 48319881512932441172801801)
  ·
    refine ⟨36239911134699330879601351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48319881512932441172801801 36239911134699330879601351)
    ·
      refine ⟨54359866702048996319402027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36239911134699330879601351 54359866702048996319402027)
      ·
        refine ⟨81539800053073494479103041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54359866702048996319402027 81539800053073494479103041)
        ·
          refine ⟨61154850039805120859327281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81539800053073494479103041 61154850039805120859327281)
          ·
            refine ⟨45866137529853840644495461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61154850039805120859327281 45866137529853840644495461)
            ·
              refine ⟨8599900786847595120842899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45866137529853840644495461 8599900786847595120842899)
              ·
                refine ⟨12899851180271392681264349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8599900786847595120842899 12899851180271392681264349)
                ·
                  refine ⟨4837444192601772255474131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12899851180271392681264349 4837444192601772255474131)
                  ·
                    refine ⟨7256166288902658383211197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4837444192601772255474131 7256166288902658383211197)
                    ·
                      refine ⟨2721062358338496893704199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7256166288902658383211197 2721062358338496893704199)
                      ·
                        rfl

theorem cell23_5299250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 1, 3, 1, 3].length) (baseStart_5299250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5299250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5299250 prefixEnd_5299250 := by exact prefixLift 5299250
  have htrace : WordTrace (prefixWord ++ tailWord_5299250) baseStart_5299250 baseEnd_5299250 := by
    simpa [prefixWord, tailWord_5299250, baseEnd_5299250] using wordTrace_append hprefix tailTrace_5299250
  have hstable : (prefixWord ++ tailWord_5299250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5299250).length < 2 ^ (prefixWord ++ tailWord_5299250).sum := by decide
  have hdescent : baseEnd_5299250 < baseStart_5299250 := by decide
  rcases family_descends (prefixWord ++ tailWord_5299250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5299276 : List Nat := [2, 2, 1, 3, 1, 1, 1, 1, 5, 1, 5]
def baseStart_5299276 : Nat := 118140960795 + 5299276 * 2 ^ 59
def prefixEnd_5299276 : Nat := 4983230072969 + 3 ^ 40 * 5299276 * 2
def baseEnd_5299276 : Nat := 2721075708835513791979079

theorem tailTrace_5299276 : CollatzResearch.WordTrace tailWord_5299276 prefixEnd_5299276 2721075708835513791979079 := by
  unfold tailWord_5299276
  simp only [CollatzResearch.WordTrace]
  refine ⟨96640237174817785565826841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128853649566423714087769121 96640237174817785565826841)
  ·
    refine ⟨72480177881113339174370131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96640237174817785565826841 72480177881113339174370131)
    ·
      refine ⟨108720266821670008761555197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72480177881113339174370131 108720266821670008761555197)
      ·
        refine ⟨40770100058126253285583199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108720266821670008761555197 40770100058126253285583199)
        ·
          refine ⟨61155150087189379928374799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40770100058126253285583199 61155150087189379928374799)
          ·
            refine ⟨91732725130784069892562199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61155150087189379928374799 91732725130784069892562199)
            ·
              refine ⟨137599087696176104838843299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91732725130784069892562199 137599087696176104838843299)
              ·
                refine ⟨206398631544264157258264949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 137599087696176104838843299 206398631544264157258264949)
                ·
                  refine ⟨19349871707274764742962339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 206398631544264157258264949 19349871707274764742962339)
                  ·
                    refine ⟨29024807560912147114443509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19349871707274764742962339 29024807560912147114443509)
                    ·
                      refine ⟨2721075708835513791979079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29024807560912147114443509 2721075708835513791979079)
                      ·
                        rfl

theorem cell23_5299276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_5299276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5299276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5299276 prefixEnd_5299276 := by exact prefixLift 5299276
  have htrace : WordTrace (prefixWord ++ tailWord_5299276) baseStart_5299276 baseEnd_5299276 := by
    simpa [prefixWord, tailWord_5299276, baseEnd_5299276] using wordTrace_append hprefix tailTrace_5299276
  have hstable : (prefixWord ++ tailWord_5299276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5299276).length < 2 ^ (prefixWord ++ tailWord_5299276).sum := by decide
  have hdescent : baseEnd_5299276 < baseStart_5299276 := by decide
  rcases family_descends (prefixWord ++ tailWord_5299276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5299294 : List Nat := [4, 4, 1, 1, 1, 1, 1, 1, 4, 3, 2]
def baseStart_5299294 : Nat := 118140960795 + 5299294 * 2 ^ 59
def prefixEnd_5299294 : Nat := 4983230072969 + 3 ^ 40 * 5299294 * 2
def baseEnd_5299294 : Nat := 2721084951487294721553997

theorem tailTrace_5299294 : CollatzResearch.WordTrace tailWord_5299294 prefixEnd_5299294 2721084951487294721553997 := by
  unfold tailWord_5299294
  simp only [CollatzResearch.WordTrace]
  refine ⟨24160141357946295025726117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128854087242380240137205957 24160141357946295025726117)
  ·
    refine ⟨4530026504614930317323647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24160141357946295025726117 4530026504614930317323647)
    ·
      refine ⟨6795039756922395475985471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4530026504614930317323647 6795039756922395475985471)
      ·
        refine ⟨10192559635383593213978207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6795039756922395475985471 10192559635383593213978207)
        ·
          refine ⟨15288839453075389820967311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10192559635383593213978207 15288839453075389820967311)
          ·
            refine ⟨22933259179613084731450967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15288839453075389820967311 22933259179613084731450967)
            ·
              refine ⟨34399888769419627097176451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22933259179613084731450967 34399888769419627097176451)
              ·
                refine ⟨51599833154129440645764677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34399888769419627097176451 51599833154129440645764677)
                ·
                  refine ⟨9674968716399270121080877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51599833154129440645764677 9674968716399270121080877)
                  ·
                    refine ⟨3628113268649726295405329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9674968716399270121080877 3628113268649726295405329)
                    ·
                      refine ⟨2721084951487294721553997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3628113268649726295405329 2721084951487294721553997)
                      ·
                        rfl

theorem cell23_5299294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_5299294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5299294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5299294 prefixEnd_5299294 := by exact prefixLift 5299294
  have htrace : WordTrace (prefixWord ++ tailWord_5299294) baseStart_5299294 baseEnd_5299294 := by
    simpa [prefixWord, tailWord_5299294, baseEnd_5299294] using wordTrace_append hprefix tailTrace_5299294
  have hstable : (prefixWord ++ tailWord_5299294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5299294).length < 2 ^ (prefixWord ++ tailWord_5299294).sum := by decide
  have hdescent : baseEnd_5299294 < baseStart_5299294 := by decide
  rcases family_descends (prefixWord ++ tailWord_5299294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5299357 : List Nat := [1, 4, 2, 1, 1, 2, 4, 2, 2, 1, 3]
def baseStart_5299357 : Nat := 118140960795 + 5299357 * 2 ^ 59
def prefixEnd_5299357 : Nat := 4983230072969 + 3 ^ 40 * 5299357 * 2
def baseEnd_5299357 : Nat := 2721117300768527975066207

theorem tailTrace_5299357 : CollatzResearch.WordTrace tailWord_5299357 prefixEnd_5299357 2721117300768527975066207 := by
  unfold tailWord_5299357
  simp only [CollatzResearch.WordTrace]
  refine ⟨193283428662342121965352325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128855619108228081310234883 193283428662342121965352325)
  ·
    refine ⟨36240642874189147868503561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 193283428662342121965352325 36240642874189147868503561)
    ·
      refine ⟨27180482155641860901377671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36240642874189147868503561 27180482155641860901377671)
      ·
        refine ⟨40770723233462791352066507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27180482155641860901377671 40770723233462791352066507)
        ·
          refine ⟨61156084850194187028099761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40770723233462791352066507 61156084850194187028099761)
          ·
            refine ⟨45867063637645640271074821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61156084850194187028099761 45867063637645640271074821)
            ·
              refine ⟨8600074432058557550826529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45867063637645640271074821 8600074432058557550826529)
              ·
                refine ⟨6450055824043918163119897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8600074432058557550826529 6450055824043918163119897)
                ·
                  refine ⟨4837541868032938622339923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6450055824043918163119897 4837541868032938622339923)
                  ·
                    refine ⟨7256312802049407933509885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4837541868032938622339923 7256312802049407933509885)
                    ·
                      refine ⟨2721117300768527975066207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7256312802049407933509885 2721117300768527975066207)
                      ·
                        rfl

theorem cell23_5299357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 2, 2, 1, 3].length) (baseStart_5299357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5299357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5299357 prefixEnd_5299357 := by exact prefixLift 5299357
  have htrace : WordTrace (prefixWord ++ tailWord_5299357) baseStart_5299357 baseEnd_5299357 := by
    simpa [prefixWord, tailWord_5299357, baseEnd_5299357] using wordTrace_append hprefix tailTrace_5299357
  have hstable : (prefixWord ++ tailWord_5299357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5299357).length < 2 ^ (prefixWord ++ tailWord_5299357).sum := by decide
  have hdescent : baseEnd_5299357 < baseStart_5299357 := by decide
  rcases family_descends (prefixWord ++ tailWord_5299357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5299358 : List Nat := [4, 3, 1, 1, 2, 1, 4, 2, 1, 2, 2]
def baseStart_5299358 : Nat := 118140960795 + 5299358 * 2 ^ 59
def prefixEnd_5299358 : Nat := 4983230072969 + 3 ^ 40 * 5299358 * 2
def baseEnd_5299358 : Nat := 2721117814249182471153703

theorem tailTrace_5299358 : CollatzResearch.WordTrace tailWord_5299358 prefixEnd_5299358 2721117814249182471153703 := by
  unfold tailWord_5299358
  simp only [CollatzResearch.WordTrace]
  refine ⟨24160433141917312392017341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128855643423558999424092485 24160433141917312392017341)
  ·
    refine ⟨9060162428218992147006503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24160433141917312392017341 9060162428218992147006503)
    ·
      refine ⟨13590243642328488220509755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9060162428218992147006503 13590243642328488220509755)
      ·
        refine ⟨20385365463492732330764633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13590243642328488220509755 20385365463492732330764633)
        ·
          refine ⟨15289024097619549248073475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20385365463492732330764633 15289024097619549248073475)
          ·
            refine ⟨22933536146429323872110213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15289024097619549248073475 22933536146429323872110213)
            ·
              refine ⟨4300038027455498226020665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22933536146429323872110213 4300038027455498226020665)
              ·
                refine ⟨3225028520591623669515499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4300038027455498226020665 3225028520591623669515499)
                ·
                  refine ⟨4837542780887435504273249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3225028520591623669515499 4837542780887435504273249)
                  ·
                    refine ⟨3628157085665576628204937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4837542780887435504273249 3628157085665576628204937)
                    ·
                      refine ⟨2721117814249182471153703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3628157085665576628204937 2721117814249182471153703)
                      ·
                        rfl

theorem cell23_5299358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 4, 2, 1, 2, 2].length) (baseStart_5299358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5299358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5299358 prefixEnd_5299358 := by exact prefixLift 5299358
  have htrace : WordTrace (prefixWord ++ tailWord_5299358) baseStart_5299358 baseEnd_5299358 := by
    simpa [prefixWord, tailWord_5299358, baseEnd_5299358] using wordTrace_append hprefix tailTrace_5299358
  have hstable : (prefixWord ++ tailWord_5299358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5299358).length < 2 ^ (prefixWord ++ tailWord_5299358).sum := by decide
  have hdescent : baseEnd_5299358 < baseStart_5299358 := by decide
  rcases family_descends (prefixWord ++ tailWord_5299358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5299367 : List Nat := [1, 1, 6, 2, 1, 1, 1, 2, 3, 3, 2]
def baseStart_5299367 : Nat := 118140960795 + 5299367 * 2 ^ 59
def prefixEnd_5299367 : Nat := 4983230072969 + 3 ^ 40 * 5299367 * 2
def baseEnd_5299367 : Nat := 2721122435575072935941161

theorem tailTrace_5299367 : CollatzResearch.WordTrace tailWord_5299367 prefixEnd_5299367 2721122435575072935941161 := by
  unfold tailWord_5299367
  simp only [CollatzResearch.WordTrace]
  refine ⟨193283793392305893673216355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128855862261537262448810903 193283793392305893673216355)
  ·
    refine ⟨289925690088458840509824533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193283793392305893673216355 289925690088458840509824533)
    ·
      refine ⟨13590266722896508148898025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 289925690088458840509824533 13590266722896508148898025)
      ·
        refine ⟨10192700042172381111673519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13590266722896508148898025 10192700042172381111673519)
        ·
          refine ⟨15289050063258571667510279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10192700042172381111673519 15289050063258571667510279)
          ·
            refine ⟨22933575094887857501265419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15289050063258571667510279 22933575094887857501265419)
            ·
              refine ⟨34400362642331786251898129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22933575094887857501265419 34400362642331786251898129)
              ·
                refine ⟨25800271981748839688923597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34400362642331786251898129 25800271981748839688923597)
                ·
                  refine ⟨9675101993155814883346349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25800271981748839688923597 9675101993155814883346349)
                  ·
                    refine ⟨3628163247433430581254881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9675101993155814883346349 3628163247433430581254881)
                    ·
                      refine ⟨2721122435575072935941161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3628163247433430581254881 2721122435575072935941161)
                      ·
                        rfl

theorem cell23_5299367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_5299367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5299367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5299367 prefixEnd_5299367 := by exact prefixLift 5299367
  have htrace : WordTrace (prefixWord ++ tailWord_5299367) baseStart_5299367 baseEnd_5299367 := by
    simpa [prefixWord, tailWord_5299367, baseEnd_5299367] using wordTrace_append hprefix tailTrace_5299367
  have hstable : (prefixWord ++ tailWord_5299367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5299367).length < 2 ^ (prefixWord ++ tailWord_5299367).sum := by decide
  have hdescent : baseEnd_5299367 < baseStart_5299367 := by decide
  rcases family_descends (prefixWord ++ tailWord_5299367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5299376 : List Nat := [2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 6]
def baseStart_5299376 : Nat := 118140960795 + 5299376 * 2 ^ 59
def prefixEnd_5299376 : Nat := 4983230072969 + 3 ^ 40 * 5299376 * 2
def baseEnd_5299376 : Nat := 2721127056900963400728619

theorem tailTrace_5299376 : CollatzResearch.WordTrace tailWord_5299376 prefixEnd_5299376 2721127056900963400728619 := by
  unfold tailWord_5299376
  simp only [CollatzResearch.WordTrace]
  refine ⟨96642060824636644105146991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128856081099515525473529321 96642060824636644105146991)
  ·
    refine ⟨144963091236954966157720487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96642060824636644105146991 144963091236954966157720487)
    ·
      refine ⟨217444636855432449236580731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144963091236954966157720487 217444636855432449236580731)
      ·
        refine ⟨326166955283148673854871097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217444636855432449236580731 326166955283148673854871097)
        ·
          refine ⟨244625216462361505391153323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 326166955283148673854871097 244625216462361505391153323)
          ·
            refine ⟨366937824693542258086729985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 244625216462361505391153323 366937824693542258086729985)
            ·
              refine ⟨275203368520156693565047489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 366937824693542258086729985 275203368520156693565047489)
              ·
                refine ⟨206402526390117520173785617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 275203368520156693565047489 206402526390117520173785617)
                ·
                  refine ⟨154801894792588140130339213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 206402526390117520173785617 154801894792588140130339213)
                  ·
                    refine ⟨58050710547220552548877205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 154801894792588140130339213 58050710547220552548877205)
                    ·
                      refine ⟨2721127056900963400728619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58050710547220552548877205 2721127056900963400728619)
                      ·
                        rfl

theorem cell23_5299376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 6].length) (baseStart_5299376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5299376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5299376 prefixEnd_5299376 := by exact prefixLift 5299376
  have htrace : WordTrace (prefixWord ++ tailWord_5299376) baseStart_5299376 baseEnd_5299376 := by
    simpa [prefixWord, tailWord_5299376, baseEnd_5299376] using wordTrace_append hprefix tailTrace_5299376
  have hstable : (prefixWord ++ tailWord_5299376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5299376).length < 2 ^ (prefixWord ++ tailWord_5299376).sum := by decide
  have hdescent : baseEnd_5299376 < baseStart_5299376 := by decide
  rcases family_descends (prefixWord ++ tailWord_5299376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5299383 : List Nat := [1, 1, 3, 1, 4, 1, 1, 2, 2, 4, 3]
def baseStart_5299383 : Nat := 118140960795 + 5299383 * 2 ^ 59
def prefixEnd_5299383 : Nat := 4983230072969 + 3 ^ 40 * 5299383 * 2
def baseEnd_5299383 : Nat := 2721130651265544873341087

theorem tailTrace_5299383 : CollatzResearch.WordTrace tailWord_5299383 prefixEnd_5299383 2721130651265544873341087 := by
  unfold tailWord_5299383
  simp only [CollatzResearch.WordTrace]
  refine ⟨193284376960247928405798803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128856251306831952270532535 193284376960247928405798803)
  ·
    refine ⟨289926565440371892608698205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193284376960247928405798803 289926565440371892608698205)
    ·
      refine ⟨108722462040139459728261827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 289926565440371892608698205 108722462040139459728261827)
      ·
        refine ⟨163083693060209189592392741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108722462040139459728261827 163083693060209189592392741)
        ·
          refine ⟨30578192448789223048573639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 163083693060209189592392741 30578192448789223048573639)
          ·
            refine ⟨45867288673183834572860459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30578192448789223048573639 45867288673183834572860459)
            ·
              refine ⟨68800933009775751859290689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45867288673183834572860459 68800933009775751859290689)
              ·
                refine ⟨51600699757331813894468017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68800933009775751859290689 51600699757331813894468017)
                ·
                  refine ⟨38700524817998860420851013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51600699757331813894468017 38700524817998860420851013)
                  ·
                    refine ⟨7256348403374786328909565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38700524817998860420851013 7256348403374786328909565)
                    ·
                      refine ⟨2721130651265544873341087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7256348403374786328909565 2721130651265544873341087)
                      ·
                        rfl

theorem cell23_5299383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 2, 4, 3].length) (baseStart_5299383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5299383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5299383 prefixEnd_5299383 := by exact prefixLift 5299383
  have htrace : WordTrace (prefixWord ++ tailWord_5299383) baseStart_5299383 baseEnd_5299383 := by
    simpa [prefixWord, tailWord_5299383, baseEnd_5299383] using wordTrace_append hprefix tailTrace_5299383
  have hstable : (prefixWord ++ tailWord_5299383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5299383).length < 2 ^ (prefixWord ++ tailWord_5299383).sum := by decide
  have hdescent : baseEnd_5299383 < baseStart_5299383 := by decide
  rcases family_descends (prefixWord ++ tailWord_5299383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5299431 : List Nat := [1, 1, 5, 3, 3, 1, 1, 1, 1, 4, 2]
def baseStart_5299431 : Nat := 118140960795 + 5299431 * 2 ^ 59
def prefixEnd_5299431 : Nat := 4983230072969 + 3 ^ 40 * 5299431 * 2
def baseEnd_5299431 : Nat := 2721155298336960685540867

theorem tailTrace_5299431 : CollatzResearch.WordTrace tailWord_5299431 prefixEnd_5299431 2721155298336960685540867 := by
  unfold tailWord_5299431
  simp only [CollatzResearch.WordTrace]
  refine ⟨193286127664074032603546147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128857418442716021735697431 193286127664074032603546147)
  ·
    refine ⟨289929191496111048905319221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193286127664074032603546147 289929191496111048905319221)
    ·
      refine ⟨27180861702760410834873677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 289929191496111048905319221 27180861702760410834873677)
      ·
        refine ⟨10192823138535154063077629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27180861702760410834873677 10192823138535154063077629)
        ·
          refine ⟨3822308676950682773654111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10192823138535154063077629 3822308676950682773654111)
          ·
            refine ⟨5733463015426024160481167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3822308676950682773654111 5733463015426024160481167)
            ·
              refine ⟨8600194523139036240721751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5733463015426024160481167 8600194523139036240721751)
              ·
                refine ⟨12900291784708554361082627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8600194523139036240721751 12900291784708554361082627)
                ·
                  refine ⟨19350437677062831541623941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12900291784708554361082627 19350437677062831541623941)
                  ·
                    refine ⟨3628207064449280914054489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19350437677062831541623941 3628207064449280914054489)
                    ·
                      refine ⟨2721155298336960685540867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3628207064449280914054489 2721155298336960685540867)
                      ·
                        rfl

theorem cell23_5299431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_5299431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5299431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5299431 prefixEnd_5299431 := by exact prefixLift 5299431
  have htrace : WordTrace (prefixWord ++ tailWord_5299431) baseStart_5299431 baseEnd_5299431 := by
    simpa [prefixWord, tailWord_5299431, baseEnd_5299431] using wordTrace_append hprefix tailTrace_5299431
  have hstable : (prefixWord ++ tailWord_5299431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5299431).length < 2 ^ (prefixWord ++ tailWord_5299431).sum := by decide
  have hdescent : baseEnd_5299431 < baseStart_5299431 := by decide
  rcases family_descends (prefixWord ++ tailWord_5299431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5299454 : List Nat := [4, 2, 2, 1, 1, 4, 1, 3, 5]
def baseStart_5299454 : Nat := 118140960795 + 5299454 * 2 ^ 59
def prefixEnd_5299454 : Nat := 4983230072969 + 3 ^ 40 * 5299454 * 2
def baseEnd_5299454 : Nat := 302351900932446010617029

theorem tailTrace_5299454 : CollatzResearch.WordTrace tailWord_5299454 prefixEnd_5299454 302351900932446010617029 := by
  unfold tailWord_5299454
  simp only [CollatzResearch.WordTrace]
  refine ⟨24160870817873838441454177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128857977695327138354422277 24160870817873838441454177)
  ·
    refine ⟨18120653113405378831090633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24160870817873838441454177 18120653113405378831090633)
    ·
      refine ⟨13590489835054034123317975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18120653113405378831090633 13590489835054034123317975)
      ·
        refine ⟨20385734752581051184976963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13590489835054034123317975 20385734752581051184976963)
        ·
          refine ⟨30578602128871576777465445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20385734752581051184976963 30578602128871576777465445)
          ·
            refine ⟨5733487899163420645774771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30578602128871576777465445 5733487899163420645774771)
            ·
              refine ⟨8600231848745130968662157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5733487899163420645774771 8600231848745130968662157)
              ·
                refine ⟨3225086943279424113248309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8600231848745130968662157 3225086943279424113248309)
                ·
                  refine ⟨302351900932446010617029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3225086943279424113248309 302351900932446010617029)
                  ·
                    rfl

theorem cell23_5299454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 3, 5].length) (baseStart_5299454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5299454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5299454 prefixEnd_5299454 := by exact prefixLift 5299454
  have htrace : WordTrace (prefixWord ++ tailWord_5299454) baseStart_5299454 baseEnd_5299454 := by
    simpa [prefixWord, tailWord_5299454, baseEnd_5299454] using wordTrace_append hprefix tailTrace_5299454
  have hstable : (prefixWord ++ tailWord_5299454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5299454).length < 2 ^ (prefixWord ++ tailWord_5299454).sum := by decide
  have hdescent : baseEnd_5299454 < baseStart_5299454 := by decide
  rcases family_descends (prefixWord ++ tailWord_5299454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5299470 : List Nat := [4, 1, 1, 2, 1, 3, 1, 1, 4, 1, 4]
def baseStart_5299470 : Nat := 118140960795 + 5299470 * 2 ^ 59
def prefixEnd_5299470 : Nat := 4983230072969 + 3 ^ 40 * 5299470 * 2
def baseEnd_5299470 : Nat := 2721175324082486032953187

theorem tailTrace_5299470 : CollatzResearch.WordTrace tailWord_5299470 prefixEnd_5299470 2721175324082486032953187 := by
  unfold tailWord_5299470
  simp only [CollatzResearch.WordTrace]
  refine ⟨24160943763866592783026983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128858366740621828176143909 24160943763866592783026983)
  ·
    refine ⟨36241415645799889174540475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24160943763866592783026983 36241415645799889174540475)
    ·
      refine ⟨54362123468699833761810713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36241415645799889174540475 54362123468699833761810713)
      ·
        refine ⟨40771592601524875321358035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54362123468699833761810713 40771592601524875321358035)
        ·
          refine ⟨61157388902287312982037053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40771592601524875321358035 61157388902287312982037053)
          ·
            refine ⟨22934020838357742368263895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61157388902287312982037053 22934020838357742368263895)
            ·
              refine ⟨34401031257536613552395843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22934020838357742368263895 34401031257536613552395843)
              ·
                refine ⟨51601546886304920328593765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34401031257536613552395843 51601546886304920328593765)
                ·
                  refine ⟨9675290041182172561611331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51601546886304920328593765 9675290041182172561611331)
                  ·
                    refine ⟨14512935061773258842416997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9675290041182172561611331 14512935061773258842416997)
                    ·
                      refine ⟨2721175324082486032953187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14512935061773258842416997 2721175324082486032953187)
                      ·
                        rfl

theorem cell23_5299470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 4, 1, 4].length) (baseStart_5299470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5299470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5299470 prefixEnd_5299470 := by exact prefixLift 5299470
  have htrace : WordTrace (prefixWord ++ tailWord_5299470) baseStart_5299470 baseEnd_5299470 := by
    simpa [prefixWord, tailWord_5299470, baseEnd_5299470] using wordTrace_append hprefix tailTrace_5299470
  have hstable : (prefixWord ++ tailWord_5299470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5299470).length < 2 ^ (prefixWord ++ tailWord_5299470).sum := by decide
  have hdescent : baseEnd_5299470 < baseStart_5299470 := by decide
  rcases family_descends (prefixWord ++ tailWord_5299470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5299507 : List Nat := [1, 1, 1, 2, 5, 3, 2, 1, 2, 2, 3]
def baseStart_5299507 : Nat := 118140960795 + 5299507 * 2 ^ 59
def prefixEnd_5299507 : Nat := 4983230072969 + 3 ^ 40 * 5299507 * 2
def baseEnd_5299507 : Nat := 2721194322866702388190517

theorem tailTrace_5299507 : CollatzResearch.WordTrace tailWord_5299507 prefixEnd_5299507 2721194322866702388190517 := by
  unfold tailWord_5299507
  simp only [CollatzResearch.WordTrace]
  refine ⟨193288899611798697583312775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128859266407865798388875183 193288899611798697583312775)
  ·
    refine ⟨289933349417698046374969163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193288899611798697583312775 289933349417698046374969163)
    ·
      refine ⟨434900024126547069562453745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289933349417698046374969163 434900024126547069562453745)
      ·
        refine ⟨326175018094910302171840309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 434900024126547069562453745 326175018094910302171840309)
        ·
          refine ⟨30578907946397840828610029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 326175018094910302171840309 30578907946397840828610029)
          ·
            refine ⟨11467090479899190310728761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30578907946397840828610029 11467090479899190310728761)
            ·
              refine ⟨8600317859924392733046571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11467090479899190310728761 8600317859924392733046571)
              ·
                refine ⟨12900476789886589099569857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8600317859924392733046571 12900476789886589099569857)
                ·
                  refine ⟨9675357592414941824677393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12900476789886589099569857 9675357592414941824677393)
                  ·
                    refine ⟨7256518194311206368508045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9675357592414941824677393 7256518194311206368508045)
                    ·
                      refine ⟨2721194322866702388190517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7256518194311206368508045 2721194322866702388190517)
                      ·
                        rfl

theorem cell23_5299507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 1, 2, 2, 3].length) (baseStart_5299507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5299507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5299507 prefixEnd_5299507 := by exact prefixLift 5299507
  have htrace : WordTrace (prefixWord ++ tailWord_5299507) baseStart_5299507 baseEnd_5299507 := by
    simpa [prefixWord, tailWord_5299507, baseEnd_5299507] using wordTrace_append hprefix tailTrace_5299507
  have hstable : (prefixWord ++ tailWord_5299507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5299507).length < 2 ^ (prefixWord ++ tailWord_5299507).sum := by decide
  have hdescent : baseEnd_5299507 < baseStart_5299507 := by decide
  rcases family_descends (prefixWord ++ tailWord_5299507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5299524 : List Nat := [2, 3, 4, 1, 1, 1, 2, 2, 2, 2, 3]
def baseStart_5299524 : Nat := 118140960795 + 5299524 * 2 ^ 59
def prefixEnd_5299524 : Nat := 4983230072969 + 3 ^ 40 * 5299524 * 2
def baseEnd_5299524 : Nat := 2721203052037828821677939

theorem tailTrace_5299524 : CollatzResearch.WordTrace tailWord_5299524 prefixEnd_5299524 2721203052037828821677939 := by
  unfold tailWord_5299524
  simp only [CollatzResearch.WordTrace]
  refine ⟨96644759826368554743340813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128859679768491406324454417 96644759826368554743340813)
  ·
    refine ⟨36241784934888208028752805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96644759826368554743340813 36241784934888208028752805)
    ·
      refine ⟨6795334675291539005391151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36241784934888208028752805 6795334675291539005391151)
      ·
        refine ⟨10193002012937308508086727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6795334675291539005391151 10193002012937308508086727)
        ·
          refine ⟨15289503019405962762130091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10193002012937308508086727 15289503019405962762130091)
          ·
            refine ⟨22934254529108944143195137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15289503019405962762130091 22934254529108944143195137)
            ·
              refine ⟨17200690896831708107396353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22934254529108944143195137 17200690896831708107396353)
              ·
                refine ⟨12900518172623781080547265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17200690896831708107396353 12900518172623781080547265)
                ·
                  refine ⟨9675388629467835810410449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12900518172623781080547265 9675388629467835810410449)
                  ·
                    refine ⟨7256541472100876857807837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9675388629467835810410449 7256541472100876857807837)
                    ·
                      refine ⟨2721203052037828821677939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7256541472100876857807837 2721203052037828821677939)
                      ·
                        rfl

theorem cell23_5299524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_5299524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5299524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5299524 prefixEnd_5299524 := by exact prefixLift 5299524
  have htrace : WordTrace (prefixWord ++ tailWord_5299524) baseStart_5299524 baseEnd_5299524 := by
    simpa [prefixWord, tailWord_5299524, baseEnd_5299524] using wordTrace_append hprefix tailTrace_5299524
  have hstable : (prefixWord ++ tailWord_5299524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5299524).length < 2 ^ (prefixWord ++ tailWord_5299524).sum := by decide
  have hdescent : baseEnd_5299524 < baseStart_5299524 := by decide
  rcases family_descends (prefixWord ++ tailWord_5299524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5299537 : List Nat := [1, 2, 2, 1, 4, 1, 2, 3, 3, 1, 3]
def baseStart_5299537 : Nat := 118140960795 + 5299537 * 2 ^ 59
def prefixEnd_5299537 : Nat := 4983230072969 + 3 ^ 40 * 5299537 * 2
def baseEnd_5299537 : Nat := 2721209727286337270815379

theorem tailTrace_5299537 : CollatzResearch.WordTrace tailWord_5299537 prefixEnd_5299537 2721209727286337270815379 := by
  unfold tailWord_5299537
  simp only [CollatzResearch.WordTrace]
  refine ⟨193289993801690012706904865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128859995867793341804603243 193289993801690012706904865)
  ·
    refine ⟨144967495351267509530178649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193289993801690012706904865 144967495351267509530178649)
    ·
      refine ⟨108725621513450632147633987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144967495351267509530178649 108725621513450632147633987)
      ·
        refine ⟨163088432270175948221450981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108725621513450632147633987 163088432270175948221450981)
        ·
          refine ⟨30579081050657990291522059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 163088432270175948221450981 30579081050657990291522059)
          ·
            refine ⟨45868621575986985437283089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30579081050657990291522059 45868621575986985437283089)
            ·
              refine ⟨34401466181990239077962317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45868621575986985437283089 34401466181990239077962317)
              ·
                refine ⟨12900549818246339654235869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34401466181990239077962317 12900549818246339654235869)
                ·
                  refine ⟨4837706181842377370338451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12900549818246339654235869 4837706181842377370338451)
                  ·
                    refine ⟨7256559272763566055507677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4837706181842377370338451 7256559272763566055507677)
                    ·
                      refine ⟨2721209727286337270815379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7256559272763566055507677 2721209727286337270815379)
                      ·
                        rfl

theorem cell23_5299537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 3, 3, 1, 3].length) (baseStart_5299537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5299537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5299537 prefixEnd_5299537 := by exact prefixLift 5299537
  have htrace : WordTrace (prefixWord ++ tailWord_5299537) baseStart_5299537 baseEnd_5299537 := by
    simpa [prefixWord, tailWord_5299537, baseEnd_5299537] using wordTrace_append hprefix tailTrace_5299537
  have hstable : (prefixWord ++ tailWord_5299537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5299537).length < 2 ^ (prefixWord ++ tailWord_5299537).sum := by decide
  have hdescent : baseEnd_5299537 < baseStart_5299537 := by decide
  rcases family_descends (prefixWord ++ tailWord_5299537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5299540 : List Nat := [2, 4, 1, 1, 2, 1, 1, 1, 5, 5]
def baseStart_5299540 : Nat := 118140960795 + 5299540 * 2 ^ 59
def prefixEnd_5299540 : Nat := 4983230072969 + 3 ^ 40 * 5299540 * 2
def baseEnd_5299540 : Nat := 907070422576100253025955

theorem tailTrace_5299540 : CollatzResearch.WordTrace tailWord_5299540 prefixEnd_5299540 907070422576100253025955 := by
  unfold tailWord_5299540
  simp only [CollatzResearch.WordTrace]
  refine ⟨96645051610339572109632037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128860068813786096146176049 96645051610339572109632037)
  ·
    refine ⟨18120947176938669770556007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96645051610339572109632037 18120947176938669770556007)
    ·
      refine ⟨27181420765408004655834011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18120947176938669770556007 27181420765408004655834011)
      ·
        refine ⟨40772131148112006983751017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27181420765408004655834011 40772131148112006983751017)
        ·
          refine ⟨30579098361084005237813263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40772131148112006983751017 30579098361084005237813263)
          ·
            refine ⟨45868647541626007856719895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30579098361084005237813263 45868647541626007856719895)
            ·
              refine ⟨68802971312439011785079843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45868647541626007856719895 68802971312439011785079843)
              ·
                refine ⟨103204456968658517677619765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68802971312439011785079843 103204456968658517677619765)
                ·
                  refine ⟨9675417840811736032276853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 103204456968658517677619765 9675417840811736032276853)
                  ·
                    refine ⟨907070422576100253025955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9675417840811736032276853 907070422576100253025955)
                    ·
                      rfl

theorem cell23_5299540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 5, 5].length) (baseStart_5299540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5299540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5299540 prefixEnd_5299540 := by exact prefixLift 5299540
  have htrace : WordTrace (prefixWord ++ tailWord_5299540) baseStart_5299540 baseEnd_5299540 := by
    simpa [prefixWord, tailWord_5299540, baseEnd_5299540] using wordTrace_append hprefix tailTrace_5299540
  have hstable : (prefixWord ++ tailWord_5299540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5299540).length < 2 ^ (prefixWord ++ tailWord_5299540).sum := by decide
  have hdescent : baseEnd_5299540 < baseStart_5299540 := by decide
  rcases family_descends (prefixWord ++ tailWord_5299540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5299554 : List Nat := [3, 3, 2, 1, 1, 1, 3, 2, 3, 1, 3]
def baseStart_5299554 : Nat := 118140960795 + 5299554 * 2 ^ 59
def prefixEnd_5299554 : Nat := 4983230072969 + 3 ^ 40 * 5299554 * 2
def baseEnd_5299554 : Nat := 2721218456457463704302801

theorem tailTrace_5299554 : CollatzResearch.WordTrace tailWord_5299554 prefixEnd_5299554 2721218456457463704302801 := by
  unfold tailWord_5299554
  simp only [CollatzResearch.WordTrace]
  refine ⟨48322653460657106152568429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128860409228418949740182477 48322653460657106152568429)
  ·
    refine ⟨18120995047746414807213161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48322653460657106152568429 18120995047746414807213161)
    ·
      refine ⟨13590746285809811105409871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18120995047746414807213161 13590746285809811105409871)
      ·
        refine ⟨20386119428714716658114807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13590746285809811105409871 20386119428714716658114807)
        ·
          refine ⟨30579179143072074987172211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20386119428714716658114807 30579179143072074987172211)
          ·
            refine ⟨45868768714608112480758317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30579179143072074987172211 45868768714608112480758317)
            ·
              refine ⟨17200788267978042180284369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45868768714608112480758317 17200788267978042180284369)
              ·
                refine ⟨12900591200983531635213277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17200788267978042180284369 12900591200983531635213277)
                ·
                  refine ⟨4837721700368824363204979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12900591200983531635213277 4837721700368824363204979)
                  ·
                    refine ⟨7256582550553236544807469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4837721700368824363204979 7256582550553236544807469)
                    ·
                      refine ⟨2721218456457463704302801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7256582550553236544807469 2721218456457463704302801)
                      ·
                        rfl

theorem cell23_5299554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 2, 3, 1, 3].length) (baseStart_5299554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5299554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5299554 prefixEnd_5299554 := by exact prefixLift 5299554
  have htrace : WordTrace (prefixWord ++ tailWord_5299554) baseStart_5299554 baseEnd_5299554 := by
    simpa [prefixWord, tailWord_5299554, baseEnd_5299554] using wordTrace_append hprefix tailTrace_5299554
  have hstable : (prefixWord ++ tailWord_5299554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5299554).length < 2 ^ (prefixWord ++ tailWord_5299554).sum := by decide
  have hdescent : baseEnd_5299554 < baseStart_5299554 := by decide
  rcases family_descends (prefixWord ++ tailWord_5299554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5299563 : List Nat := [1, 1, 1, 1, 2, 2, 2, 1, 2, 5, 5]
def baseStart_5299563 : Nat := 118140960795 + 5299563 * 2 ^ 59
def prefixEnd_5299563 : Nat := 4983230072969 + 3 ^ 40 * 5299563 * 2
def baseEnd_5299563 : Nat := 2721223077783354169090259

theorem tailTrace_5299563 : CollatzResearch.WordTrace tailWord_5299563 prefixEnd_5299563 2721223077783354169090259 := by
  unfold tailWord_5299563
  simp only [CollatzResearch.WordTrace]
  refine ⟨193290942099595819147351343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128860628066397212764900895 193290942099595819147351343)
  ·
    refine ⟨289936413149393728721027015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193290942099595819147351343 289936413149393728721027015)
    ·
      refine ⟨434904619724090593081540523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289936413149393728721027015 434904619724090593081540523)
      ·
        refine ⟨652356929586135889622310785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 434904619724090593081540523 652356929586135889622310785)
        ·
          refine ⟨489267697189601917216733089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 652356929586135889622310785 489267697189601917216733089)
          ·
            refine ⟨366950772892201437912549817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 489267697189601917216733089 366950772892201437912549817)
            ·
              refine ⟨275213079669151078434412363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 366950772892201437912549817 275213079669151078434412363)
              ·
                refine ⟨412819619503726617651618545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 275213079669151078434412363 412819619503726617651618545)
                ·
                  refine ⟨309614714627794963238713909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 412819619503726617651618545 309614714627794963238713909)
                  ·
                    refine ⟨29026379496355777803629429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 309614714627794963238713909 29026379496355777803629429)
                    ·
                      refine ⟨2721223077783354169090259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29026379496355777803629429 2721223077783354169090259)
                      ·
                        rfl

theorem cell23_5299563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 5, 5].length) (baseStart_5299563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5299563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5299563 prefixEnd_5299563 := by exact prefixLift 5299563
  have htrace : WordTrace (prefixWord ++ tailWord_5299563) baseStart_5299563 baseEnd_5299563 := by
    simpa [prefixWord, tailWord_5299563, baseEnd_5299563] using wordTrace_append hprefix tailTrace_5299563
  have hstable : (prefixWord ++ tailWord_5299563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5299563).length < 2 ^ (prefixWord ++ tailWord_5299563).sum := by decide
  have hdescent : baseEnd_5299563 < baseStart_5299563 := by decide
  rcases family_descends (prefixWord ++ tailWord_5299563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5299564 : List Nat := [2, 2, 1, 1, 5, 1, 3, 1, 2, 3, 2]
def baseStart_5299564 : Nat := 118140960795 + 5299564 * 2 ^ 59
def prefixEnd_5299564 : Nat := 4983230072969 + 3 ^ 40 * 5299564 * 2
def baseEnd_5299564 : Nat := 2721223591264008665177755

theorem tailTrace_5299564 : CollatzResearch.WordTrace tailWord_5299564 prefixEnd_5299564 2721223591264008665177755 := by
  unfold tailWord_5299564
  simp only [CollatzResearch.WordTrace]
  refine ⟨96645489286296098159068873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128860652381728130878758497 96645489286296098159068873)
  ·
    refine ⟨72484116964722073619301655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96645489286296098159068873 72484116964722073619301655)
    ·
      refine ⟨108726175447083110428952483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72484116964722073619301655 108726175447083110428952483)
      ·
        refine ⟨163089263170624665643428725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108726175447083110428952483 163089263170624665643428725)
        ·
          refine ⟨15289618422246062404071443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 163089263170624665643428725 15289618422246062404071443)
          ·
            refine ⟨22934427633369093606107165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15289618422246062404071443 22934427633369093606107165)
            ·
              refine ⟨8600410362513410102290187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22934427633369093606107165 8600410362513410102290187)
              ·
                refine ⟨12900615543770115153435281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8600410362513410102290187 12900615543770115153435281)
                ·
                  refine ⟨9675461657827586365076461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12900615543770115153435281 9675461657827586365076461)
                  ·
                    refine ⟨3628298121685344886903673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9675461657827586365076461 3628298121685344886903673)
                    ·
                      refine ⟨2721223591264008665177755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3628298121685344886903673 2721223591264008665177755)
                      ·
                        rfl

theorem cell23_5299564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 3, 2].length) (baseStart_5299564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5299564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5299564 prefixEnd_5299564 := by exact prefixLift 5299564
  have htrace : WordTrace (prefixWord ++ tailWord_5299564) baseStart_5299564 baseEnd_5299564 := by
    simpa [prefixWord, tailWord_5299564, baseEnd_5299564] using wordTrace_append hprefix tailTrace_5299564
  have hstable : (prefixWord ++ tailWord_5299564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5299564).length < 2 ^ (prefixWord ++ tailWord_5299564).sum := by decide
  have hdescent : baseEnd_5299564 < baseStart_5299564 := by decide
  rcases family_descends (prefixWord ++ tailWord_5299564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5299570 : List Nat := [3, 2, 1, 2, 1, 2, 1, 4, 1, 6]
def baseStart_5299570 : Nat := 118140960795 + 5299570 * 2 ^ 59
def prefixEnd_5299570 : Nat := 4983230072969 + 3 ^ 40 * 5299570 * 2
def baseEnd_5299570 : Nat := 907075557382645213900909

theorem tailTrace_5299570 : CollatzResearch.WordTrace tailWord_5299570 prefixEnd_5299570 907075557382645213900909 := by
  unfold tailWord_5299570
  simp only [CollatzResearch.WordTrace]
  refine ⟨48322799352642614835714041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128860798273713639561904109 48322799352642614835714041)
  ·
    refine ⟨36242099514481961126785531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48322799352642614835714041 36242099514481961126785531)
    ·
      refine ⟨54363149271722941690178297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36242099514481961126785531 54363149271722941690178297)
      ·
        refine ⟨40772361953792206267633723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54363149271722941690178297 40772361953792206267633723)
        ·
          refine ⟨61158542930688309401450585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40772361953792206267633723 61158542930688309401450585)
          ·
            refine ⟨45868907198016232051087939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61158542930688309401450585 45868907198016232051087939)
            ·
              refine ⟨68803360797024348076631909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45868907198016232051087939 68803360797024348076631909)
              ·
                refine ⟨12900630149442065264368483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68803360797024348076631909 12900630149442065264368483)
                ·
                  refine ⟨19350945224163097896552725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12900630149442065264368483 19350945224163097896552725)
                  ·
                    refine ⟨907075557382645213900909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19350945224163097896552725 907075557382645213900909)
                    ·
                      rfl

theorem cell23_5299570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 4, 1, 6].length) (baseStart_5299570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5299570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5299570 prefixEnd_5299570 := by exact prefixLift 5299570
  have htrace : WordTrace (prefixWord ++ tailWord_5299570) baseStart_5299570 baseEnd_5299570 := by
    simpa [prefixWord, tailWord_5299570, baseEnd_5299570] using wordTrace_append hprefix tailTrace_5299570
  have hstable : (prefixWord ++ tailWord_5299570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5299570).length < 2 ^ (prefixWord ++ tailWord_5299570).sum := by decide
  have hdescent : baseEnd_5299570 < baseStart_5299570 := by decide
  rcases family_descends (prefixWord ++ tailWord_5299570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5299580 : List Nat := [2, 2, 2, 1, 1, 1, 4, 3, 1, 1, 5]
def baseStart_5299580 : Nat := 118140960795 + 5299580 * 2 ^ 59
def prefixEnd_5299580 : Nat := 4983230072969 + 3 ^ 40 * 5299580 * 2
def baseEnd_5299580 : Nat := 2721231806954480602577681

theorem tailTrace_5299580 : CollatzResearch.WordTrace tailWord_5299580 prefixEnd_5299580 2721231806954480602577681 := by
  unfold tailWord_5299580
  simp only [CollatzResearch.WordTrace]
  refine ⟨96645781070267115525360097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128861041427022820700480129 96645781070267115525360097)
  ·
    refine ⟨72484335802700336644020073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96645781070267115525360097 72484335802700336644020073)
    ·
      refine ⟨54363251852025252483015055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72484335802700336644020073 54363251852025252483015055)
      ·
        refine ⟨81544877778037878724522583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54363251852025252483015055 81544877778037878724522583)
        ·
          refine ⟨122317316667056818086783875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81544877778037878724522583 122317316667056818086783875)
          ·
            refine ⟨183475975000585227130175813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122317316667056818086783875 183475975000585227130175813)
            ·
              refine ⟨34401745312609730086907965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 183475975000585227130175813 34401745312609730086907965)
              ·
                refine ⟨12900654492228648782590487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34401745312609730086907965 12900654492228648782590487)
                ·
                  refine ⟨19350981738342973173885731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12900654492228648782590487 19350981738342973173885731)
                  ·
                    refine ⟨29026472607514459760828597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19350981738342973173885731 29026472607514459760828597)
                    ·
                      refine ⟨2721231806954480602577681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29026472607514459760828597 2721231806954480602577681)
                      ·
                        rfl

theorem cell23_5299580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 3, 1, 1, 5].length) (baseStart_5299580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5299580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5299580 prefixEnd_5299580 := by exact prefixLift 5299580
  have htrace : WordTrace (prefixWord ++ tailWord_5299580) baseStart_5299580 baseEnd_5299580 := by
    simpa [prefixWord, tailWord_5299580, baseEnd_5299580] using wordTrace_append hprefix tailTrace_5299580
  have hstable : (prefixWord ++ tailWord_5299580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5299580).length < 2 ^ (prefixWord ++ tailWord_5299580).sum := by decide
  have hdescent : baseEnd_5299580 < baseStart_5299580 := by decide
  rcases family_descends (prefixWord ++ tailWord_5299580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5299587 : List Nat := [1, 1, 1, 3, 5, 2, 1, 1, 4, 4]
def baseStart_5299587 : Nat := 118140960795 + 5299587 * 2 ^ 59
def prefixEnd_5299587 : Nat := 4983230072969 + 3 ^ 40 * 5299587 * 2
def baseEnd_5299587 : Nat := 907078467106354025063383

theorem tailTrace_5299587 : CollatzResearch.WordTrace tailWord_5299587 prefixEnd_5299587 907078467106354025063383 := by
  unfold tailWord_5299587
  simp only [CollatzResearch.WordTrace]
  refine ⟨193291817451508871246225015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128861211634339247497483343 193291817451508871246225015)
  ·
    refine ⟨289937726177263306869337523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193291817451508871246225015 289937726177263306869337523)
    ·
      refine ⟨434906589265894960304006285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289937726177263306869337523 434906589265894960304006285)
      ·
        refine ⟨163089970974710610114002357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 434906589265894960304006285 163089970974710610114002357)
        ·
          refine ⟨15289684778879119698187721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 163089970974710610114002357 15289684778879119698187721)
          ·
            refine ⟨11467263584159339773640791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15289684778879119698187721 11467263584159339773640791)
            ·
              refine ⟨17200895376239009660461187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11467263584159339773640791 17200895376239009660461187)
              ·
                refine ⟨25801343064358514490691781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17200895376239009660461187 25801343064358514490691781)
                ·
                  refine ⟨4837751824567221467004709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25801343064358514490691781 4837751824567221467004709)
                  ·
                    refine ⟨907078467106354025063383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4837751824567221467004709 907078467106354025063383)
                    ·
                      rfl

theorem cell23_5299587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 1, 4, 4].length) (baseStart_5299587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5299587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5299587 prefixEnd_5299587 := by exact prefixLift 5299587
  have htrace : WordTrace (prefixWord ++ tailWord_5299587) baseStart_5299587 baseEnd_5299587 := by
    simpa [prefixWord, tailWord_5299587, baseEnd_5299587] using wordTrace_append hprefix tailTrace_5299587
  have hstable : (prefixWord ++ tailWord_5299587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5299587).length < 2 ^ (prefixWord ++ tailWord_5299587).sum := by decide
  have hdescent : baseEnd_5299587 < baseStart_5299587 := by decide
  rcases family_descends (prefixWord ++ tailWord_5299587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5299604 : List Nat := [2, 4, 2, 1, 2, 3, 1, 1, 1, 6]
def baseStart_5299604 : Nat := 118140960795 + 5299604 * 2 ^ 59
def prefixEnd_5299604 : Nat := 4983230072969 + 3 ^ 40 * 5299604 * 2
def baseEnd_5299604 : Nat := 907081376830062836225857

theorem tailTrace_5299604 : CollatzResearch.WordTrace tailWord_5299604 prefixEnd_5299604 907081376830062836225857 := by
  unfold tailWord_5299604
  simp only [CollatzResearch.WordTrace]
  refine ⟨96646218746223641574796933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128861624994964855433062577 96646218746223641574796933)
  ·
    refine ⟨18121166014916932795274425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96646218746223641574796933 18121166014916932795274425)
    ·
      refine ⟨13590874511187699596455819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18121166014916932795274425 13590874511187699596455819)
      ·
        refine ⟨20386311766781549394683729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13590874511187699596455819 20386311766781549394683729)
        ·
          refine ⟨15289733825086162046012797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20386311766781549394683729 15289733825086162046012797)
          ·
            refine ⟨5733650184407310767254799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15289733825086162046012797 5733650184407310767254799)
            ·
              refine ⟨8600475276610966150882199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5733650184407310767254799 8600475276610966150882199)
              ·
                refine ⟨12900712914916449226323299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8600475276610966150882199 12900712914916449226323299)
                ·
                  refine ⟨19351069372374673839484949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12900712914916449226323299 19351069372374673839484949)
                  ·
                    refine ⟨907081376830062836225857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19351069372374673839484949 907081376830062836225857)
                    ·
                      rfl

theorem cell23_5299604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_5299604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5299604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5299604 prefixEnd_5299604 := by exact prefixLift 5299604
  have htrace : WordTrace (prefixWord ++ tailWord_5299604) baseStart_5299604 baseEnd_5299604 := by
    simpa [prefixWord, tailWord_5299604, baseEnd_5299604] using wordTrace_append hprefix tailTrace_5299604
  have hstable : (prefixWord ++ tailWord_5299604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5299604).length < 2 ^ (prefixWord ++ tailWord_5299604).sum := by decide
  have hdescent : baseEnd_5299604 < baseStart_5299604 := by decide
  rcases family_descends (prefixWord ++ tailWord_5299604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5299680 : List Nat := [2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 4]
def baseStart_5299680 : Nat := 118140960795 + 5299680 * 2 ^ 59
def prefixEnd_5299680 : Nat := 4983230072969 + 3 ^ 40 * 5299680 * 2
def baseEnd_5299680 : Nat := 2721283155019930211327221

theorem tailTrace_5299680 : CollatzResearch.WordTrace tailWord_5299680 prefixEnd_5299680 2721283155019930211327221 := by
  unfold tailWord_5299680
  simp only [CollatzResearch.WordTrace]
  refine ⟨96647604720085974064680247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128863472960114632086240329 96647604720085974064680247)
  ·
    refine ⟨144971407080128961097020371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96647604720085974064680247 144971407080128961097020371)
    ·
      refine ⟨217457110620193441645530557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144971407080128961097020371 217457110620193441645530557)
      ·
        refine ⟨81546416482572540617073959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 217457110620193441645530557 81546416482572540617073959)
        ·
          refine ⟨122319624723858810925610939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81546416482572540617073959 122319624723858810925610939)
          ·
            refine ⟨183479437085788216388416409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122319624723858810925610939 183479437085788216388416409)
            ·
              refine ⟨137609577814341162291312307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 183479437085788216388416409 137609577814341162291312307)
              ·
                refine ⟨206414366721511743436968461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 137609577814341162291312307 206414366721511743436968461)
                ·
                  refine ⟨77405387520566903788863173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 206414366721511743436968461 77405387520566903788863173)
                  ·
                    refine ⟨14513510160106294460411845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 77405387520566903788863173 14513510160106294460411845)
                    ·
                      refine ⟨2721283155019930211327221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14513510160106294460411845 2721283155019930211327221)
                      ·
                        rfl

theorem cell23_5299680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 4].length) (baseStart_5299680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5299680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5299680 prefixEnd_5299680 := by exact prefixLift 5299680
  have htrace : WordTrace (prefixWord ++ tailWord_5299680) baseStart_5299680 baseEnd_5299680 := by
    simpa [prefixWord, tailWord_5299680, baseEnd_5299680] using wordTrace_append hprefix tailTrace_5299680
  have hstable : (prefixWord ++ tailWord_5299680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5299680).length < 2 ^ (prefixWord ++ tailWord_5299680).sum := by decide
  have hdescent : baseEnd_5299680 < baseStart_5299680 := by decide
  rcases family_descends (prefixWord ++ tailWord_5299680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5299684 : List Nat := [2, 3, 1, 1, 1, 1, 1, 3, 6, 2, 2]
def baseStart_5299684 : Nat := 118140960795 + 5299684 * 2 ^ 59
def prefixEnd_5299684 : Nat := 4983230072969 + 3 ^ 40 * 5299684 * 2
def baseEnd_5299684 : Nat := 2721285208942548195677203

theorem tailTrace_5299684 : CollatzResearch.WordTrace tailWord_5299684 prefixEnd_5299684 2721285208942548195677203 := by
  unfold tailWord_5299684
  simp only [CollatzResearch.WordTrace]
  refine ⟨96647677666078728406253053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128863570221438304541670737 96647677666078728406253053)
  ·
    refine ⟨36242879124779523152344895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96647677666078728406253053 36242879124779523152344895)
    ·
      refine ⟨54364318687169284728517343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36242879124779523152344895 54364318687169284728517343)
      ·
        refine ⟨81546478030753927092776015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54364318687169284728517343 81546478030753927092776015)
        ·
          refine ⟨122319717046130890639164023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81546478030753927092776015 122319717046130890639164023)
          ·
            refine ⟨183479575569196335958746035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122319717046130890639164023 183479575569196335958746035)
            ·
              refine ⟨275219363353794503938119053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 183479575569196335958746035 275219363353794503938119053)
              ·
                refine ⟨103207261257672938976794645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 275219363353794503938119053 103207261257672938976794645)
                ·
                  refine ⟨4837840371453419014537249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 103207261257672938976794645 4837840371453419014537249)
                  ·
                    refine ⟨3628380278590064260902937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4837840371453419014537249 3628380278590064260902937)
                    ·
                      refine ⟨2721285208942548195677203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3628380278590064260902937 2721285208942548195677203)
                      ·
                        rfl

theorem cell23_5299684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 6, 2, 2].length) (baseStart_5299684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5299684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5299684 prefixEnd_5299684 := by exact prefixLift 5299684
  have htrace : WordTrace (prefixWord ++ tailWord_5299684) baseStart_5299684 baseEnd_5299684 := by
    simpa [prefixWord, tailWord_5299684, baseEnd_5299684] using wordTrace_append hprefix tailTrace_5299684
  have hstable : (prefixWord ++ tailWord_5299684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5299684).length < 2 ^ (prefixWord ++ tailWord_5299684).sum := by decide
  have hdescent : baseEnd_5299684 < baseStart_5299684 := by decide
  rcases family_descends (prefixWord ++ tailWord_5299684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5299687 : List Nat := [1, 1, 5, 2, 1, 2, 2, 1, 2, 1, 5]
def baseStart_5299687 : Nat := 118140960795 + 5299687 * 2 ^ 59
def prefixEnd_5299687 : Nat := 4983230072969 + 3 ^ 40 * 5299687 * 2
def baseEnd_5299687 : Nat := 2721286749384511683939689

theorem tailTrace_5299687 : CollatzResearch.WordTrace tailWord_5299687 prefixEnd_5299687 2721286749384511683939689 := by
  unfold tailWord_5299687
  simp only [CollatzResearch.WordTrace]
  refine ⟨193295464751146588324865315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128863643167431058883243543 193295464751146588324865315)
  ·
    refine ⟨289943197126719882487297973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193295464751146588324865315 289943197126719882487297973)
    ·
      refine ⟨27182174730629988983184185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 289943197126719882487297973 27182174730629988983184185)
      ·
        refine ⟨20386631047972491737388139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27182174730629988983184185 20386631047972491737388139)
        ·
          refine ⟨30579946571958737606082209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20386631047972491737388139 30579946571958737606082209)
          ·
            refine ⟨22934959928969053204561657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30579946571958737606082209 22934959928969053204561657)
            ·
              refine ⟨17201219946726789903421243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22934959928969053204561657 17201219946726789903421243)
              ·
                refine ⟨25801829920090184855131865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17201219946726789903421243 25801829920090184855131865)
                ·
                  refine ⟨19351372440067638641348899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25801829920090184855131865 19351372440067638641348899)
                  ·
                    refine ⟨29027058660101457962023349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19351372440067638641348899 29027058660101457962023349)
                    ·
                      refine ⟨2721286749384511683939689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29027058660101457962023349 2721286749384511683939689)
                      ·
                        rfl

theorem cell23_5299687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_5299687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5299687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5299687 prefixEnd_5299687 := by exact prefixLift 5299687
  have htrace : WordTrace (prefixWord ++ tailWord_5299687) baseStart_5299687 baseEnd_5299687 := by
    simpa [prefixWord, tailWord_5299687, baseEnd_5299687] using wordTrace_append hprefix tailTrace_5299687
  have hstable : (prefixWord ++ tailWord_5299687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5299687).length < 2 ^ (prefixWord ++ tailWord_5299687).sum := by decide
  have hdescent : baseEnd_5299687 < baseStart_5299687 := by decide
  rcases family_descends (prefixWord ++ tailWord_5299687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5299707 : List Nat := [1, 1, 1, 1, 1, 3, 2, 8, 5]
def baseStart_5299707 : Nat := 118140960795 + 5299707 * 2 ^ 59
def prefixEnd_5299707 : Nat := 4983230072969 + 3 ^ 40 * 5299707 * 2
def baseEnd_5299707 : Nat := 302366335444177956187733

theorem tailTrace_5299707 : CollatzResearch.WordTrace tailWord_5299707 prefixEnd_5299707 302366335444177956187733 := by
  unfold tailWord_5299707
  simp only [CollatzResearch.WordTrace]
  refine ⟨193296194211074131740593375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128864129474049421160395583 193296194211074131740593375)
  ·
    refine ⟨289944291316611197610890063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193296194211074131740593375 289944291316611197610890063)
    ·
      refine ⟨434916436974916796416335095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289944291316611197610890063 434916436974916796416335095)
      ·
        refine ⟨652374655462375194624502643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 434916436974916796416335095 652374655462375194624502643)
        ·
          refine ⟨978561983193562791936753965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 652374655462375194624502643 978561983193562791936753965)
          ·
            refine ⟨366960743697586046976282737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 978561983193562791936753965 366960743697586046976282737)
            ·
              refine ⟨275220557773189535232212053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 366960743697586046976282737 275220557773189535232212053)
              ·
                refine ⟨3225240911404564866002485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 275220557773189535232212053 3225240911404564866002485)
                ·
                  refine ⟨302366335444177956187733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3225240911404564866002485 302366335444177956187733)
                  ·
                    rfl

theorem cell23_5299707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 8, 5].length) (baseStart_5299707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5299707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5299707 prefixEnd_5299707 := by exact prefixLift 5299707
  have htrace : WordTrace (prefixWord ++ tailWord_5299707) baseStart_5299707 baseEnd_5299707 := by
    simpa [prefixWord, tailWord_5299707, baseEnd_5299707] using wordTrace_append hprefix tailTrace_5299707
  have hstable : (prefixWord ++ tailWord_5299707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5299707).length < 2 ^ (prefixWord ++ tailWord_5299707).sum := by decide
  have hdescent : baseEnd_5299707 < baseStart_5299707 := by decide
  rcases family_descends (prefixWord ++ tailWord_5299707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5299714 : List Nat := [3, 4, 1, 2, 1, 1, 1, 1, 1, 4, 4]
def baseStart_5299714 : Nat := 118140960795 + 5299714 * 2 ^ 59
def prefixEnd_5299714 : Nat := 4983230072969 + 3 ^ 40 * 5299714 * 2
def baseEnd_5299714 : Nat := 2721300613362183078302065

theorem tailTrace_5299714 : CollatzResearch.WordTrace tailWord_5299714 prefixEnd_5299714 2721300613362183078302065 := by
  unfold tailWord_5299714
  simp only [CollatzResearch.WordTrace]
  refine ⟨48324112380512192984024549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128864299681365847957398797 48324112380512192984024549)
  ·
    refine ⟨9060771071346036184504603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48324112380512192984024549 9060771071346036184504603)
    ·
      refine ⟨13591156607019054276756905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9060771071346036184504603 13591156607019054276756905)
      ·
        refine ⟨10193367455264290707567679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13591156607019054276756905 10193367455264290707567679)
        ·
          refine ⟨15290051182896436061351519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10193367455264290707567679 15290051182896436061351519)
          ·
            refine ⟨22935076774344654092027279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15290051182896436061351519 22935076774344654092027279)
            ·
              refine ⟨34402615161516981138040919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22935076774344654092027279 34402615161516981138040919)
              ·
                refine ⟨51603922742275471707061379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34402615161516981138040919 51603922742275471707061379)
                ·
                  refine ⟨77405884113413207560592069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51603922742275471707061379 77405884113413207560592069)
                  ·
                    refine ⟨14513603271264976417611013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 77405884113413207560592069 14513603271264976417611013)
                    ·
                      refine ⟨2721300613362183078302065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14513603271264976417611013 2721300613362183078302065)
                      ·
                        rfl

theorem cell23_5299714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_5299714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5299714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5299714 prefixEnd_5299714 := by exact prefixLift 5299714
  have htrace : WordTrace (prefixWord ++ tailWord_5299714) baseStart_5299714 baseEnd_5299714 := by
    simpa [prefixWord, tailWord_5299714, baseEnd_5299714] using wordTrace_append hprefix tailTrace_5299714
  have hstable : (prefixWord ++ tailWord_5299714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5299714).length < 2 ^ (prefixWord ++ tailWord_5299714).sum := by decide
  have hdescent : baseEnd_5299714 < baseStart_5299714 := by decide
  rcases family_descends (prefixWord ++ tailWord_5299714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5299727 : List Nat := [1, 1, 2, 1, 1, 1, 2, 2, 3, 7, 2]
def baseStart_5299727 : Nat := 118140960795 + 5299727 * 2 ^ 59
def prefixEnd_5299727 : Nat := 4983230072969 + 3 ^ 40 * 5299727 * 2
def baseEnd_5299727 : Nat := 2721307288610691527439505

theorem tailTrace_5299727 : CollatzResearch.WordTrace tailWord_5299727 prefixEnd_5299727 2721307288610691527439505 := by
  unfold tailWord_5299727
  simp only [CollatzResearch.WordTrace]
  refine ⟨193296923671001675156321435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128864615780667783437547623 193296923671001675156321435)
  ·
    refine ⟨289945385506502512734482153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193296923671001675156321435 289945385506502512734482153)
    ·
      refine ⟨217459039129876884550861615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 289945385506502512734482153 217459039129876884550861615)
      ·
        refine ⟨326188558694815326826292423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217459039129876884550861615 326188558694815326826292423)
        ·
          refine ⟨489282838042222990239438635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 326188558694815326826292423 489282838042222990239438635)
          ·
            refine ⟨733924257063334485359157953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 489282838042222990239438635 733924257063334485359157953)
            ·
              refine ⟨550443192797500864019368465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 733924257063334485359157953 550443192797500864019368465)
              ·
                refine ⟨412832394598125648014526349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 550443192797500864019368465 412832394598125648014526349)
                ·
                  refine ⟨154812147974297118005447381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 412832394598125648014526349 154812147974297118005447381)
                  ·
                    refine ⟨3628409718147588703252673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 154812147974297118005447381 3628409718147588703252673)
                    ·
                      refine ⟨2721307288610691527439505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3628409718147588703252673 2721307288610691527439505)
                      ·
                        rfl

theorem cell23_5299727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 7, 2].length) (baseStart_5299727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5299727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5299727 prefixEnd_5299727 := by exact prefixLift 5299727
  have htrace : WordTrace (prefixWord ++ tailWord_5299727) baseStart_5299727 baseEnd_5299727 := by
    simpa [prefixWord, tailWord_5299727, baseEnd_5299727] using wordTrace_append hprefix tailTrace_5299727
  have hstable : (prefixWord ++ tailWord_5299727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5299727).length < 2 ^ (prefixWord ++ tailWord_5299727).sum := by decide
  have hdescent : baseEnd_5299727 < baseStart_5299727 := by decide
  rcases family_descends (prefixWord ++ tailWord_5299727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5299752 : List Nat := [2, 1, 5, 2, 3, 1, 1, 2, 2, 2, 2]
def baseStart_5299752 : Nat := 118140960795 + 5299752 * 2 ^ 59
def prefixEnd_5299752 : Nat := 4983230072969 + 3 ^ 40 * 5299752 * 2
def baseEnd_5299752 : Nat := 2721320125627053929626891

theorem tailTrace_5299752 : CollatzResearch.WordTrace tailWord_5299752 prefixEnd_5299752 2721320125627053929626891 := by
  unfold tailWord_5299752
  simp only [CollatzResearch.WordTrace]
  refine ⟨96648917747955552212990755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128865223663940736283987673 96648917747955552212990755)
  ·
    refine ⟨144973376621933328319486133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96648917747955552212990755 144973376621933328319486133)
    ·
      refine ⟨13591254058306249529951825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 144973376621933328319486133 13591254058306249529951825)
      ·
        refine ⟨10193440543729687147463869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13591254058306249529951825 10193440543729687147463869)
        ·
          refine ⟨3822540203898632680298951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10193440543729687147463869 3822540203898632680298951)
          ·
            refine ⟨5733810305847949020448427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3822540203898632680298951 5733810305847949020448427)
            ·
              refine ⟨8600715458771923530672641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5733810305847949020448427 8600715458771923530672641)
              ·
                refine ⟨6450536594078942648004481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8600715458771923530672641 6450536594078942648004481)
                ·
                  refine ⟨4837902445559206986003361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6450536594078942648004481 4837902445559206986003361)
                  ·
                    refine ⟨3628426834169405239502521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4837902445559206986003361 3628426834169405239502521)
                    ·
                      refine ⟨2721320125627053929626891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3628426834169405239502521 2721320125627053929626891)
                      ·
                        rfl

theorem cell23_5299752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_5299752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5299752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5299752 prefixEnd_5299752 := by exact prefixLift 5299752
  have htrace : WordTrace (prefixWord ++ tailWord_5299752) baseStart_5299752 baseEnd_5299752 := by
    simpa [prefixWord, tailWord_5299752, baseEnd_5299752] using wordTrace_append hprefix tailTrace_5299752
  have hstable : (prefixWord ++ tailWord_5299752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5299752).length < 2 ^ (prefixWord ++ tailWord_5299752).sum := by decide
  have hdescent : baseEnd_5299752 < baseStart_5299752 := by decide
  rcases family_descends (prefixWord ++ tailWord_5299752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5299794 : List Nat := [3, 2, 2, 1, 2, 2, 2, 1, 1, 4, 3]
def baseStart_5299794 : Nat := 118140960795 + 5299794 * 2 ^ 59
def prefixEnd_5299794 : Nat := 4983230072969 + 3 ^ 40 * 5299794 * 2
def baseEnd_5299794 : Nat := 2721341691814542765301697

theorem tailTrace_5299794 : CollatzResearch.WordTrace tailWord_5299794 prefixEnd_5299794 2721341691814542765301697 := by
  unfold tailWord_5299794
  simp only [CollatzResearch.WordTrace]
  refine ⟨48324841840439736399752609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128866244907839297066006957 48324841840439736399752609)
  ·
    refine ⟨36243631380329802299814457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48324841840439736399752609 36243631380329802299814457)
    ·
      refine ⟨27182723535247351724860843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36243631380329802299814457 27182723535247351724860843)
      ·
        refine ⟨40774085302871027587291265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27182723535247351724860843 40774085302871027587291265)
        ·
          refine ⟨30580563977153270690468449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40774085302871027587291265 30580563977153270690468449)
          ·
            refine ⟨22935422982864953017851337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30580563977153270690468449 22935422982864953017851337)
            ·
              refine ⟨17201567237148714763388503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22935422982864953017851337 17201567237148714763388503)
              ·
                refine ⟨25802350855723072145082755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17201567237148714763388503 25802350855723072145082755)
                ·
                  refine ⟨38703526283584608217624133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25802350855723072145082755 38703526283584608217624133)
                  ·
                    refine ⟨7256911178172114040804525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38703526283584608217624133 7256911178172114040804525)
                    ·
                      refine ⟨2721341691814542765301697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7256911178172114040804525 2721341691814542765301697)
                      ·
                        rfl

theorem cell23_5299794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 1, 1, 4, 3].length) (baseStart_5299794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5299794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5299794 prefixEnd_5299794 := by exact prefixLift 5299794
  have htrace : WordTrace (prefixWord ++ tailWord_5299794) baseStart_5299794 baseEnd_5299794 := by
    simpa [prefixWord, tailWord_5299794, baseEnd_5299794] using wordTrace_append hprefix tailTrace_5299794
  have hstable : (prefixWord ++ tailWord_5299794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5299794).length < 2 ^ (prefixWord ++ tailWord_5299794).sum := by decide
  have hdescent : baseEnd_5299794 < baseStart_5299794 := by decide
  rcases family_descends (prefixWord ++ tailWord_5299794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5299834 : List Nat := [3, 1, 1, 1, 1, 1, 1, 6, 1, 5, 2]
def baseStart_5299834 : Nat := 118140960795 + 5299834 * 2 ^ 59
def prefixEnd_5299834 : Nat := 4983230072969 + 3 ^ 40 * 5299834 * 2
def baseEnd_5299834 : Nat := 2721362231040722608801513

theorem tailTrace_5299834 : CollatzResearch.WordTrace tailWord_5299834 prefixEnd_5299834 2721362231040722608801513 := by
  unfold tailWord_5299834
  simp only [CollatzResearch.WordTrace]
  refine ⟨48325206570403508107616639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128867217521076021620311037 48325206570403508107616639)
  ·
    refine ⟨72487809855605262161424959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48325206570403508107616639 72487809855605262161424959)
    ·
      refine ⟨108731714783407893242137439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72487809855605262161424959 108731714783407893242137439)
      ·
        refine ⟨163097572175111839863206159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108731714783407893242137439 163097572175111839863206159)
        ·
          refine ⟨244646358262667759794809239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163097572175111839863206159 244646358262667759794809239)
          ·
            refine ⟨366969537394001639692213859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 244646358262667759794809239 366969537394001639692213859)
            ·
              refine ⟨550454306091002459538320789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 366969537394001639692213859 550454306091002459538320789)
              ·
                refine ⟨25802545598015740290858787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 550454306091002459538320789 25802545598015740290858787)
                ·
                  refine ⟨38703818397023610436288181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25802545598015740290858787 38703818397023610436288181)
                  ·
                    refine ⟨3628482974720963478402017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38703818397023610436288181 3628482974720963478402017)
                    ·
                      refine ⟨2721362231040722608801513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3628482974720963478402017 2721362231040722608801513)
                      ·
                        rfl

theorem cell23_5299834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 6, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 6, 1, 5, 2].length) (baseStart_5299834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5299834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5299834 prefixEnd_5299834 := by exact prefixLift 5299834
  have htrace : WordTrace (prefixWord ++ tailWord_5299834) baseStart_5299834 baseEnd_5299834 := by
    simpa [prefixWord, tailWord_5299834, baseEnd_5299834] using wordTrace_append hprefix tailTrace_5299834
  have hstable : (prefixWord ++ tailWord_5299834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5299834).length < 2 ^ (prefixWord ++ tailWord_5299834).sum := by decide
  have hdescent : baseEnd_5299834 < baseStart_5299834 := by decide
  rcases family_descends (prefixWord ++ tailWord_5299834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5299851 : List Nat := [1, 1, 1, 1, 4, 1, 6, 1, 2, 3, 2]
def baseStart_5299851 : Nat := 118140960795 + 5299851 * 2 ^ 59
def prefixEnd_5299851 : Nat := 4983230072969 + 3 ^ 40 * 5299851 * 2
def baseEnd_5299851 : Nat := 2721370960211849042288935

theorem tailTrace_5299851 : CollatzResearch.WordTrace tailWord_5299851 prefixEnd_5299851 2721370960211849042288935 := by
  unfold tailWord_5299851
  simp only [CollatzResearch.WordTrace]
  refine ⟨193301446322552444333835407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128867630881701629555890271 193301446322552444333835407)
  ·
    refine ⟨289952169483828666500753111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193301446322552444333835407 289952169483828666500753111)
    ·
      refine ⟨434928254225742999751129667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289952169483828666500753111 434928254225742999751129667)
      ·
        refine ⟨652392381338614499626694501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 434928254225742999751129667 652392381338614499626694501)
        ·
          refine ⟨122323571500990218680005219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 652392381338614499626694501 122323571500990218680005219)
          ·
            refine ⟨183485357251485328020007829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122323571500990218680005219 183485357251485328020007829)
            ·
              refine ⟨8600876121163374750937867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 183485357251485328020007829 8600876121163374750937867)
              ·
                refine ⟨12901314181745062126406801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8600876121163374750937867 12901314181745062126406801)
                ·
                  refine ⟨9675985636308796594805101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12901314181745062126406801 9675985636308796594805101)
                  ·
                    refine ⟨3628494613615798723051913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9675985636308796594805101 3628494613615798723051913)
                    ·
                      refine ⟨2721370960211849042288935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3628494613615798723051913 2721370960211849042288935)
                      ·
                        rfl

theorem cell23_5299851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 1, 2, 3, 2].length) (baseStart_5299851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5299851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5299851 prefixEnd_5299851 := by exact prefixLift 5299851
  have htrace : WordTrace (prefixWord ++ tailWord_5299851) baseStart_5299851 baseEnd_5299851 := by
    simpa [prefixWord, tailWord_5299851, baseEnd_5299851] using wordTrace_append hprefix tailTrace_5299851
  have hstable : (prefixWord ++ tailWord_5299851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5299851).length < 2 ^ (prefixWord ++ tailWord_5299851).sum := by decide
  have hdescent : baseEnd_5299851 < baseStart_5299851 := by decide
  rcases family_descends (prefixWord ++ tailWord_5299851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5299877 : List Nat := [1, 3, 1, 2, 1, 2, 2, 1, 3, 1, 6]
def baseStart_5299877 : Nat := 118140960795 + 5299877 * 2 ^ 59
def prefixEnd_5299877 : Nat := 4983230072969 + 3 ^ 40 * 5299877 * 2
def baseEnd_5299877 : Nat := 2721384310708865940563815

theorem tailTrace_5299877 : CollatzResearch.WordTrace tailWord_5299877 prefixEnd_5299877 2721384310708865940563815 := by
  unfold tailWord_5299877
  simp only [CollatzResearch.WordTrace]
  refine ⟨193302394620458250774281885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128868263080305500516187923 193302394620458250774281885)
  ·
    refine ⟨72488397982671844040355707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 193302394620458250774281885 72488397982671844040355707)
    ·
      refine ⟨108732596974007766060533561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72488397982671844040355707 108732596974007766060533561)
      ·
        refine ⟨81549447730505824545400171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108732596974007766060533561 81549447730505824545400171)
        ·
          refine ⟨122324171595758736818100257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81549447730505824545400171 122324171595758736818100257)
          ·
            refine ⟨91743128696819052613575193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122324171595758736818100257 91743128696819052613575193)
            ·
              refine ⟨68807346522614289460181395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91743128696819052613575193 68807346522614289460181395)
              ·
                refine ⟨103211019783921434190272093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68807346522614289460181395 103211019783921434190272093)
                ·
                  refine ⟨38704132418970537821352035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 103211019783921434190272093 38704132418970537821352035)
                  ·
                    refine ⟨58056198628455806732028053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38704132418970537821352035 58056198628455806732028053)
                    ·
                      refine ⟨2721384310708865940563815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58056198628455806732028053 2721384310708865940563815)
                      ·
                        rfl

theorem cell23_5299877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 3, 1, 6].length) (baseStart_5299877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5299877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5299877 prefixEnd_5299877 := by exact prefixLift 5299877
  have htrace : WordTrace (prefixWord ++ tailWord_5299877) baseStart_5299877 baseEnd_5299877 := by
    simpa [prefixWord, tailWord_5299877, baseEnd_5299877] using wordTrace_append hprefix tailTrace_5299877
  have hstable : (prefixWord ++ tailWord_5299877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5299877).length < 2 ^ (prefixWord ++ tailWord_5299877).sum := by decide
  have hdescent : baseEnd_5299877 < baseStart_5299877 := by decide
  rcases family_descends (prefixWord ++ tailWord_5299877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5299898 : List Nat := [3, 1, 1, 1, 2, 5, 1, 2, 3, 2, 2]
def baseStart_5299898 : Nat := 118140960795 + 5299898 * 2 ^ 59
def prefixEnd_5299898 : Nat := 4983230072969 + 3 ^ 40 * 5299898 * 2
def baseEnd_5299898 : Nat := 2721395093802610358401219

theorem tailTrace_5299898 : CollatzResearch.WordTrace tailWord_5299898 prefixEnd_5299898 2721395093802610358401219 := by
  unfold tailWord_5299898
  simp only [CollatzResearch.WordTrace]
  refine ⟨48325790138345542840199087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128868773702254780907197565 48325790138345542840199087)
  ·
    refine ⟨72488685207518314260298631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48325790138345542840199087 72488685207518314260298631)
    ·
      refine ⟨108733027811277471390447947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72488685207518314260298631 108733027811277471390447947)
      ·
        refine ⟨163099541716916207085671921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108733027811277471390447947 163099541716916207085671921)
        ·
          refine ⟨122324656287687155314253941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163099541716916207085671921 122324656287687155314253941)
          ·
            refine ⟨11467936526970670810711307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 122324656287687155314253941 11467936526970670810711307)
            ·
              refine ⟨17201904790456006216066961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11467936526970670810711307 17201904790456006216066961)
              ·
                refine ⟨12901428592842004662050221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17201904790456006216066961 12901428592842004662050221)
                ·
                  refine ⟨4838035722315751748268833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12901428592842004662050221 4838035722315751748268833)
                  ·
                    refine ⟨3628526791736813811201625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4838035722315751748268833 3628526791736813811201625)
                    ·
                      refine ⟨2721395093802610358401219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3628526791736813811201625 2721395093802610358401219)
                      ·
                        rfl

theorem cell23_5299898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 2, 3, 2, 2].length) (baseStart_5299898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5299898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5299898 prefixEnd_5299898 := by exact prefixLift 5299898
  have htrace : WordTrace (prefixWord ++ tailWord_5299898) baseStart_5299898 baseEnd_5299898 := by
    simpa [prefixWord, tailWord_5299898, baseEnd_5299898] using wordTrace_append hprefix tailTrace_5299898
  have hstable : (prefixWord ++ tailWord_5299898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5299898).length < 2 ^ (prefixWord ++ tailWord_5299898).sum := by decide
  have hdescent : baseEnd_5299898 < baseStart_5299898 := by decide
  rcases family_descends (prefixWord ++ tailWord_5299898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5299901 : List Nat := [1, 4, 1, 2, 1, 2, 2, 4, 1, 2, 3]
def baseStart_5299901 : Nat := 118140960795 + 5299901 * 2 ^ 59
def prefixEnd_5299901 : Nat := 4983230072969 + 3 ^ 40 * 5299901 * 2
def baseEnd_5299901 : Nat := 2721396634244573846663705

theorem tailTrace_5299901 : CollatzResearch.WordTrace tailWord_5299901 prefixEnd_5299901 2721396634244573846663705 := by
  unfold tailWord_5299901
  simp only [CollatzResearch.WordTrace]
  refine ⟨193303269972371302873155557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128868846648247535248770371 193303269972371302873155557)
  ·
    refine ⟨36244363119819619288716667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 193303269972371302873155557 36244363119819619288716667)
    ·
      refine ⟨54366544679729428933075001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36244363119819619288716667 54366544679729428933075001)
      ·
        refine ⟨40774908509797071699806251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54366544679729428933075001 40774908509797071699806251)
        ·
          refine ⟨61162362764695607549709377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40774908509797071699806251 61162362764695607549709377)
          ·
            refine ⟨45871772073521705662282033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61162362764695607549709377 45871772073521705662282033)
            ·
              refine ⟨34403829055141279246711525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45871772073521705662282033 34403829055141279246711525)
              ·
                refine ⟨6450717947838989858758411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34403829055141279246711525 6450717947838989858758411)
                ·
                  refine ⟨9676076921758484788137617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6450717947838989858758411 9676076921758484788137617)
                  ·
                    refine ⟨7257057691318863591103213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9676076921758484788137617 7257057691318863591103213)
                    ·
                      refine ⟨2721396634244573846663705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7257057691318863591103213 2721396634244573846663705)
                      ·
                        rfl

theorem cell23_5299901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 4, 1, 2, 3].length) (baseStart_5299901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5299901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5299901 prefixEnd_5299901 := by exact prefixLift 5299901
  have htrace : WordTrace (prefixWord ++ tailWord_5299901) baseStart_5299901 baseEnd_5299901 := by
    simpa [prefixWord, tailWord_5299901, baseEnd_5299901] using wordTrace_append hprefix tailTrace_5299901
  have hstable : (prefixWord ++ tailWord_5299901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5299901).length < 2 ^ (prefixWord ++ tailWord_5299901).sum := by decide
  have hdescent : baseEnd_5299901 < baseStart_5299901 := by decide
  rcases family_descends (prefixWord ++ tailWord_5299901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5299904 : List Nat := [2, 1, 1, 2, 4, 1, 5, 7]
def baseStart_5299904 : Nat := 118140960795 + 5299904 * 2 ^ 59
def prefixEnd_5299904 : Nat := 4983230072969 + 3 ^ 40 * 5299904 * 2
def baseEnd_5299904 : Nat := 100792524988390271663933

theorem tailTrace_5299904 : CollatzResearch.WordTrace tailWord_5299904 prefixEnd_5299904 100792524988390271663933 := by
  unfold tailWord_5299904
  simp only [CollatzResearch.WordTrace]
  refine ⟨96651689695680217192757383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128868919594240289590343177 96651689695680217192757383)
  ·
    refine ⟨144977534543520325789136075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96651689695680217192757383 144977534543520325789136075)
    ·
      refine ⟨217466301815280488683704113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144977534543520325789136075 217466301815280488683704113)
      ·
        refine ⟨163099726361460366512778085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 217466301815280488683704113 163099726361460366512778085)
        ·
          refine ⟨30581198692773818721145891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 163099726361460366512778085 30581198692773818721145891)
          ·
            refine ⟨45871798039160728081718837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30581198692773818721145891 45871798039160728081718837)
            ·
              refine ⟨4300481066171318257661141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45871798039160728081718837 4300481066171318257661141)
              ·
                refine ⟨100792524988390271663933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4300481066171318257661141 100792524988390271663933)
                ·
                  rfl

theorem cell23_5299904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 5, 7].length) (baseStart_5299904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5299904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5299904 prefixEnd_5299904 := by exact prefixLift 5299904
  have htrace : WordTrace (prefixWord ++ tailWord_5299904) baseStart_5299904 baseEnd_5299904 := by
    simpa [prefixWord, tailWord_5299904, baseEnd_5299904] using wordTrace_append hprefix tailTrace_5299904
  have hstable : (prefixWord ++ tailWord_5299904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5299904).length < 2 ^ (prefixWord ++ tailWord_5299904).sum := by decide
  have hdescent : baseEnd_5299904 < baseStart_5299904 := by decide
  rcases family_descends (prefixWord ++ tailWord_5299904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5299932 : List Nat := [2, 2, 5, 1, 2, 1, 2, 1, 3, 2, 2]
def baseStart_5299932 : Nat := 118140960795 + 5299932 * 2 ^ 59
def prefixEnd_5299932 : Nat := 4983230072969 + 3 ^ 40 * 5299932 * 2
def baseEnd_5299932 : Nat := 2721412552144863225376063

theorem tailTrace_5299932 : CollatzResearch.WordTrace tailWord_5299932 prefixEnd_5299932 2721412552144863225376063 := by
  unfold tailWord_5299932
  simp only [CollatzResearch.WordTrace]
  refine ⟨96652200317629497583767025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128869600423505996778356033 96652200317629497583767025)
  ·
    refine ⟨72489150238222123187825269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96652200317629497583767025 72489150238222123187825269)
    ·
      refine ⟨6795857834833324048858619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 72489150238222123187825269 6795857834833324048858619)
      ·
        refine ⟨10193786752249986073287929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6795857834833324048858619 10193786752249986073287929)
        ·
          refine ⟨7645340064187489554965947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10193786752249986073287929 7645340064187489554965947)
          ·
            refine ⟨11468010096281234332448921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7645340064187489554965947 11468010096281234332448921)
            ·
              refine ⟨8601007572210925749336691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11468010096281234332448921 8601007572210925749336691)
              ·
                refine ⟨12901511358316388624005037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8601007572210925749336691 12901511358316388624005037)
                ·
                  refine ⟨4838066759368645734001889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12901511358316388624005037 4838066759368645734001889)
                  ·
                    refine ⟨3628550069526484300501417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4838066759368645734001889 3628550069526484300501417)
                    ·
                      refine ⟨2721412552144863225376063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3628550069526484300501417 2721412552144863225376063)
                      ·
                        rfl

theorem cell23_5299932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_5299932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5299932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5299932 prefixEnd_5299932 := by exact prefixLift 5299932
  have htrace : WordTrace (prefixWord ++ tailWord_5299932) baseStart_5299932 baseEnd_5299932 := by
    simpa [prefixWord, tailWord_5299932, baseEnd_5299932] using wordTrace_append hprefix tailTrace_5299932
  have hstable : (prefixWord ++ tailWord_5299932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5299932).length < 2 ^ (prefixWord ++ tailWord_5299932).sum := by decide
  have hdescent : baseEnd_5299932 < baseStart_5299932 := by decide
  rcases family_descends (prefixWord ++ tailWord_5299932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5299966 : List Nat := [4, 2, 2, 1, 4, 1, 1, 3, 1, 2, 2]
def baseStart_5299966 : Nat := 118140960795 + 5299966 * 2 ^ 59
def prefixEnd_5299966 : Nat := 4983230072969 + 3 ^ 40 * 5299966 * 2
def baseEnd_5299966 : Nat := 2721430010487116092350907

theorem tailTrace_5299966 : CollatzResearch.WordTrace tailWord_5299966 prefixEnd_5299966 2721430010487116092350907 := by
  unfold tailWord_5299966
  simp only [CollatzResearch.WordTrace]
  refine ⟨24163205089641977371783969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128870427144757212649514501 24163205089641977371783969)
  ·
    refine ⟨18122403817231483028837977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24163205089641977371783969 18122403817231483028837977)
    ·
      refine ⟨13591802862923612271628483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18122403817231483028837977 13591802862923612271628483)
      ·
        refine ⟨20387704294385418407442725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13591802862923612271628483 20387704294385418407442725)
        ·
          refine ⟨3822694555197265951395511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20387704294385418407442725 3822694555197265951395511)
          ·
            refine ⟨5734041832795898927093267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3822694555197265951395511 5734041832795898927093267)
            ·
              refine ⟨8601062749193848390639901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5734041832795898927093267 8601062749193848390639901)
              ·
                refine ⟨3225398530947693146489963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8601062749193848390639901 3225398530947693146489963)
                ·
                  refine ⟨4838097796421539719734945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3225398530947693146489963 4838097796421539719734945)
                  ·
                    refine ⟨3628573347316154789801209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4838097796421539719734945 3628573347316154789801209)
                    ·
                      refine ⟨2721430010487116092350907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3628573347316154789801209 2721430010487116092350907)
                      ·
                        rfl

theorem cell23_5299966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 3, 1, 2, 2].length) (baseStart_5299966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5299966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5299966 prefixEnd_5299966 := by exact prefixLift 5299966
  have htrace : WordTrace (prefixWord ++ tailWord_5299966) baseStart_5299966 baseEnd_5299966 := by
    simpa [prefixWord, tailWord_5299966, baseEnd_5299966] using wordTrace_append hprefix tailTrace_5299966
  have hstable : (prefixWord ++ tailWord_5299966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5299966).length < 2 ^ (prefixWord ++ tailWord_5299966).sum := by decide
  have hdescent : baseEnd_5299966 < baseStart_5299966 := by decide
  rcases family_descends (prefixWord ++ tailWord_5299966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5299971 : List Nat := [1, 1, 1, 3, 2, 2, 2, 4, 1, 4, 2]
def baseStart_5299971 : Nat := 118140960795 + 5299971 * 2 ^ 59
def prefixEnd_5299971 : Nat := 4983230072969 + 3 ^ 40 * 5299971 * 2
def baseEnd_5299971 : Nat := 2721432577890388572788383

theorem tailTrace_5299971 : CollatzResearch.WordTrace tailWord_5299971 prefixEnd_5299971 2721432577890388572788383 := by
  unfold tailWord_5299971
  simp only [CollatzResearch.WordTrace]
  refine ⟨193305823082117704828203767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128870548721411803218802511 193305823082117704828203767)
  ·
    refine ⟨289958734623176557242305651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193305823082117704828203767 289958734623176557242305651)
    ·
      refine ⟨434938101934764835863458477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289958734623176557242305651 434938101934764835863458477)
      ·
        refine ⟨163101788225536813448796929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 434938101934764835863458477 163101788225536813448796929)
        ·
          refine ⟨122326341169152610086597697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163101788225536813448796929 122326341169152610086597697)
          ·
            refine ⟨91744755876864457564948273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122326341169152610086597697 91744755876864457564948273)
            ·
              refine ⟨68808566907648343173711205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91744755876864457564948273 68808566907648343173711205)
              ·
                refine ⟨12901606295184064345070851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68808566907648343173711205 12901606295184064345070851)
                ·
                  refine ⟨19352409442776096517606277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12901606295184064345070851 19352409442776096517606277)
                  ·
                    refine ⟨3628576770520518097051177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19352409442776096517606277 3628576770520518097051177)
                    ·
                      refine ⟨2721432577890388572788383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3628576770520518097051177 2721432577890388572788383)
                      ·
                        rfl

theorem cell23_5299971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 4, 1, 4, 2].length) (baseStart_5299971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5299971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5299971 prefixEnd_5299971 := by exact prefixLift 5299971
  have htrace : WordTrace (prefixWord ++ tailWord_5299971) baseStart_5299971 baseEnd_5299971 := by
    simpa [prefixWord, tailWord_5299971, baseEnd_5299971] using wordTrace_append hprefix tailTrace_5299971
  have hstable : (prefixWord ++ tailWord_5299971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5299971).length < 2 ^ (prefixWord ++ tailWord_5299971).sum := by decide
  have hdescent : baseEnd_5299971 < baseStart_5299971 := by decide
  rcases family_descends (prefixWord ++ tailWord_5299971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5300005 : List Nat := [1, 3, 1, 2, 3, 3, 1, 3, 2, 2, 2]
def baseStart_5300005 : Nat := 118140960795 + 5300005 * 2 ^ 59
def prefixEnd_5300005 : Nat := 4983230072969 + 3 ^ 40 * 5300005 * 2
def baseEnd_5300005 : Nat := 2721450036232641439763227

theorem tailTrace_5300005 : CollatzResearch.WordTrace tailWord_5300005 prefixEnd_5300005 2721450036232641439763227 := by
  unfold tailWord_5300005
  simp only [CollatzResearch.WordTrace]
  refine ⟨193307063163994528634941469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128871375442663019089960979 193307063163994528634941469)
  ·
    refine ⟨72490148686497948238103051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 193307063163994528634941469 72490148686497948238103051)
    ·
      refine ⟨108735223029746922357154577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72490148686497948238103051 108735223029746922357154577)
      ·
        refine ⟨81551417272310191767865933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108735223029746922357154577 81551417272310191767865933)
        ·
          refine ⟨30581781477116321912949725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81551417272310191767865933 30581781477116321912949725)
          ·
            refine ⟨11468168053918620717356147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30581781477116321912949725 11468168053918620717356147)
            ·
              refine ⟨17202252080877931076034221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11468168053918620717356147 17202252080877931076034221)
              ·
                refine ⟨6450844530329224153512833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17202252080877931076034221 6450844530329224153512833)
                ·
                  refine ⟨4838133397746918115134625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6450844530329224153512833 4838133397746918115134625)
                  ·
                    refine ⟨3628600048310188586350969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4838133397746918115134625 3628600048310188586350969)
                    ·
                      refine ⟨2721450036232641439763227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3628600048310188586350969 2721450036232641439763227)
                      ·
                        rfl

theorem cell23_5300005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 3, 2, 2, 2].length) (baseStart_5300005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5300005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5300005 prefixEnd_5300005 := by exact prefixLift 5300005
  have htrace : WordTrace (prefixWord ++ tailWord_5300005) baseStart_5300005 baseEnd_5300005 := by
    simpa [prefixWord, tailWord_5300005, baseEnd_5300005] using wordTrace_append hprefix tailTrace_5300005
  have hstable : (prefixWord ++ tailWord_5300005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5300005).length < 2 ^ (prefixWord ++ tailWord_5300005).sum := by decide
  have hdescent : baseEnd_5300005 < baseStart_5300005 := by decide
  rcases family_descends (prefixWord ++ tailWord_5300005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5300045 : List Nat := [1, 6, 1, 2, 1, 2, 1, 4, 5]
def baseStart_5300045 : Nat := 118140960795 + 5300045 * 2 ^ 59
def prefixEnd_5300045 : Nat := 4983230072969 + 3 ^ 40 * 5300045 * 2
def baseEnd_5300045 : Nat := 302385619495424587029227

theorem tailTrace_5300045 : CollatzResearch.WordTrace tailWord_5300045 prefixEnd_5300045 302385619495424587029227 := by
  unfold tailWord_5300045
  simp only [CollatzResearch.WordTrace]
  refine ⟨193308522083849615466397589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128872348055899743644265059 193308522083849615466397589)
  ·
    refine ⟨9061336972680450724987387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 193308522083849615466397589 9061336972680450724987387)
    ·
      refine ⟨13592005459020676087481081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9061336972680450724987387 13592005459020676087481081)
      ·
        refine ⟨10194004094265507065610811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13592005459020676087481081 10194004094265507065610811)
        ·
          refine ⟨15291006141398260598416217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10194004094265507065610811 15291006141398260598416217)
          ·
            refine ⟨11468254606048695448812163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15291006141398260598416217 11468254606048695448812163)
            ·
              refine ⟨17202381909073043173218245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11468254606048695448812163 17202381909073043173218245)
              ·
                refine ⟨3225446607951195594978421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17202381909073043173218245 3225446607951195594978421)
                ·
                  refine ⟨302385619495424587029227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3225446607951195594978421 302385619495424587029227)
                  ·
                    rfl

theorem cell23_5300045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 4, 5].length) (baseStart_5300045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5300045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5300045 prefixEnd_5300045 := by exact prefixLift 5300045
  have htrace : WordTrace (prefixWord ++ tailWord_5300045) baseStart_5300045 baseEnd_5300045 := by
    simpa [prefixWord, tailWord_5300045, baseEnd_5300045] using wordTrace_append hprefix tailTrace_5300045
  have hstable : (prefixWord ++ tailWord_5300045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5300045).length < 2 ^ (prefixWord ++ tailWord_5300045).sum := by decide
  have hdescent : baseEnd_5300045 < baseStart_5300045 := by decide
  rcases family_descends (prefixWord ++ tailWord_5300045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5300078 : List Nat := [4, 1, 2, 3, 1, 2, 1, 1, 1, 3, 4]
def baseStart_5300078 : Nat := 118140960795 + 5300078 * 2 ^ 59
def prefixEnd_5300078 : Nat := 4983230072969 + 3 ^ 40 * 5300078 * 2
def baseEnd_5300078 : Nat := 2721487520320419654150391

theorem tailTrace_5300078 : CollatzResearch.WordTrace tailWord_5300078 prefixEnd_5300078 2721487520320419654150391 := by
  unfold tailWord_5300078
  simp only [CollatzResearch.WordTrace]
  refine ⟨24163715711591257762793611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128873150461820041401565925 24163715711591257762793611)
  ·
    refine ⟨36245573567386886644190417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24163715711591257762793611 36245573567386886644190417)
    ·
      refine ⟨27184180175540164983142813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36245573567386886644190417 27184180175540164983142813)
      ·
        refine ⟨10194067565827561868678555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27184180175540164983142813 10194067565827561868678555)
        ·
          refine ⟨15291101348741342803017833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10194067565827561868678555 15291101348741342803017833)
          ·
            refine ⟨11468326011556007102263375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15291101348741342803017833 11468326011556007102263375)
            ·
              refine ⟨17202489017334010653395063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11468326011556007102263375 17202489017334010653395063)
              ·
                refine ⟨25803733526001015980092595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17202489017334010653395063 25803733526001015980092595)
                ·
                  refine ⟨38705600289001523970138893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25803733526001015980092595 38705600289001523970138893)
                  ·
                    refine ⟨14514600108375571488802085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38705600289001523970138893 14514600108375571488802085)
                    ·
                      refine ⟨2721487520320419654150391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14514600108375571488802085 2721487520320419654150391)
                      ·
                        rfl

theorem cell23_5300078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_5300078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5300078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5300078 prefixEnd_5300078 := by exact prefixLift 5300078
  have htrace : WordTrace (prefixWord ++ tailWord_5300078) baseStart_5300078 baseEnd_5300078 := by
    simpa [prefixWord, tailWord_5300078, baseEnd_5300078] using wordTrace_append hprefix tailTrace_5300078
  have hstable : (prefixWord ++ tailWord_5300078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5300078).length < 2 ^ (prefixWord ++ tailWord_5300078).sum := by decide
  have hdescent : baseEnd_5300078 < baseStart_5300078 := by decide
  rcases family_descends (prefixWord ++ tailWord_5300078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5300081 : List Nat := [1, 2, 2, 2, 1, 3, 3, 1, 1, 4, 3]
def baseStart_5300081 : Nat := 118140960795 + 5300081 * 2 ^ 59
def prefixEnd_5300081 : Nat := 4983230072969 + 3 ^ 40 * 5300081 * 2
def baseEnd_5300081 : Nat := 2721489060762383142412877

theorem tailTrace_5300081 : CollatzResearch.WordTrace tailWord_5300081 prefixEnd_5300081 2721489060762383142412877 := by
  unfold tailWord_5300081
  simp only [CollatzResearch.WordTrace]
  refine ⟨193309835111719193614708097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128873223407812795743138731 193309835111719193614708097)
  ·
    refine ⟨144982376333789395211031073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193309835111719193614708097 144982376333789395211031073)
    ·
      refine ⟨108736782250342046408273305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144982376333789395211031073 108736782250342046408273305)
      ·
        refine ⟨81552586687756534806204979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108736782250342046408273305 81552586687756534806204979)
        ·
          refine ⟨122328880031634802209307469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81552586687756534806204979 122328880031634802209307469)
          ·
            refine ⟨45873330011863050828490301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 122328880031634802209307469 45873330011863050828490301)
            ·
              refine ⟨17202498754448644060683863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45873330011863050828490301 17202498754448644060683863)
              ·
                refine ⟨25803748131672966091025795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17202498754448644060683863 25803748131672966091025795)
                ·
                  refine ⟨38705622197509449136538693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25803748131672966091025795 38705622197509449136538693)
                  ·
                    refine ⟨7257304162033021713101005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38705622197509449136538693 7257304162033021713101005)
                    ·
                      refine ⟨2721489060762383142412877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7257304162033021713101005 2721489060762383142412877)
                      ·
                        rfl

theorem cell23_5300081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 1, 1, 4, 3].length) (baseStart_5300081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5300081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5300081 prefixEnd_5300081 := by exact prefixLift 5300081
  have htrace : WordTrace (prefixWord ++ tailWord_5300081) baseStart_5300081 baseEnd_5300081 := by
    simpa [prefixWord, tailWord_5300081, baseEnd_5300081] using wordTrace_append hprefix tailTrace_5300081
  have hstable : (prefixWord ++ tailWord_5300081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5300081).length < 2 ^ (prefixWord ++ tailWord_5300081).sum := by decide
  have hdescent : baseEnd_5300081 < baseStart_5300081 := by decide
  rcases family_descends (prefixWord ++ tailWord_5300081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5300151 : List Nat := [1, 1, 3, 1, 3, 1, 1, 2, 5, 1, 4]
def baseStart_5300151 : Nat := 118140960795 + 5300151 * 2 ^ 59
def prefixEnd_5300151 : Nat := 4983230072969 + 3 ^ 40 * 5300151 * 2
def baseEnd_5300151 : Nat := 2721525004408197868537555

theorem tailTrace_5300151 : CollatzResearch.WordTrace tailWord_5300151 prefixEnd_5300151 2721525004408197868537555 := by
  unfold tailWord_5300151
  simp only [CollatzResearch.WordTrace]
  refine ⟨193312388221465595569756307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128874925480977063713170871 193312388221465595569756307)
  ·
    refine ⟨289968582332198393354634461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193312388221465595569756307 289968582332198393354634461)
    ·
      refine ⟨108738218374574397507987923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 289968582332198393354634461 108738218374574397507987923)
      ·
        refine ⟨163107327561861596261981885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108738218374574397507987923 163107327561861596261981885)
        ·
          refine ⟨61165247835698098598243207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 163107327561861596261981885 61165247835698098598243207)
          ·
            refine ⟨91747871753547147897364811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61165247835698098598243207 91747871753547147897364811)
            ·
              refine ⟨137621807630320721846047217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91747871753547147897364811 137621807630320721846047217)
              ·
                refine ⟨103216355722740541384535413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 137621807630320721846047217 103216355722740541384535413)
                ·
                  refine ⟨9676533349006925754800195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 103216355722740541384535413 9676533349006925754800195)
                  ·
                    refine ⟨14514800023510388632200293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9676533349006925754800195 14514800023510388632200293)
                    ·
                      refine ⟨2721525004408197868537555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14514800023510388632200293 2721525004408197868537555)
                      ·
                        rfl

theorem cell23_5300151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 5, 1, 4].length) (baseStart_5300151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5300151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5300151 prefixEnd_5300151 := by exact prefixLift 5300151
  have htrace : WordTrace (prefixWord ++ tailWord_5300151) baseStart_5300151 baseEnd_5300151 := by
    simpa [prefixWord, tailWord_5300151, baseEnd_5300151] using wordTrace_append hprefix tailTrace_5300151
  have hstable : (prefixWord ++ tailWord_5300151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5300151).length < 2 ^ (prefixWord ++ tailWord_5300151).sum := by decide
  have hdescent : baseEnd_5300151 < baseStart_5300151 := by decide
  rcases family_descends (prefixWord ++ tailWord_5300151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5300171 : List Nat := [1, 1, 1, 1, 3, 4, 1, 4, 1, 1, 5]
def baseStart_5300171 : Nat := 118140960795 + 5300171 * 2 ^ 59
def prefixEnd_5300171 : Nat := 4983230072969 + 3 ^ 40 * 5300171 * 2
def baseEnd_5300171 : Nat := 2721535274021287790287463

theorem tailTrace_5300171 : CollatzResearch.WordTrace tailWord_5300171 prefixEnd_5300171 2721535274021287790287463 := by
  unfold tailWord_5300171
  simp only [CollatzResearch.WordTrace]
  refine ⟨193313117681393138985484367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128875411787595425990322911 193313117681393138985484367)
  ·
    refine ⟨289969676522089708478226551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193313117681393138985484367 289969676522089708478226551)
    ·
      refine ⟨434954514783134562717339827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289969676522089708478226551 434954514783134562717339827)
      ·
        refine ⟨652431772174701844076009741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 434954514783134562717339827 652431772174701844076009741)
        ·
          refine ⟨244661914565513191528503653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 652431772174701844076009741 244661914565513191528503653)
          ·
            refine ⟨45874108981033723411594435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 244661914565513191528503653 45874108981033723411594435)
            ·
              refine ⟨68811163471550585117391653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45874108981033723411594435 68811163471550585117391653)
              ·
                refine ⟨12902093150915734709510935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68811163471550585117391653 12902093150915734709510935)
                ·
                  refine ⟨19353139726373602064266403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12902093150915734709510935 19353139726373602064266403)
                  ·
                    refine ⟨29029709589560403096399605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19353139726373602064266403 29029709589560403096399605)
                    ·
                      refine ⟨2721535274021287790287463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29029709589560403096399605 2721535274021287790287463)
                      ·
                        rfl

theorem cell23_5300171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 1, 1, 5].length) (baseStart_5300171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5300171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5300171 prefixEnd_5300171 := by exact prefixLift 5300171
  have htrace : WordTrace (prefixWord ++ tailWord_5300171) baseStart_5300171 baseEnd_5300171 := by
    simpa [prefixWord, tailWord_5300171, baseEnd_5300171] using wordTrace_append hprefix tailTrace_5300171
  have hstable : (prefixWord ++ tailWord_5300171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5300171).length < 2 ^ (prefixWord ++ tailWord_5300171).sum := by decide
  have hdescent : baseEnd_5300171 < baseStart_5300171 := by decide
  rcases family_descends (prefixWord ++ tailWord_5300171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5300191 : List Nat := [1, 1, 2, 3, 4, 1, 2, 9]
def baseStart_5300191 : Nat := 118140960795 + 5300191 * 2 ^ 59
def prefixEnd_5300191 : Nat := 4983230072969 + 3 ^ 40 * 5300191 * 2
def baseEnd_5300191 : Nat := 100797983097569544890273

theorem tailTrace_5300191 : CollatzResearch.WordTrace tailWord_5300191 prefixEnd_5300191 100797983097569544890273 := by
  unfold tailWord_5300191
  simp only [CollatzResearch.WordTrace]
  refine ⟨193313847141320682401212427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128875898094213788267474951 193313847141320682401212427)
  ·
    refine ⟨289970770711981023601818641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193313847141320682401212427 289970770711981023601818641)
    ·
      refine ⟨217478078033985767701363981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 289970770711981023601818641 217478078033985767701363981)
      ·
        refine ⟨81554279262744662888011493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 217478078033985767701363981 81554279262744662888011493)
        ·
          refine ⟨15291427361764624291502155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81554279262744662888011493 15291427361764624291502155)
          ·
            refine ⟨22937141042646936437253233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15291427361764624291502155 22937141042646936437253233)
            ·
              refine ⟨17202855781985202327939925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22937141042646936437253233 17202855781985202327939925)
              ·
                refine ⟨100797983097569544890273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17202855781985202327939925 100797983097569544890273)
                ·
                  rfl

theorem cell23_5300191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 9].length) (baseStart_5300191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5300191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5300191 prefixEnd_5300191 := by exact prefixLift 5300191
  have htrace : WordTrace (prefixWord ++ tailWord_5300191) baseStart_5300191 baseEnd_5300191 := by
    simpa [prefixWord, tailWord_5300191, baseEnd_5300191] using wordTrace_append hprefix tailTrace_5300191
  have hstable : (prefixWord ++ tailWord_5300191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5300191).length < 2 ^ (prefixWord ++ tailWord_5300191).sum := by decide
  have hdescent : baseEnd_5300191 < baseStart_5300191 := by decide
  rcases family_descends (prefixWord ++ tailWord_5300191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5300219 : List Nat := [1, 1, 1, 1, 1, 3, 8, 2, 1, 2, 2]
def baseStart_5300219 : Nat := 118140960795 + 5300219 * 2 ^ 59
def prefixEnd_5300219 : Nat := 4983230072969 + 3 ^ 40 * 5300219 * 2
def baseEnd_5300219 : Nat := 2721559921092703602487243

theorem tailTrace_5300219 : CollatzResearch.WordTrace tailWord_5300219 prefixEnd_5300219 2721559921092703602487243 := by
  unfold tailWord_5300219
  simp only [CollatzResearch.WordTrace]
  refine ⟨193314868385219243183231711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128876578923479495455487807 193314868385219243183231711)
  ·
    refine ⟨289972302577828864774847567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193314868385219243183231711 289972302577828864774847567)
    ·
      refine ⟨434958453866743297162271351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289972302577828864774847567 434958453866743297162271351)
      ·
        refine ⟨652437680800114945743407027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 434958453866743297162271351 652437680800114945743407027)
        ·
          refine ⟨978656521200172418615110541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 652437680800114945743407027 978656521200172418615110541)
          ·
            refine ⟨366996195450064656980666453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 978656521200172418615110541 366996195450064656980666453)
            ·
              refine ⟨4300736665430445198992185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 366996195450064656980666453 4300736665430445198992185)
              ·
                refine ⟨3225552499072833899244139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4300736665430445198992185 3225552499072833899244139)
                ·
                  refine ⟨4838328748609250848866209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3225552499072833899244139 4838328748609250848866209)
                  ·
                    refine ⟨3628746561456938136649657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4838328748609250848866209 3628746561456938136649657)
                    ·
                      refine ⟨2721559921092703602487243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3628746561456938136649657 2721559921092703602487243)
                      ·
                        rfl

theorem cell23_5300219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 8, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 8, 2, 1, 2, 2].length) (baseStart_5300219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5300219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5300219 prefixEnd_5300219 := by exact prefixLift 5300219
  have htrace : WordTrace (prefixWord ++ tailWord_5300219) baseStart_5300219 baseEnd_5300219 := by
    simpa [prefixWord, tailWord_5300219, baseEnd_5300219] using wordTrace_append hprefix tailTrace_5300219
  have hstable : (prefixWord ++ tailWord_5300219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5300219).length < 2 ^ (prefixWord ++ tailWord_5300219).sum := by decide
  have hdescent : baseEnd_5300219 < baseStart_5300219 := by decide
  rcases family_descends (prefixWord ++ tailWord_5300219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5300221 : List Nat := [1, 4, 1, 1, 1, 2, 3, 1, 2, 7]
def baseStart_5300221 : Nat := 118140960795 + 5300221 * 2 ^ 59
def prefixEnd_5300221 : Nat := 4983230072969 + 3 ^ 40 * 5300221 * 2
def baseEnd_5300221 : Nat := 907186982684670864887411

theorem tailTrace_5300221 : CollatzResearch.WordTrace tailWord_5300221 prefixEnd_5300221 907186982684670864887411 := by
  unfold tailWord_5300221
  simp only [CollatzResearch.WordTrace]
  refine ⟨193314941331211997524804517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128876627554141331683203011 193314941331211997524804517)
  ·
    refine ⟨36246551499602249535900847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 193314941331211997524804517 36246551499602249535900847)
    ·
      refine ⟨54369827249403374303851271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36246551499602249535900847 54369827249403374303851271)
      ·
        refine ⟨81554740874105061455776907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54369827249403374303851271 81554740874105061455776907)
        ·
          refine ⟨122332111311157592183665361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81554740874105061455776907 122332111311157592183665361)
          ·
            refine ⟨91749083483368194137749021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122332111311157592183665361 91749083483368194137749021)
            ·
              refine ⟨34405906306263072801655883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91749083483368194137749021 34405906306263072801655883)
              ·
                refine ⟨51608859459394609202483825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34405906306263072801655883 51608859459394609202483825)
                ·
                  refine ⟨38706644594545956901862869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51608859459394609202483825 38706644594545956901862869)
                  ·
                    refine ⟨907186982684670864887411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38706644594545956901862869 907186982684670864887411)
                    ·
                      rfl

theorem cell23_5300221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 2, 7].length) (baseStart_5300221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5300221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5300221 prefixEnd_5300221 := by exact prefixLift 5300221
  have htrace : WordTrace (prefixWord ++ tailWord_5300221) baseStart_5300221 baseEnd_5300221 := by
    simpa [prefixWord, tailWord_5300221, baseEnd_5300221] using wordTrace_append hprefix tailTrace_5300221
  have hstable : (prefixWord ++ tailWord_5300221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5300221).length < 2 ^ (prefixWord ++ tailWord_5300221).sum := by decide
  have hdescent : baseEnd_5300221 < baseStart_5300221 := by decide
  rcases family_descends (prefixWord ++ tailWord_5300221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5300235 : List Nat := [1, 1, 1, 1, 6, 1, 1, 5, 2, 1, 3]
def baseStart_5300235 : Nat := 118140960795 + 5300235 * 2 ^ 59
def prefixEnd_5300235 : Nat := 4983230072969 + 3 ^ 40 * 5300235 * 2
def baseEnd_5300235 : Nat := 2721568136783175539887169

theorem tailTrace_5300235 : CollatzResearch.WordTrace tailWord_5300235 prefixEnd_5300235 2721568136783175539887169 := by
  unfold tailWord_5300235
  simp only [CollatzResearch.WordTrace]
  refine ⟨193315451953161277915814159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128876967968774185277209439 193315451953161277915814159)
  ·
    refine ⟨289973177929741916873721239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193315451953161277915814159 289973177929741916873721239)
    ·
      refine ⟨434959766894612875310581859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289973177929741916873721239 434959766894612875310581859)
      ·
        refine ⟨652439650341919312965872789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 434959766894612875310581859 652439650341919312965872789)
        ·
          refine ⟨30583108609777467795275287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 652439650341919312965872789 30583108609777467795275287)
          ·
            refine ⟨45874662914666201692912931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30583108609777467795275287 45874662914666201692912931)
            ·
              refine ⟨68811994371999302539369397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45874662914666201692912931 68811994371999302539369397)
              ·
                refine ⟨6451124472374934613065881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 68811994371999302539369397 6451124472374934613065881)
                ·
                  refine ⟨4838343354281200959799411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6451124472374934613065881 4838343354281200959799411)
                  ·
                    refine ⟨7257515031421801439699117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4838343354281200959799411 7257515031421801439699117)
                    ·
                      refine ⟨2721568136783175539887169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7257515031421801439699117 2721568136783175539887169)
                      ·
                        rfl

theorem cell23_5300235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 5, 2, 1, 3].length) (baseStart_5300235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5300235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5300235 prefixEnd_5300235 := by exact prefixLift 5300235
  have htrace : WordTrace (prefixWord ++ tailWord_5300235) baseStart_5300235 baseEnd_5300235 := by
    simpa [prefixWord, tailWord_5300235, baseEnd_5300235] using wordTrace_append hprefix tailTrace_5300235
  have hstable : (prefixWord ++ tailWord_5300235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5300235).length < 2 ^ (prefixWord ++ tailWord_5300235).sum := by decide
  have hdescent : baseEnd_5300235 < baseStart_5300235 := by decide
  rcases family_descends (prefixWord ++ tailWord_5300235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5300286 : List Nat := [4, 2, 1, 3, 2, 1, 3, 1, 2, 1, 3]
def baseStart_5300286 : Nat := 118140960795 + 5300286 * 2 ^ 59
def prefixEnd_5300286 : Nat := 4983230072969 + 3 ^ 40 * 5300286 * 2
def baseEnd_5300286 : Nat := 2721594324296554840349435

theorem tailTrace_5300286 : CollatzResearch.WordTrace tailWord_5300286 prefixEnd_5300286 2721594324296554840349435 := by
  unfold tailWord_5300286
  simp only [CollatzResearch.WordTrace]
  refine ⟨24164664009497064203240089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128878208050651009083947141 24164664009497064203240089)
  ·
    refine ⟨18123498007122798152430067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24164664009497064203240089 18123498007122798152430067)
    ·
      refine ⟨27185247010684197228645101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18123498007122798152430067 27185247010684197228645101)
      ·
        refine ⟨10194467629006573960741913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27185247010684197228645101 10194467629006573960741913)
        ·
          refine ⟨7645850721754930470556435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10194467629006573960741913 7645850721754930470556435)
          ·
            refine ⟨11468776082632395705834653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7645850721754930470556435 11468776082632395705834653)
            ·
              refine ⟨4300791030987148389687995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11468776082632395705834653 4300791030987148389687995)
              ·
                refine ⟨6451186546480722584531993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4300791030987148389687995 6451186546480722584531993)
                ·
                  refine ⟨4838389909860541938398995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6451186546480722584531993 4838389909860541938398995)
                  ·
                    refine ⟨7257584864790812907598493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4838389909860541938398995 7257584864790812907598493)
                    ·
                      refine ⟨2721594324296554840349435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7257584864790812907598493 2721594324296554840349435)
                      ·
                        rfl

theorem cell23_5300286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_5300286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5300286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5300286 prefixEnd_5300286 := by exact prefixLift 5300286
  have htrace : WordTrace (prefixWord ++ tailWord_5300286) baseStart_5300286 baseEnd_5300286 := by
    simpa [prefixWord, tailWord_5300286, baseEnd_5300286] using wordTrace_append hprefix tailTrace_5300286
  have hstable : (prefixWord ++ tailWord_5300286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5300286).length < 2 ^ (prefixWord ++ tailWord_5300286).sum := by decide
  have hdescent : baseEnd_5300286 < baseStart_5300286 := by decide
  rcases family_descends (prefixWord ++ tailWord_5300286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5300288 : List Nat := [2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 4]
def baseStart_5300288 : Nat := 118140960795 + 5300288 * 2 ^ 59
def prefixEnd_5300288 : Nat := 4983230072969 + 3 ^ 40 * 5300288 * 2
def baseEnd_5300288 : Nat := 2721595351257863832524425

theorem tailTrace_5300288 : CollatzResearch.WordTrace tailWord_5300288 prefixEnd_5300288 2721595351257863832524425 := by
  unfold tailWord_5300288
  simp only [CollatzResearch.WordTrace]
  refine ⟨96658692510984633983746759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128878256681312845311662345 96658692510984633983746759)
  ·
    refine ⟨144988038766476950975620139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96658692510984633983746759 144988038766476950975620139)
    ·
      refine ⟨217482058149715426463430209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144988038766476950975620139 217482058149715426463430209)
      ·
        refine ⟨163111543612286569847572657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 217482058149715426463430209 163111543612286569847572657)
        ·
          refine ⟨122333657709214927385679493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163111543612286569847572657 122333657709214927385679493)
          ·
            refine ⟨22937560820477798884814905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 122333657709214927385679493 22937560820477798884814905)
            ·
              refine ⟨17203170615358349163611179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22937560820477798884814905 17203170615358349163611179)
              ·
                refine ⟨25804755923037523745416769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17203170615358349163611179 25804755923037523745416769)
                ·
                  refine ⟨19353566942278142809062577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25804755923037523745416769 19353566942278142809062577)
                  ·
                    refine ⟨14515175206708607106796933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19353566942278142809062577 14515175206708607106796933)
                    ·
                      refine ⟨2721595351257863832524425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14515175206708607106796933 2721595351257863832524425)
                      ·
                        rfl

theorem cell23_5300288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 4].length) (baseStart_5300288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5300288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5300288 prefixEnd_5300288 := by exact prefixLift 5300288
  have htrace : WordTrace (prefixWord ++ tailWord_5300288) baseStart_5300288 baseEnd_5300288 := by
    simpa [prefixWord, tailWord_5300288, baseEnd_5300288] using wordTrace_append hprefix tailTrace_5300288
  have hstable : (prefixWord ++ tailWord_5300288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5300288).length < 2 ^ (prefixWord ++ tailWord_5300288).sum := by decide
  have hdescent : baseEnd_5300288 < baseStart_5300288 := by decide
  rcases family_descends (prefixWord ++ tailWord_5300288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5300331 : List Nat := [1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 8]
def baseStart_5300331 : Nat := 118140960795 + 5300331 * 2 ^ 59
def prefixEnd_5300331 : Nat := 4983230072969 + 3 ^ 40 * 5300331 * 2
def baseEnd_5300331 : Nat := 2721617430926007164286727

theorem tailTrace_5300331 : CollatzResearch.WordTrace tailWord_5300331 prefixEnd_5300331 2721617430926007164286727 := by
  unfold tailWord_5300331
  simp only [CollatzResearch.WordTrace]
  refine ⟨193318953360813486311308847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128879302240542324207539231 193318953360813486311308847)
  ·
    refine ⟨289978430041220229466963271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193318953360813486311308847 289978430041220229466963271)
    ·
      refine ⟨434967645061830344200444907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289978430041220229466963271 434967645061830344200444907)
      ·
        refine ⟨652451467592745516300667361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 434967645061830344200444907 652451467592745516300667361)
        ·
          refine ⟨489338600694559137225500521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 652451467592745516300667361 489338600694559137225500521)
          ·
            refine ⟨367003950520919352919125391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 489338600694559137225500521 367003950520919352919125391)
            ·
              refine ⟨550505925781379029378688087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 367003950520919352919125391 550505925781379029378688087)
              ·
                refine ⟨825758888672068544068032131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 550505925781379029378688087 825758888672068544068032131)
                ·
                  refine ⟨1238638333008102816102048197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 825758888672068544068032131 1238638333008102816102048197)
                  ·
                    refine ⟨232244687439019278019134037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1238638333008102816102048197 232244687439019278019134037)
                    ·
                      refine ⟨2721617430926007164286727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 232244687439019278019134037 2721617430926007164286727)
                      ·
                        rfl

theorem cell23_5300331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 8].length) (baseStart_5300331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5300331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5300331 prefixEnd_5300331 := by exact prefixLift 5300331
  have htrace : WordTrace (prefixWord ++ tailWord_5300331) baseStart_5300331 baseEnd_5300331 := by
    simpa [prefixWord, tailWord_5300331, baseEnd_5300331] using wordTrace_append hprefix tailTrace_5300331
  have hstable : (prefixWord ++ tailWord_5300331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5300331).length < 2 ^ (prefixWord ++ tailWord_5300331).sum := by decide
  have hdescent : baseEnd_5300331 < baseStart_5300331 := by decide
  rcases family_descends (prefixWord ++ tailWord_5300331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5300332 : List Nat := [2, 2, 1, 1, 3, 4, 3, 2, 5]
def baseStart_5300332 : Nat := 118140960795 + 5300332 * 2 ^ 59
def prefixEnd_5300332 : Nat := 4983230072969 + 3 ^ 40 * 5300332 * 2
def baseEnd_5300332 : Nat := 302401993822962406708247

theorem tailTrace_5300332 : CollatzResearch.WordTrace tailWord_5300332 prefixEnd_5300332 302401993822962406708247 := by
  unfold tailWord_5300332
  simp only [CollatzResearch.WordTrace]
  refine ⟨96659494916904931741047625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128879326555873242321396833 96659494916904931741047625)
  ·
    refine ⟨72494621187678698805785719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96659494916904931741047625 72494621187678698805785719)
    ·
      refine ⟨108741931781518048208678579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72494621187678698805785719 108741931781518048208678579)
      ·
        refine ⟨163112897672277072313017869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108741931781518048208678579 163112897672277072313017869)
        ·
          refine ⟨61167336627103902117381701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 163112897672277072313017869 61167336627103902117381701)
          ·
            refine ⟨11468875617581981647009069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61167336627103902117381701 11468875617581981647009069)
            ·
              refine ⟨4300828356593243117628401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11468875617581981647009069 4300828356593243117628401)
              ·
                refine ⟨3225621267444932338221301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4300828356593243117628401 3225621267444932338221301)
                ·
                  refine ⟨302401993822962406708247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3225621267444932338221301 302401993822962406708247)
                  ·
                    rfl

theorem cell23_5300332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 3, 2, 5].length) (baseStart_5300332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5300332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5300332 prefixEnd_5300332 := by exact prefixLift 5300332
  have htrace : WordTrace (prefixWord ++ tailWord_5300332) baseStart_5300332 baseEnd_5300332 := by
    simpa [prefixWord, tailWord_5300332, baseEnd_5300332] using wordTrace_append hprefix tailTrace_5300332
  have hstable : (prefixWord ++ tailWord_5300332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5300332).length < 2 ^ (prefixWord ++ tailWord_5300332).sum := by decide
  have hdescent : baseEnd_5300332 < baseStart_5300332 := by decide
  rcases family_descends (prefixWord ++ tailWord_5300332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5300338 : List Nat := [3, 2, 1, 2, 2, 2, 1, 1, 1, 1, 7]
def baseStart_5300338 : Nat := 118140960795 + 5300338 * 2 ^ 59
def prefixEnd_5300338 : Nat := 4983230072969 + 3 ^ 40 * 5300338 * 2
def baseEnd_5300338 : Nat := 2721621025290588636899195

theorem tailTrace_5300338 : CollatzResearch.WordTrace tailWord_5300338 prefixEnd_5300338 2721621025290588636899195 := by
  unfold tailWord_5300338
  simp only [CollatzResearch.WordTrace]
  refine ⟨48329802167947031626703417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128879472447858751004542445 48329802167947031626703417)
  ·
    refine ⟨36247351625960273720027563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48329802167947031626703417 36247351625960273720027563)
    ·
      refine ⟨54371027438940410580041345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36247351625960273720027563 54371027438940410580041345)
      ·
        refine ⟨40778270579205307935031009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54371027438940410580041345 40778270579205307935031009)
        ·
          refine ⟨30583702934403980951273257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40778270579205307935031009 30583702934403980951273257)
          ·
            refine ⟨22937777200802985713454943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30583702934403980951273257 22937777200802985713454943)
            ·
              refine ⟨34406665801204478570182415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22937777200802985713454943 34406665801204478570182415)
              ·
                refine ⟨51609998701806717855273623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34406665801204478570182415 51609998701806717855273623)
                ·
                  refine ⟨77414998052710076782910435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51609998701806717855273623 77414998052710076782910435)
                  ·
                    refine ⟨116122497079065115174365653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 77414998052710076782910435 116122497079065115174365653)
                    ·
                      refine ⟨2721621025290588636899195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 116122497079065115174365653 2721621025290588636899195)
                      ·
                        rfl

theorem cell23_5300338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_5300338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5300338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5300338 prefixEnd_5300338 := by exact prefixLift 5300338
  have htrace : WordTrace (prefixWord ++ tailWord_5300338) baseStart_5300338 baseEnd_5300338 := by
    simpa [prefixWord, tailWord_5300338, baseEnd_5300338] using wordTrace_append hprefix tailTrace_5300338
  have hstable : (prefixWord ++ tailWord_5300338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5300338).length < 2 ^ (prefixWord ++ tailWord_5300338).sum := by decide
  have hdescent : baseEnd_5300338 < baseStart_5300338 := by decide
  rcases family_descends (prefixWord ++ tailWord_5300338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5300442 : List Nat := [3, 1, 1, 2, 2, 1, 2, 4, 2, 3, 2]
def baseStart_5300442 : Nat := 118140960795 + 5300442 * 2 ^ 59
def prefixEnd_5300442 : Nat := 4983230072969 + 3 ^ 40 * 5300442 * 2
def baseEnd_5300442 : Nat := 2721674427278656229998717

theorem tailTrace_5300442 : CollatzResearch.WordTrace tailWord_5300442 prefixEnd_5300442 2721674427278656229998717 := by
  unfold tailWord_5300442
  simp only [CollatzResearch.WordTrace]
  refine ⟨48330750465852838067149895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128882001242274234845733053 48330750465852838067149895)
  ·
    refine ⟨72496125698779257100724843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48330750465852838067149895 72496125698779257100724843)
    ·
      refine ⟨108744188548168885651087265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72496125698779257100724843 108744188548168885651087265)
      ·
        refine ⟨81558141411126664238315449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108744188548168885651087265 81558141411126664238315449)
        ·
          refine ⟨61168606058344998178736587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81558141411126664238315449 61168606058344998178736587)
          ·
            refine ⟨91752909087517497268104881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61168606058344998178736587 91752909087517497268104881)
            ·
              refine ⟨68814681815638122951078661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91752909087517497268104881 68814681815638122951078661)
              ·
                refine ⟨12902752840432148053327249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68814681815638122951078661 12902752840432148053327249)
                ·
                  refine ⟨9677064630324111039995437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12902752840432148053327249 9677064630324111039995437)
                  ·
                    refine ⟨3628899236371541639998289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9677064630324111039995437 3628899236371541639998289)
                    ·
                      refine ⟨2721674427278656229998717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3628899236371541639998289 2721674427278656229998717)
                      ·
                        rfl

theorem cell23_5300442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 4, 2, 3, 2].length) (baseStart_5300442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5300442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5300442 prefixEnd_5300442 := by exact prefixLift 5300442
  have htrace : WordTrace (prefixWord ++ tailWord_5300442) baseStart_5300442 baseEnd_5300442 := by
    simpa [prefixWord, tailWord_5300442, baseEnd_5300442] using wordTrace_append hprefix tailTrace_5300442
  have hstable : (prefixWord ++ tailWord_5300442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5300442).length < 2 ^ (prefixWord ++ tailWord_5300442).sum := by decide
  have hdescent : baseEnd_5300442 < baseStart_5300442 := by decide
  rcases family_descends (prefixWord ++ tailWord_5300442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5300449 : List Nat := [1, 2, 3, 1, 3, 1, 1, 6, 1, 1, 3]
def baseStart_5300449 : Nat := 118140960795 + 5300449 * 2 ^ 59
def prefixEnd_5300449 : Nat := 4983230072969 + 3 ^ 40 * 5300449 * 2
def baseEnd_5300449 : Nat := 2721678021643237702611185

theorem tailTrace_5300449 : CollatzResearch.WordTrace tailWord_5300449 prefixEnd_5300449 2721678021643237702611185 := by
  unfold tailWord_5300449
  simp only [CollatzResearch.WordTrace]
  refine ⟨193323257174385992464104401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128882171449590661642736267 193323257174385992464104401)
  ·
    refine ⟨144992442880789494348078301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193323257174385992464104401 144992442880789494348078301)
    ·
      refine ⟨54372166080296060380529363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144992442880789494348078301 54372166080296060380529363)
      ·
        refine ⟨81558249120444090570794045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54372166080296060380529363 81558249120444090570794045)
        ·
          refine ⟨30584343420166533964047767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81558249120444090570794045 30584343420166533964047767)
          ·
            refine ⟨45876515130249800946071651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30584343420166533964047767 45876515130249800946071651)
            ·
              refine ⟨68814772695374701419107477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45876515130249800946071651 68814772695374701419107477)
              ·
                refine ⟨3225692470095689129020663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 68814772695374701419107477 3225692470095689129020663)
                ·
                  refine ⟨4838538705143533693530995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3225692470095689129020663 4838538705143533693530995)
                  ·
                    refine ⟨7257808057715300540296493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4838538705143533693530995 7257808057715300540296493)
                    ·
                      refine ⟨2721678021643237702611185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7257808057715300540296493 2721678021643237702611185)
                      ·
                        rfl

theorem cell23_5300449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 6, 1, 1, 3].length) (baseStart_5300449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5300449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5300449 prefixEnd_5300449 := by exact prefixLift 5300449
  have htrace : WordTrace (prefixWord ++ tailWord_5300449) baseStart_5300449 baseEnd_5300449 := by
    simpa [prefixWord, tailWord_5300449, baseEnd_5300449] using wordTrace_append hprefix tailTrace_5300449
  have hstable : (prefixWord ++ tailWord_5300449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5300449).length < 2 ^ (prefixWord ++ tailWord_5300449).sum := by decide
  have hdescent : baseEnd_5300449 < baseStart_5300449 := by decide
  rcases family_descends (prefixWord ++ tailWord_5300449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5300465 : List Nat := [1, 2, 2, 2, 2, 1, 5, 1, 1, 6]
def baseStart_5300465 : Nat := 118140960795 + 5300465 * 2 ^ 59
def prefixEnd_5300465 : Nat := 4983230072969 + 3 ^ 40 * 5300465 * 2
def baseEnd_5300465 : Nat := 907228745777903213337037

theorem tailTrace_5300465 : CollatzResearch.WordTrace tailWord_5300465 prefixEnd_5300465 907228745777903213337037 := by
  unfold tailWord_5300465
  simp only [CollatzResearch.WordTrace]
  refine ⟨193323840742328027196686849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128882560494885351464457899 193323840742328027196686849)
  ·
    refine ⟨144992880556746020397515137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193323840742328027196686849 144992880556746020397515137)
    ·
      refine ⟨108744660417559515298136353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144992880556746020397515137 108744660417559515298136353)
      ·
        refine ⟨81558495313169636473602265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108744660417559515298136353 81558495313169636473602265)
        ·
          refine ⟨61168871484877227355201699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81558495313169636473602265 61168871484877227355201699)
          ·
            refine ⟨91753307227315841032802549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61168871484877227355201699 91753307227315841032802549)
            ·
              refine ⟨8601872552560860096825239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 91753307227315841032802549 8601872552560860096825239)
              ·
                refine ⟨12902808828841290145237859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8601872552560860096825239 12902808828841290145237859)
                ·
                  refine ⟨19354213243261935217856789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12902808828841290145237859 19354213243261935217856789)
                  ·
                    refine ⟨907228745777903213337037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19354213243261935217856789 907228745777903213337037)
                    ·
                      rfl

theorem cell23_5300465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 1, 1, 6].length) (baseStart_5300465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5300465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5300465 prefixEnd_5300465 := by exact prefixLift 5300465
  have htrace : WordTrace (prefixWord ++ tailWord_5300465) baseStart_5300465 baseEnd_5300465 := by
    simpa [prefixWord, tailWord_5300465, baseEnd_5300465] using wordTrace_append hprefix tailTrace_5300465
  have hstable : (prefixWord ++ tailWord_5300465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5300465).length < 2 ^ (prefixWord ++ tailWord_5300465).sum := by decide
  have hdescent : baseEnd_5300465 < baseStart_5300465 := by decide
  rcases family_descends (prefixWord ++ tailWord_5300465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5300492 : List Nat := [2, 2, 1, 2, 2, 2, 1, 5, 1, 2, 3]
def baseStart_5300492 : Nat := 118140960795 + 5300492 * 2 ^ 59
def prefixEnd_5300492 : Nat := 4983230072969 + 3 ^ 40 * 5300492 * 2
def baseEnd_5300492 : Nat := 2721700101311381034373487

theorem tailTrace_5300492 : CollatzResearch.WordTrace tailWord_5300492 prefixEnd_5300492 2721700101311381034373487 := by
  unfold tailWord_5300492
  simp only [CollatzResearch.WordTrace]
  refine ⟨96662412756615105403959865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128883217008820140538613153 96662412756615105403959865)
  ·
    refine ⟨72496809567461329052969899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96662412756615105403959865 72496809567461329052969899)
    ·
      refine ⟨108745214351191993579454849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72496809567461329052969899 108745214351191993579454849)
      ·
        refine ⟨81558910763393995184591137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108745214351191993579454849 81558910763393995184591137)
        ·
          refine ⟨61169183072545496388443353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81558910763393995184591137 61169183072545496388443353)
          ·
            refine ⟨45876887304409122291332515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61169183072545496388443353 45876887304409122291332515)
            ·
              refine ⟨68815330956613683436998773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45876887304409122291332515 68815330956613683436998773)
              ·
                refine ⟨6451437277182532822218635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 68815330956613683436998773 6451437277182532822218635)
                ·
                  refine ⟨9677155915773799233327953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6451437277182532822218635 9677155915773799233327953)
                  ·
                    refine ⟨7257866936830349424995965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9677155915773799233327953 7257866936830349424995965)
                    ·
                      refine ⟨2721700101311381034373487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7257866936830349424995965 2721700101311381034373487)
                      ·
                        rfl

theorem cell23_5300492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 5, 1, 2, 3].length) (baseStart_5300492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5300492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5300492 prefixEnd_5300492 := by exact prefixLift 5300492
  have htrace : WordTrace (prefixWord ++ tailWord_5300492) baseStart_5300492 baseEnd_5300492 := by
    simpa [prefixWord, tailWord_5300492, baseEnd_5300492] using wordTrace_append hprefix tailTrace_5300492
  have hstable : (prefixWord ++ tailWord_5300492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5300492).length < 2 ^ (prefixWord ++ tailWord_5300492).sum := by decide
  have hdescent : baseEnd_5300492 < baseStart_5300492 := by decide
  rcases family_descends (prefixWord ++ tailWord_5300492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5300516 : List Nat := [2, 3, 1, 3, 1, 4, 2, 1, 2, 4]
def baseStart_5300516 : Nat := 118140960795 + 5300516 * 2 ^ 59
def prefixEnd_5300516 : Nat := 4983230072969 + 3 ^ 40 * 5300516 * 2
def baseEnd_5300516 : Nat := 907237474949029646824459

theorem tailTrace_5300516 : CollatzResearch.WordTrace tailWord_5300516 prefixEnd_5300516 907237474949029646824459 := by
  unfold tailWord_5300516
  simp only [CollatzResearch.WordTrace]
  refine ⟨96662850432571631453396701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128883800576762175271195601 96662850432571631453396701)
  ·
    refine ⟨36248568912214361795023763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96662850432571631453396701 36248568912214361795023763)
    ·
      refine ⟨54372853368321542692535645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36248568912214361795023763 54372853368321542692535645)
      ·
        refine ⟨20389820013120578509700867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54372853368321542692535645 20389820013120578509700867)
        ·
          refine ⟨30584730019680867764551301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20389820013120578509700867 30584730019680867764551301)
          ·
            refine ⟨5734636878690162705853369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30584730019680867764551301 5734636878690162705853369)
            ·
              refine ⟨4300977659017622029390027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5734636878690162705853369 4300977659017622029390027)
              ·
                refine ⟨6451466488526433044085041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4300977659017622029390027 6451466488526433044085041)
                ·
                  refine ⟨4838599866394824783063781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6451466488526433044085041 4838599866394824783063781)
                  ·
                    refine ⟨907237474949029646824459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4838599866394824783063781 907237474949029646824459)
                    ·
                      rfl

theorem cell23_5300516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 2, 1, 2, 4].length) (baseStart_5300516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5300516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5300516 prefixEnd_5300516 := by exact prefixLift 5300516
  have htrace : WordTrace (prefixWord ++ tailWord_5300516) baseStart_5300516 baseEnd_5300516 := by
    simpa [prefixWord, tailWord_5300516, baseEnd_5300516] using wordTrace_append hprefix tailTrace_5300516
  have hstable : (prefixWord ++ tailWord_5300516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5300516).length < 2 ^ (prefixWord ++ tailWord_5300516).sum := by decide
  have hdescent : baseEnd_5300516 < baseStart_5300516 := by decide
  rcases family_descends (prefixWord ++ tailWord_5300516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5300526 : List Nat := [4, 1, 3, 3, 1, 1, 1, 1, 3, 2, 3]
def baseStart_5300526 : Nat := 118140960795 + 5300526 * 2 ^ 59
def prefixEnd_5300526 : Nat := 4983230072969 + 3 ^ 40 * 5300526 * 2
def baseEnd_5300526 : Nat := 2721717559653633901348331

theorem tailTrace_5300526 : CollatzResearch.WordTrace tailWord_5300526 prefixEnd_5300526 2721717559653633901348331 := by
  unfold tailWord_5300526
  simp only [CollatzResearch.WordTrace]
  refine ⟨24165758199388379326832179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128884043730071356409771621 24165758199388379326832179)
  ·
    refine ⟨36248637299082568990248269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24165758199388379326832179 36248637299082568990248269)
    ·
      refine ⟨13593238987155963371343101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36248637299082568990248269 13593238987155963371343101)
      ·
        refine ⟨5097464620183486264253663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13593238987155963371343101 5097464620183486264253663)
        ·
          refine ⟨7646196930275229396380495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5097464620183486264253663 7646196930275229396380495)
          ·
            refine ⟨11469295395412844094570743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7646196930275229396380495 11469295395412844094570743)
            ·
              refine ⟨17203943093119266141856115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11469295395412844094570743 17203943093119266141856115)
              ·
                refine ⟨25805914639678899212784173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17203943093119266141856115 25805914639678899212784173)
                ·
                  refine ⟨9677217989879587204794065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25805914639678899212784173 9677217989879587204794065)
                  ·
                    refine ⟨7257913492409690403595549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9677217989879587204794065 7257913492409690403595549)
                    ·
                      refine ⟨2721717559653633901348331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7257913492409690403595549 2721717559653633901348331)
                      ·
                        rfl

theorem cell23_5300526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_5300526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5300526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5300526 prefixEnd_5300526 := by exact prefixLift 5300526
  have htrace : WordTrace (prefixWord ++ tailWord_5300526) baseStart_5300526 baseEnd_5300526 := by
    simpa [prefixWord, tailWord_5300526, baseEnd_5300526] using wordTrace_append hprefix tailTrace_5300526
  have hstable : (prefixWord ++ tailWord_5300526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5300526).length < 2 ^ (prefixWord ++ tailWord_5300526).sum := by decide
  have hdescent : baseEnd_5300526 < baseStart_5300526 := by decide
  rcases family_descends (prefixWord ++ tailWord_5300526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5300575 : List Nat := [1, 1, 2, 3, 1, 2, 3, 1, 1, 4, 4]
def baseStart_5300575 : Nat := 118140960795 + 5300575 * 2 ^ 59
def prefixEnd_5300575 : Nat := 4983230072969 + 3 ^ 40 * 5300575 * 2
def baseEnd_5300575 : Nat := 2721742720205704209635605

theorem tailTrace_5300575 : CollatzResearch.WordTrace tailWord_5300575 prefixEnd_5300575 2721742720205704209635605 := by
  unfold tailWord_5300575
  simp only [CollatzResearch.WordTrace]
  refine ⟨193327852771929515983191179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128885235181286343988794119 193327852771929515983191179)
  ·
    refine ⟨289991779157894273974786769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193327852771929515983191179 289991779157894273974786769)
    ·
      refine ⟨217493834368420705481090077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 289991779157894273974786769 217493834368420705481090077)
      ·
        refine ⟨81560187888157764555408779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 217493834368420705481090077 81560187888157764555408779)
        ·
          refine ⟨122340281832236646833113169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81560187888157764555408779 122340281832236646833113169)
          ·
            refine ⟨91755211374177485124834877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122340281832236646833113169 91755211374177485124834877)
            ·
              refine ⟨34408204265316556921813079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91755211374177485124834877 34408204265316556921813079)
              ·
                refine ⟨51612306397974835382719619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34408204265316556921813079 51612306397974835382719619)
                ·
                  refine ⟨77418459596962253074079429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51612306397974835382719619 77418459596962253074079429)
                  ·
                    refine ⟨14515961174430422451389893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 77418459596962253074079429 14515961174430422451389893)
                    ·
                      refine ⟨2721742720205704209635605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14515961174430422451389893 2721742720205704209635605)
                      ·
                        rfl

theorem cell23_5300575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 4, 4].length) (baseStart_5300575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5300575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5300575 prefixEnd_5300575 := by exact prefixLift 5300575
  have htrace : WordTrace (prefixWord ++ tailWord_5300575) baseStart_5300575 baseEnd_5300575 := by
    simpa [prefixWord, tailWord_5300575, baseEnd_5300575] using wordTrace_append hprefix tailTrace_5300575
  have hstable : (prefixWord ++ tailWord_5300575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5300575).length < 2 ^ (prefixWord ++ tailWord_5300575).sum := by decide
  have hdescent : baseEnd_5300575 < baseStart_5300575 := by decide
  rcases family_descends (prefixWord ++ tailWord_5300575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5300579 : List Nat := [1, 1, 1, 5, 2, 1, 4, 1, 1, 4, 2]
def baseStart_5300579 : Nat := 118140960795 + 5300579 * 2 ^ 59
def prefixEnd_5300579 : Nat := 4983230072969 + 3 ^ 40 * 5300579 * 2
def baseEnd_5300579 : Nat := 2721744774128322193985587

theorem tailTrace_5300579 : CollatzResearch.WordTrace tailWord_5300579 prefixEnd_5300579 2721744774128322193985587 := by
  unfold tailWord_5300579
  simp only [CollatzResearch.WordTrace]
  refine ⟨193327998663915024666336791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128885332442610016444224527 193327998663915024666336791)
  ·
    refine ⟨289991997995872536999505187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193327998663915024666336791 289991997995872536999505187)
    ·
      refine ⟨434987996993808805499257781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289991997995872536999505187 434987996993808805499257781)
      ·
        refine ⟨40780124718169575515555417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 434987996993808805499257781 40780124718169575515555417)
        ·
          refine ⟨30585093538627181636666563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40780124718169575515555417 30585093538627181636666563)
          ·
            refine ⟨45877640307940772454999845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30585093538627181636666563 45877640307940772454999845)
            ·
              refine ⟨8602057557738894835312471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45877640307940772454999845 8602057557738894835312471)
              ·
                refine ⟨12903086336608342252968707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8602057557738894835312471 12903086336608342252968707)
                ·
                  refine ⟨19354629504912513379453061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12903086336608342252968707 19354629504912513379453061)
                  ·
                    refine ⟨3628993032171096258647449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19354629504912513379453061 3628993032171096258647449)
                    ·
                      refine ⟨2721744774128322193985587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3628993032171096258647449 2721744774128322193985587)
                      ·
                        rfl

theorem cell23_5300579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 1, 1, 4, 2].length) (baseStart_5300579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5300579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5300579 prefixEnd_5300579 := by exact prefixLift 5300579
  have htrace : WordTrace (prefixWord ++ tailWord_5300579) baseStart_5300579 baseEnd_5300579 := by
    simpa [prefixWord, tailWord_5300579, baseEnd_5300579] using wordTrace_append hprefix tailTrace_5300579
  have hstable : (prefixWord ++ tailWord_5300579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5300579).length < 2 ^ (prefixWord ++ tailWord_5300579).sum := by decide
  have hdescent : baseEnd_5300579 < baseStart_5300579 := by decide
  rcases family_descends (prefixWord ++ tailWord_5300579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5300585 : List Nat := [1, 2, 1, 1, 1, 3, 5, 2, 7]
def baseStart_5300585 : Nat := 118140960795 + 5300585 * 2 ^ 59
def prefixEnd_5300585 : Nat := 4983230072969 + 3 ^ 40 * 5300585 * 2
def baseEnd_5300585 : Nat := 302416428334694352278951

theorem tailTrace_5300585 : CollatzResearch.WordTrace tailWord_5300585 prefixEnd_5300585 302416428334694352278951 := by
  unfold tailWord_5300585
  simp only [CollatzResearch.WordTrace]
  refine ⟨193328217501893287691055209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128885478334595525127370139 193328217501893287691055209)
  ·
    refine ⟨144996163126419965768291407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193328217501893287691055209 144996163126419965768291407)
    ·
      refine ⟨217494244689629948652437111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144996163126419965768291407 217494244689629948652437111)
      ·
        refine ⟨326241367034444922978655667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217494244689629948652437111 326241367034444922978655667)
        ·
          refine ⟨489362050551667384467983501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 326241367034444922978655667 489362050551667384467983501)
          ·
            refine ⟨183510768956875269175493813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 489362050551667384467983501 183510768956875269175493813)
            ·
              refine ⟨17204134589707056485202545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 183510768956875269175493813 17204134589707056485202545)
              ·
                refine ⟨12903100942280292363901909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17204134589707056485202545 12903100942280292363901909)
                ·
                  refine ⟨302416428334694352278951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12903100942280292363901909 302416428334694352278951)
                  ·
                    rfl

theorem cell23_5300585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 2, 7].length) (baseStart_5300585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5300585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5300585 prefixEnd_5300585 := by exact prefixLift 5300585
  have htrace : WordTrace (prefixWord ++ tailWord_5300585) baseStart_5300585 baseEnd_5300585 := by
    simpa [prefixWord, tailWord_5300585, baseEnd_5300585] using wordTrace_append hprefix tailTrace_5300585
  have hstable : (prefixWord ++ tailWord_5300585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5300585).length < 2 ^ (prefixWord ++ tailWord_5300585).sum := by decide
  have hdescent : baseEnd_5300585 < baseStart_5300585 := by decide
  rcases family_descends (prefixWord ++ tailWord_5300585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5300612 : List Nat := [2, 3, 2, 1, 1, 2, 1, 1, 4, 3, 3]
def baseStart_5300612 : Nat := 118140960795 + 5300612 * 2 ^ 59
def prefixEnd_5300612 : Nat := 4983230072969 + 3 ^ 40 * 5300612 * 2
def baseEnd_5300612 : Nat := 2721761718989920564872935

theorem tailTrace_5300612 : CollatzResearch.WordTrace tailWord_5300612 prefixEnd_5300612 2721761718989920564872935 := by
  unfold tailWord_5300612
  simp only [CollatzResearch.WordTrace]
  refine ⟨96664601136397735651144045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128886134848530314201525393 96664601136397735651144045)
  ·
    refine ⟨36249225426149150869179017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96664601136397735651144045 36249225426149150869179017)
    ·
      refine ⟨27186919069611863151884263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36249225426149150869179017 27186919069611863151884263)
      ·
        refine ⟨40780378604417794727826395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27186919069611863151884263 40780378604417794727826395)
        ·
          refine ⟨61170567906626692091739593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40780378604417794727826395 61170567906626692091739593)
          ·
            refine ⟨45877925929970019068804695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61170567906626692091739593 45877925929970019068804695)
            ·
              refine ⟨68816888894955028603207043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45877925929970019068804695 68816888894955028603207043)
              ·
                refine ⟨103225333342432542904810565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68816888894955028603207043 103225333342432542904810565)
                ·
                  refine ⟨19354750001706101794651981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 103225333342432542904810565 19354750001706101794651981)
                  ·
                    refine ⟨7258031250639788172994493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19354750001706101794651981 7258031250639788172994493)
                    ·
                      refine ⟨2721761718989920564872935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7258031250639788172994493 2721761718989920564872935)
                      ·
                        rfl

theorem cell23_5300612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 4, 3, 3].length) (baseStart_5300612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5300612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5300612 prefixEnd_5300612 := by exact prefixLift 5300612
  have htrace : WordTrace (prefixWord ++ tailWord_5300612) baseStart_5300612 baseEnd_5300612 := by
    simpa [prefixWord, tailWord_5300612, baseEnd_5300612] using wordTrace_append hprefix tailTrace_5300612
  have hstable : (prefixWord ++ tailWord_5300612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5300612).length < 2 ^ (prefixWord ++ tailWord_5300612).sum := by decide
  have hdescent : baseEnd_5300612 < baseStart_5300612 := by decide
  rcases family_descends (prefixWord ++ tailWord_5300612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5300632 : List Nat := [2, 1, 2, 5, 1, 1, 1, 2, 1, 7]
def baseStart_5300632 : Nat := 118140960795 + 5300632 * 2 ^ 59
def prefixEnd_5300632 : Nat := 4983230072969 + 3 ^ 40 * 5300632 * 2
def baseEnd_5300632 : Nat := 907257329534336828874281

theorem tailTrace_5300632 : CollatzResearch.WordTrace tailWord_5300632 prefixEnd_5300632 907257329534336828874281 := by
  unfold tailWord_5300632
  simp only [CollatzResearch.WordTrace]
  refine ⟨96664965866361507359008075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128886621155148676478677433 96664965866361507359008075)
  ·
    refine ⟨144997448799542261038512113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96664965866361507359008075 144997448799542261038512113)
    ·
      refine ⟨108748086599656695778884085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144997448799542261038512113 108748086599656695778884085)
      ·
        refine ⟨10195133118717815229270383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 108748086599656695778884085 10195133118717815229270383)
        ·
          refine ⟨15292699678076722843905575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10195133118717815229270383 15292699678076722843905575)
          ·
            refine ⟨22939049517115084265858363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15292699678076722843905575 22939049517115084265858363)
            ·
              refine ⟨34408574275672626398787545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22939049517115084265858363 34408574275672626398787545)
              ·
                refine ⟨25806430706754469799090659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34408574275672626398787545 25806430706754469799090659)
                ·
                  refine ⟨38709646060131704698635989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25806430706754469799090659 38709646060131704698635989)
                  ·
                    refine ⟨907257329534336828874281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38709646060131704698635989 907257329534336828874281)
                    ·
                      rfl

theorem cell23_5300632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 2, 1, 7].length) (baseStart_5300632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5300632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5300632 prefixEnd_5300632 := by exact prefixLift 5300632
  have htrace : WordTrace (prefixWord ++ tailWord_5300632) baseStart_5300632 baseEnd_5300632 := by
    simpa [prefixWord, tailWord_5300632, baseEnd_5300632] using wordTrace_append hprefix tailTrace_5300632
  have hstable : (prefixWord ++ tailWord_5300632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5300632).length < 2 ^ (prefixWord ++ tailWord_5300632).sum := by decide
  have hdescent : baseEnd_5300632 < baseStart_5300632 := by decide
  rcases family_descends (prefixWord ++ tailWord_5300632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5300645 : List Nat := [1, 3, 1, 2, 1, 1, 3, 1, 2, 8]
def baseStart_5300645 : Nat := 118140960795 + 5300645 * 2 ^ 59
def prefixEnd_5300645 : Nat := 4983230072969 + 3 ^ 40 * 5300645 * 2
def baseEnd_5300645 : Nat := 907259554617172978586761

theorem tailTrace_5300645 : CollatzResearch.WordTrace tailWord_5300645 prefixEnd_5300645 907259554617172978586761 := by
  unfold tailWord_5300645
  simp only [CollatzResearch.WordTrace]
  refine ⟨193330405881675917938239389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128886937254450611958826259 193330405881675917938239389)
  ·
    refine ⟨72498902205628469226839771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 193330405881675917938239389 72498902205628469226839771)
    ·
      refine ⟨108748353308442703840259657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72498902205628469226839771 108748353308442703840259657)
      ·
        refine ⟨81561264981332027880194743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108748353308442703840259657 81561264981332027880194743)
        ·
          refine ⟨122341897471998041820292115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81561264981332027880194743 122341897471998041820292115)
          ·
            refine ⟨183512846207997062730438173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122341897471998041820292115 183512846207997062730438173)
            ·
              refine ⟨68817317327998898523914315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 183512846207997062730438173 68817317327998898523914315)
              ·
                refine ⟨103225975991998347785871473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68817317327998898523914315 103225975991998347785871473)
                ·
                  refine ⟨77419481993998760839403605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 103225975991998347785871473 77419481993998760839403605)
                  ·
                    refine ⟨907259554617172978586761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 77419481993998760839403605 907259554617172978586761)
                    ·
                      rfl

theorem cell23_5300645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 8].length) (baseStart_5300645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5300645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5300645 prefixEnd_5300645 := by exact prefixLift 5300645
  have htrace : WordTrace (prefixWord ++ tailWord_5300645) baseStart_5300645 baseEnd_5300645 := by
    simpa [prefixWord, tailWord_5300645, baseEnd_5300645] using wordTrace_append hprefix tailTrace_5300645
  have hstable : (prefixWord ++ tailWord_5300645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5300645).length < 2 ^ (prefixWord ++ tailWord_5300645).sum := by decide
  have hdescent : baseEnd_5300645 < baseStart_5300645 := by decide
  rcases family_descends (prefixWord ++ tailWord_5300645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5300652 : List Nat := [2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 4]
def baseStart_5300652 : Nat := 118140960795 + 5300652 * 2 ^ 59
def prefixEnd_5300652 : Nat := 4983230072969 + 3 ^ 40 * 5300652 * 2
def baseEnd_5300652 : Nat := 2721782258216100408372751

theorem tailTrace_5300652 : CollatzResearch.WordTrace tailWord_5300652 prefixEnd_5300652 2721782258216100408372751 := by
  unfold tailWord_5300652
  simp only [CollatzResearch.WordTrace]
  refine ⟨96665330596325279066872105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128887107461767038755829473 96665330596325279066872105)
  ·
    refine ⟨72498997947243959300154079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96665330596325279066872105 72498997947243959300154079)
    ·
      refine ⟨108748496920865938950231119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72498997947243959300154079 108748496920865938950231119)
      ·
        refine ⟨163122745381298908425346679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108748496920865938950231119 163122745381298908425346679)
        ·
          refine ⟨244684118071948362638020019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163122745381298908425346679 244684118071948362638020019)
          ·
            refine ⟨367026177107922543957030029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 244684118071948362638020019 367026177107922543957030029)
            ·
              refine ⟨137634816415470953983886261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 367026177107922543957030029 137634816415470953983886261)
              ·
                refine ⟨12903264038950401935989337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 137634816415470953983886261 12903264038950401935989337)
                ·
                  refine ⟨9677448029212801451992003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12903264038950401935989337 9677448029212801451992003)
                  ·
                    refine ⟨14516172043819202177988005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9677448029212801451992003 14516172043819202177988005)
                    ·
                      refine ⟨2721782258216100408372751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14516172043819202177988005 2721782258216100408372751)
                      ·
                        rfl

theorem cell23_5300652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 4].length) (baseStart_5300652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5300652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5300652 prefixEnd_5300652 := by exact prefixLift 5300652
  have htrace : WordTrace (prefixWord ++ tailWord_5300652) baseStart_5300652 baseEnd_5300652 := by
    simpa [prefixWord, tailWord_5300652, baseEnd_5300652] using wordTrace_append hprefix tailTrace_5300652
  have hstable : (prefixWord ++ tailWord_5300652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5300652).length < 2 ^ (prefixWord ++ tailWord_5300652).sum := by decide
  have hdescent : baseEnd_5300652 < baseStart_5300652 := by decide
  rcases family_descends (prefixWord ++ tailWord_5300652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5300653 : List Nat := [1, 5, 2, 2, 2, 2, 1, 3, 5]
def baseStart_5300653 : Nat := 118140960795 + 5300653 * 2 ^ 59
def prefixEnd_5300653 : Nat := 4983230072969 + 3 ^ 40 * 5300653 * 2
def baseEnd_5300653 : Nat := 302420307966306100495583

theorem tailTrace_5300653 : CollatzResearch.WordTrace tailWord_5300653 prefixEnd_5300653 302420307966306100495583 := by
  unfold tailWord_5300653
  simp only [CollatzResearch.WordTrace]
  refine ⟨193330697665646935304530613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128887131777097956869687075 193330697665646935304530613)
  ·
    refine ⟨18124752906154400184799745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 193330697665646935304530613 18124752906154400184799745)
    ·
      refine ⟨13593564679615800138599809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18124752906154400184799745 13593564679615800138599809)
      ·
        refine ⟨10195173509711850103949857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13593564679615800138599809 10195173509711850103949857)
        ·
          refine ⟨7646380132283887577962393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10195173509711850103949857 7646380132283887577962393)
          ·
            refine ⟨5734785099212915683471795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7646380132283887577962393 5734785099212915683471795)
            ·
              refine ⟨8602177648819373525207693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5734785099212915683471795 8602177648819373525207693)
              ·
                refine ⟨3225816618307265071952885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8602177648819373525207693 3225816618307265071952885)
                ·
                  refine ⟨302420307966306100495583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3225816618307265071952885 302420307966306100495583)
                  ·
                    rfl

theorem cell23_5300653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 3, 5].length) (baseStart_5300653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5300653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5300653 prefixEnd_5300653 := by exact prefixLift 5300653
  have htrace : WordTrace (prefixWord ++ tailWord_5300653) baseStart_5300653 baseEnd_5300653 := by
    simpa [prefixWord, tailWord_5300653, baseEnd_5300653] using wordTrace_append hprefix tailTrace_5300653
  have hstable : (prefixWord ++ tailWord_5300653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5300653).length < 2 ^ (prefixWord ++ tailWord_5300653).sum := by decide
  have hdescent : baseEnd_5300653 < baseStart_5300653 := by decide
  rcases family_descends (prefixWord ++ tailWord_5300653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5300655 : List Nat := [1, 1, 2, 1, 2, 2, 1, 1, 4, 3, 5]
def baseStart_5300655 : Nat := 118140960795 + 5300655 * 2 ^ 59
def prefixEnd_5300655 : Nat := 4983230072969 + 3 ^ 40 * 5300655 * 2
def baseEnd_5300655 : Nat := 2721783798658063896635237

theorem tailTrace_5300655 : CollatzResearch.WordTrace tailWord_5300655 prefixEnd_5300655 2721783798658063896635237 := by
  unfold tailWord_5300655
  simp only [CollatzResearch.WordTrace]
  refine ⟨193330770611639689646103419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128887180407759793097402279 193330770611639689646103419)
  ·
    refine ⟨289996155917459534469155129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193330770611639689646103419 289996155917459534469155129)
    ·
      refine ⟨217497116938094650851866347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 289996155917459534469155129 217497116938094650851866347)
      ·
        refine ⟨326245675407141976277799521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217497116938094650851866347 326245675407141976277799521)
        ·
          refine ⟨244684256555356482208349641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 326245675407141976277799521 244684256555356482208349641)
          ·
            refine ⟨183513192416517361656262231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 244684256555356482208349641 183513192416517361656262231)
            ·
              refine ⟨275269788624776042484393347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 183513192416517361656262231 275269788624776042484393347)
              ·
                refine ⟨412904682937164063726590021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 275269788624776042484393347 412904682937164063726590021)
                ·
                  refine ⟨77419628050718261948735629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 412904682937164063726590021 77419628050718261948735629)
                  ·
                    refine ⟨29032360519019348230775861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 77419628050718261948735629 29032360519019348230775861)
                    ·
                      refine ⟨2721783798658063896635237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29032360519019348230775861 2721783798658063896635237)
                      ·
                        rfl

theorem cell23_5300655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 3, 5].length) (baseStart_5300655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5300655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5300655 prefixEnd_5300655 := by exact prefixLift 5300655
  have htrace : WordTrace (prefixWord ++ tailWord_5300655) baseStart_5300655 baseEnd_5300655 := by
    simpa [prefixWord, tailWord_5300655, baseEnd_5300655] using wordTrace_append hprefix tailTrace_5300655
  have hstable : (prefixWord ++ tailWord_5300655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5300655).length < 2 ^ (prefixWord ++ tailWord_5300655).sum := by decide
  have hdescent : baseEnd_5300655 < baseStart_5300655 := by decide
  rcases family_descends (prefixWord ++ tailWord_5300655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5300669 : List Nat := [1, 4, 1, 2, 2, 3, 1, 2, 2, 1, 4]
def baseStart_5300669 : Nat := 118140960795 + 5300669 * 2 ^ 59
def prefixEnd_5300669 : Nat := 4983230072969 + 3 ^ 40 * 5300669 * 2
def baseEnd_5300669 : Nat := 2721790987387226841860173

theorem tailTrace_5300669 : CollatzResearch.WordTrace tailWord_5300669 prefixEnd_5300669 2721790987387226841860173 := by
  unfold tailWord_5300669
  simp only [CollatzResearch.WordTrace]
  refine ⟨193331281233588970037113061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128887520822392646691408707 193331281233588970037113061)
  ·
    refine ⟨36249615231297931881958699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 193331281233588970037113061 36249615231297931881958699)
    ·
      refine ⟨54374422846946897822938049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36249615231297931881958699 54374422846946897822938049)
      ·
        refine ⟨40780817135210173367203537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54374422846946897822938049 40780817135210173367203537)
        ·
          refine ⟨30585612851407630025402653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40780817135210173367203537 30585612851407630025402653)
          ·
            refine ⟨11469604819277861259525995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30585612851407630025402653 11469604819277861259525995)
            ·
              refine ⟨17204407228916791889288993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11469604819277861259525995 17204407228916791889288993)
              ·
                refine ⟨12903305421687593916966745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17204407228916791889288993 12903305421687593916966745)
                ·
                  refine ⟨9677479066265695437725059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12903305421687593916966745 9677479066265695437725059)
                  ·
                    refine ⟨14516218599398543156587589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9677479066265695437725059 14516218599398543156587589)
                    ·
                      refine ⟨2721790987387226841860173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14516218599398543156587589 2721790987387226841860173)
                      ·
                        rfl

theorem cell23_5300669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 2, 2, 1, 4].length) (baseStart_5300669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5300669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5300669 prefixEnd_5300669 := by exact prefixLift 5300669
  have htrace : WordTrace (prefixWord ++ tailWord_5300669) baseStart_5300669 baseEnd_5300669 := by
    simpa [prefixWord, tailWord_5300669, baseEnd_5300669] using wordTrace_append hprefix tailTrace_5300669
  have hstable : (prefixWord ++ tailWord_5300669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5300669).length < 2 ^ (prefixWord ++ tailWord_5300669).sum := by decide
  have hdescent : baseEnd_5300669 < baseStart_5300669 := by decide
  rcases family_descends (prefixWord ++ tailWord_5300669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5300679 : List Nat := [1, 1, 4, 1, 1, 4, 3, 1, 3, 4]
def baseStart_5300679 : Nat := 118140960795 + 5300679 * 2 ^ 59
def prefixEnd_5300679 : Nat := 4983230072969 + 3 ^ 40 * 5300679 * 2
def baseEnd_5300679 : Nat := 907265374064590600911709

theorem tailTrace_5300679 : CollatzResearch.WordTrace tailWord_5300679 prefixEnd_5300679 907265374064590600911709 := by
  unfold tailWord_5300679
  simp only [CollatzResearch.WordTrace]
  refine ⟨193331645963552741744977091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128887763975701827829984727 193331645963552741744977091)
  ·
    refine ⟨289997468945329112617465637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193331645963552741744977091 289997468945329112617465637)
    ·
      refine ⟨54374525427249208615774807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 289997468945329112617465637 54374525427249208615774807)
      ·
        refine ⟨81561788140873812923662211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54374525427249208615774807 81561788140873812923662211)
        ·
          refine ⟨122342682211310719385493317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81561788140873812923662211 122342682211310719385493317)
          ·
            refine ⟨22939252914620759884779997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 122342682211310719385493317 22939252914620759884779997)
            ·
              refine ⟨8602219842982784956792499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22939252914620759884779997 8602219842982784956792499)
              ·
                refine ⟨12903329764474177435188749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8602219842982784956792499 12903329764474177435188749)
                ·
                  refine ⟨4838748661677816538195781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12903329764474177435188749 4838748661677816538195781)
                  ·
                    refine ⟨907265374064590600911709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4838748661677816538195781 907265374064590600911709)
                    ·
                      rfl

theorem cell23_5300679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 1, 3, 4].length) (baseStart_5300679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5300679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5300679 prefixEnd_5300679 := by exact prefixLift 5300679
  have htrace : WordTrace (prefixWord ++ tailWord_5300679) baseStart_5300679 baseEnd_5300679 := by
    simpa [prefixWord, tailWord_5300679, baseEnd_5300679] using wordTrace_append hprefix tailTrace_5300679
  have hstable : (prefixWord ++ tailWord_5300679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5300679).length < 2 ^ (prefixWord ++ tailWord_5300679).sum := by decide
  have hdescent : baseEnd_5300679 < baseStart_5300679 := by decide
  rcases family_descends (prefixWord ++ tailWord_5300679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5300756 : List Nat := [2, 4, 3, 1, 1, 1, 2, 1, 3, 5]
def baseStart_5300756 : Nat := 118140960795 + 5300756 * 2 ^ 59
def prefixEnd_5300756 : Nat := 4983230072969 + 3 ^ 40 * 5300756 * 2
def baseEnd_5300756 : Nat := 907278553401389333824091

theorem tailTrace_5300756 : CollatzResearch.WordTrace tailWord_5300756 prefixEnd_5300756 907278553401389333824091 := by
  unfold tailWord_5300756
  simp only [CollatzResearch.WordTrace]
  refine ⟨96667227192136891947765061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128889636256182522597020081 96667227192136891947765061)
  ·
    refine ⟨18125105098525667240205949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96667227192136891947765061 18125105098525667240205949)
    ·
      refine ⟨6796914411947125215077231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18125105098525667240205949 6796914411947125215077231)
      ·
        refine ⟨10195371617920687822615847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6796914411947125215077231 10195371617920687822615847)
        ·
          refine ⟨15293057426881031733923771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10195371617920687822615847 15293057426881031733923771)
          ·
            refine ⟨22939586140321547600885657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15293057426881031733923771 22939586140321547600885657)
            ·
              refine ⟨17204689605241160700664243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22939586140321547600885657 17204689605241160700664243)
              ·
                refine ⟨25807034407861741050996365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17204689605241160700664243 25807034407861741050996365)
                ·
                  refine ⟨9677637902948152894123637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25807034407861741050996365 9677637902948152894123637)
                  ·
                    refine ⟨907278553401389333824091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9677637902948152894123637 907278553401389333824091)
                    ·
                      rfl

theorem cell23_5300756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_5300756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5300756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5300756 prefixEnd_5300756 := by exact prefixLift 5300756
  have htrace : WordTrace (prefixWord ++ tailWord_5300756) baseStart_5300756 baseEnd_5300756 := by
    simpa [prefixWord, tailWord_5300756, baseEnd_5300756] using wordTrace_append hprefix tailTrace_5300756
  have hstable : (prefixWord ++ tailWord_5300756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5300756).length < 2 ^ (prefixWord ++ tailWord_5300756).sum := by decide
  have hdescent : baseEnd_5300756 < baseStart_5300756 := by decide
  rcases family_descends (prefixWord ++ tailWord_5300756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5300769 : List Nat := [1, 2, 3, 2, 2, 1, 2, 2, 4, 4]
def baseStart_5300769 : Nat := 118140960795 + 5300769 * 2 ^ 59
def prefixEnd_5300769 : Nat := 4983230072969 + 3 ^ 40 * 5300769 * 2
def baseEnd_5300769 : Nat := 907280778484225483536571

theorem tailTrace_5300769 : CollatzResearch.WordTrace tailWord_5300769 prefixEnd_5300769 907280778484225483536571 := by
  unfold tailWord_5300769
  simp only [CollatzResearch.WordTrace]
  refine ⟨193334928533226687115753361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128889952355484458077168907 193334928533226687115753361)
  ·
    refine ⟨145001196399920015336815021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193334928533226687115753361 145001196399920015336815021)
    ·
      refine ⟨54375448649970005751305633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145001196399920015336815021 54375448649970005751305633)
      ·
        refine ⟨40781586487477504313479225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54375448649970005751305633 40781586487477504313479225)
        ·
          refine ⟨30586189865608128235109419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40781586487477504313479225 30586189865608128235109419)
          ·
            refine ⟨45879284798412192352664129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30586189865608128235109419 45879284798412192352664129)
            ·
              refine ⟨34409463598809144264498097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45879284798412192352664129 34409463598809144264498097)
              ·
                refine ⟨25807097699106858198373573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34409463598809144264498097 25807097699106858198373573)
                ·
                  refine ⟨4838830818582535912195045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25807097699106858198373573 4838830818582535912195045)
                  ·
                    refine ⟨907280778484225483536571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4838830818582535912195045 907280778484225483536571)
                    ·
                      rfl

theorem cell23_5300769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 2, 4, 4].length) (baseStart_5300769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5300769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5300769 prefixEnd_5300769 := by exact prefixLift 5300769
  have htrace : WordTrace (prefixWord ++ tailWord_5300769) baseStart_5300769 baseEnd_5300769 := by
    simpa [prefixWord, tailWord_5300769, baseEnd_5300769] using wordTrace_append hprefix tailTrace_5300769
  have hstable : (prefixWord ++ tailWord_5300769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5300769).length < 2 ^ (prefixWord ++ tailWord_5300769).sum := by decide
  have hdescent : baseEnd_5300769 < baseStart_5300769 := by decide
  rcases family_descends (prefixWord ++ tailWord_5300769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5300786 : List Nat := [3, 2, 1, 1, 2, 1, 5, 2, 2, 4]
def baseStart_5300786 : Nat := 118140960795 + 5300786 * 2 ^ 59
def prefixEnd_5300786 : Nat := 4983230072969 + 3 ^ 40 * 5300786 * 2
def baseEnd_5300786 : Nat := 907283688207934294699045

theorem tailTrace_5300786 : CollatzResearch.WordTrace tailWord_5300786 prefixEnd_5300786 907283688207934294699045 := by
  unfold tailWord_5300786
  simp only [CollatzResearch.WordTrace]
  refine ⟨48333887143541274754780553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128890365716110066012748141 48333887143541274754780553)
  ·
    refine ⟨36250415357655956066085415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48333887143541274754780553 36250415357655956066085415)
    ·
      refine ⟨54375623036483934099128123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36250415357655956066085415 54375623036483934099128123)
      ·
        refine ⟨81563434554725901148692185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54375623036483934099128123 81563434554725901148692185)
        ·
          refine ⟨61172575916044425861519139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81563434554725901148692185 61172575916044425861519139)
          ·
            refine ⟨91758863874066638792278709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61172575916044425861519139 91758863874066638792278709)
            ·
              refine ⟨8602393488193747386776129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 91758863874066638792278709 8602393488193747386776129)
              ·
                refine ⟨6451795116145310540082097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8602393488193747386776129 6451795116145310540082097)
                ·
                  refine ⟨4838846337108982905061573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6451795116145310540082097 4838846337108982905061573)
                  ·
                    refine ⟨907283688207934294699045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4838846337108982905061573 907283688207934294699045)
                    ·
                      rfl

theorem cell23_5300786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 2, 2, 4].length) (baseStart_5300786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5300786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5300786 prefixEnd_5300786 := by exact prefixLift 5300786
  have htrace : WordTrace (prefixWord ++ tailWord_5300786) baseStart_5300786 baseEnd_5300786 := by
    simpa [prefixWord, tailWord_5300786, baseEnd_5300786] using wordTrace_append hprefix tailTrace_5300786
  have hstable : (prefixWord ++ tailWord_5300786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5300786).length < 2 ^ (prefixWord ++ tailWord_5300786).sum := by decide
  have hdescent : baseEnd_5300786 < baseStart_5300786 := by decide
  rcases family_descends (prefixWord ++ tailWord_5300786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5300793 : List Nat := [1, 2, 1, 5, 1, 1, 4, 1, 3, 2, 2]
def baseStart_5300793 : Nat := 118140960795 + 5300793 * 2 ^ 59
def prefixEnd_5300793 : Nat := 4983230072969 + 3 ^ 40 * 5300793 * 2
def baseEnd_5300793 : Nat := 2721854658988384356709603

theorem tailTrace_5300793 : CollatzResearch.WordTrace tailWord_5300793 prefixEnd_5300793 2721854658988384356709603 := by
  unfold tailWord_5300793
  simp only [CollatzResearch.WordTrace]
  refine ⟨193335803885139739214627033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128890535923426492809751355 193335803885139739214627033)
  ·
    refine ⟨145001852913854804410970275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193335803885139739214627033 145001852913854804410970275)
    ·
      refine ⟨217502779370782206616455413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145001852913854804410970275 217502779370782206616455413)
      ·
        refine ⟨20390885566010831870292695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 217502779370782206616455413 20390885566010831870292695)
        ·
          refine ⟨30586328349016247805439043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20390885566010831870292695 30586328349016247805439043)
          ·
            refine ⟨45879492523524371708158565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30586328349016247805439043 45879492523524371708158565)
            ·
              refine ⟨8602404848160819695279731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45879492523524371708158565 8602404848160819695279731)
              ·
                refine ⟨12903607272241229542919597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8602404848160819695279731 12903607272241229542919597)
                ·
                  refine ⟨4838852727090461078594849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12903607272241229542919597 4838852727090461078594849)
                  ·
                    refine ⟨3629139545317845808946137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4838852727090461078594849 3629139545317845808946137)
                    ·
                      refine ⟨2721854658988384356709603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3629139545317845808946137 2721854658988384356709603)
                      ·
                        rfl

theorem cell23_5300793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 1, 3, 2, 2].length) (baseStart_5300793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5300793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5300793 prefixEnd_5300793 := by exact prefixLift 5300793
  have htrace : WordTrace (prefixWord ++ tailWord_5300793) baseStart_5300793 baseEnd_5300793 := by
    simpa [prefixWord, tailWord_5300793, baseEnd_5300793] using wordTrace_append hprefix tailTrace_5300793
  have hstable : (prefixWord ++ tailWord_5300793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5300793).length < 2 ^ (prefixWord ++ tailWord_5300793).sum := by decide
  have hdescent : baseEnd_5300793 < baseStart_5300793 := by decide
  rcases family_descends (prefixWord ++ tailWord_5300793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5300813 : List Nat := [1, 6, 1, 1, 2, 1, 1, 4, 1, 2, 3]
def baseStart_5300813 : Nat := 118140960795 + 5300813 * 2 ^ 59
def prefixEnd_5300813 : Nat := 4983230072969 + 3 ^ 40 * 5300813 * 2
def baseEnd_5300813 : Nat := 2721864928601474278459511

theorem tailTrace_5300813 : CollatzResearch.WordTrace tailWord_5300813 prefixEnd_5300813 2721864928601474278459511 := by
  unfold tailWord_5300813
  simp only [CollatzResearch.WordTrace]
  refine ⟨193336533345067282630355093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128891022230044855086903395 193336533345067282630355093)
  ·
    refine ⟨9062650000550028873297895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 193336533345067282630355093 9062650000550028873297895)
    ·
      refine ⟨13593975000825043309946843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9062650000550028873297895 13593975000825043309946843)
      ·
        refine ⟨20390962501237564964920265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13593975000825043309946843 20390962501237564964920265)
        ·
          refine ⟨15293221875928173723690199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20390962501237564964920265 15293221875928173723690199)
          ·
            refine ⟨22939832813892260585535299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15293221875928173723690199 22939832813892260585535299)
            ·
              refine ⟨34409749220838390878302949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22939832813892260585535299 34409749220838390878302949)
              ·
                refine ⟨6451827978907198289681803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34409749220838390878302949 6451827978907198289681803)
                ·
                  refine ⟨9677741968360797434522705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6451827978907198289681803 9677741968360797434522705)
                  ·
                    refine ⟨7258306476270598075892029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9677741968360797434522705 7258306476270598075892029)
                    ·
                      refine ⟨2721864928601474278459511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7258306476270598075892029 2721864928601474278459511)
                      ·
                        rfl

theorem cell23_5300813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 4, 1, 2, 3].length) (baseStart_5300813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5300813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5300813 prefixEnd_5300813 := by exact prefixLift 5300813
  have htrace : WordTrace (prefixWord ++ tailWord_5300813) baseStart_5300813 baseEnd_5300813 := by
    simpa [prefixWord, tailWord_5300813, baseEnd_5300813] using wordTrace_append hprefix tailTrace_5300813
  have hstable : (prefixWord ++ tailWord_5300813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5300813).length < 2 ^ (prefixWord ++ tailWord_5300813).sum := by decide
  have hdescent : baseEnd_5300813 < baseStart_5300813 := by decide
  rcases family_descends (prefixWord ++ tailWord_5300813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5300869 : List Nat := [1, 3, 1, 1, 4, 2, 1, 2, 2, 1, 5]
def baseStart_5300869 : Nat := 118140960795 + 5300869 * 2 ^ 59
def prefixEnd_5300869 : Nat := 4983230072969 + 3 ^ 40 * 5300869 * 2
def baseEnd_5300869 : Nat := 2721893683518126059359253

theorem tailTrace_5300869 : CollatzResearch.WordTrace tailWord_5300869 prefixEnd_5300869 2721893683518126059359253 := by
  unfold tailWord_5300869
  simp only [CollatzResearch.WordTrace]
  refine ⟨193338575832864404194393661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128892383888576269462929107 193338575832864404194393661)
  ·
    refine ⟨72501965937324151572897623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 193338575832864404194393661 72501965937324151572897623)
    ·
      refine ⟨108752948905986227359346435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72501965937324151572897623 108752948905986227359346435)
      ·
        refine ⟨163129423358979341039019653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108752948905986227359346435 163129423358979341039019653)
        ·
          refine ⟨30586766879808626444816185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 163129423358979341039019653 30586766879808626444816185)
          ·
            refine ⟨22940075159856469833612139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30586766879808626444816185 22940075159856469833612139)
            ·
              refine ⟨34410112739784704750418209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22940075159856469833612139 34410112739784704750418209)
              ·
                refine ⟨25807584554838528562813657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34410112739784704750418209 25807584554838528562813657)
                ·
                  refine ⟨19355688416128896422110243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25807584554838528562813657 19355688416128896422110243)
                  ·
                    refine ⟨29033532624193344633165365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19355688416128896422110243 29033532624193344633165365)
                    ·
                      refine ⟨2721893683518126059359253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29033532624193344633165365 2721893683518126059359253)
                      ·
                        rfl

theorem cell23_5300869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 2, 2, 1, 5].length) (baseStart_5300869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5300869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5300869 prefixEnd_5300869 := by exact prefixLift 5300869
  have htrace : WordTrace (prefixWord ++ tailWord_5300869) baseStart_5300869 baseEnd_5300869 := by
    simpa [prefixWord, tailWord_5300869, baseEnd_5300869] using wordTrace_append hprefix tailTrace_5300869
  have hstable : (prefixWord ++ tailWord_5300869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5300869).length < 2 ^ (prefixWord ++ tailWord_5300869).sum := by decide
  have hdescent : baseEnd_5300869 < baseStart_5300869 := by decide
  rcases family_descends (prefixWord ++ tailWord_5300869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5300900 : List Nat := [2, 3, 1, 2, 2, 1, 4, 2, 2, 2, 2]
def baseStart_5300900 : Nat := 118140960795 + 5300900 * 2 ^ 59
def prefixEnd_5300900 : Nat := 4983230072969 + 3 ^ 40 * 5300900 * 2
def baseEnd_5300900 : Nat := 2721909601418415438071611

theorem tailTrace_5300900 : CollatzResearch.WordTrace tailWord_5300900 prefixEnd_5300900 2721909601418415438071611 := by
  unfold tailWord_5300900
  simp only [CollatzResearch.WordTrace]
  refine ⟨96669853247876048244386077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128893137663834730992514769 96669853247876048244386077)
  ·
    refine ⟨36251194967953518091644779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96669853247876048244386077 36251194967953518091644779)
    ·
      refine ⟨54376792451930277137467169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36251194967953518091644779 54376792451930277137467169)
      ·
        refine ⟨40782594338947707853100377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54376792451930277137467169 40782594338947707853100377)
        ·
          refine ⟨30586945754210780889825283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40782594338947707853100377 30586945754210780889825283)
          ·
            refine ⟨45880418631316171334737925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30586945754210780889825283 45880418631316171334737925)
            ·
              refine ⟨8602578493371782125263361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45880418631316171334737925 8602578493371782125263361)
              ·
                refine ⟨6451933870028836593947521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8602578493371782125263361 6451933870028836593947521)
                ·
                  refine ⟨4838950402521627445460641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6451933870028836593947521 4838950402521627445460641)
                  ·
                    refine ⟨3629212801891220584095481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4838950402521627445460641 3629212801891220584095481)
                    ·
                      refine ⟨2721909601418415438071611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3629212801891220584095481 2721909601418415438071611)
                      ·
                        rfl

theorem cell23_5300900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 2, 2, 2, 2].length) (baseStart_5300900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5300900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5300900 prefixEnd_5300900 := by exact prefixLift 5300900
  have htrace : WordTrace (prefixWord ++ tailWord_5300900) baseStart_5300900 baseEnd_5300900 := by
    simpa [prefixWord, tailWord_5300900, baseEnd_5300900] using wordTrace_append hprefix tailTrace_5300900
  have hstable : (prefixWord ++ tailWord_5300900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5300900).length < 2 ^ (prefixWord ++ tailWord_5300900).sum := by decide
  have hdescent : baseEnd_5300900 < baseStart_5300900 := by decide
  rcases family_descends (prefixWord ++ tailWord_5300900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5300913 : List Nat := [1, 2, 2, 6, 1, 1, 1, 1, 2, 2, 4]
def baseStart_5300913 : Nat := 118140960795 + 5300913 * 2 ^ 59
def prefixEnd_5300913 : Nat := 4983230072969 + 3 ^ 40 * 5300913 * 2
def baseEnd_5300913 : Nat := 2721916276666923887209051

theorem tailTrace_5300913 : CollatzResearch.WordTrace tailWord_5300913 prefixEnd_5300913 2721916276666923887209051 := by
  unfold tailWord_5300913
  simp only [CollatzResearch.WordTrace]
  refine ⟨193340180644704999708995393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128893453763136666472663595 193340180644704999708995393)
  ·
    refine ⟨145005135483528749781746545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193340180644704999708995393 145005135483528749781746545)
    ·
      refine ⟨108753851612646562336309909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145005135483528749781746545 108753851612646562336309909)
      ·
        refine ⟨5097836794342807609514527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 108753851612646562336309909 5097836794342807609514527)
        ·
          refine ⟨7646755191514211414271791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5097836794342807609514527 7646755191514211414271791)
          ·
            refine ⟨11470132787271317121407687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7646755191514211414271791 11470132787271317121407687)
            ·
              refine ⟨17205199180906975682111531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11470132787271317121407687 17205199180906975682111531)
              ·
                refine ⟨25807798771360463523167297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17205199180906975682111531 25807798771360463523167297)
                ·
                  refine ⟨19355849078520347642375473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25807798771360463523167297 19355849078520347642375473)
                  ·
                    refine ⟨14516886808890260731781605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19355849078520347642375473 14516886808890260731781605)
                    ·
                      refine ⟨2721916276666923887209051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14516886808890260731781605 2721916276666923887209051)
                      ·
                        rfl

theorem cell23_5300913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_5300913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5300913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5300913 prefixEnd_5300913 := by exact prefixLift 5300913
  have htrace : WordTrace (prefixWord ++ tailWord_5300913) baseStart_5300913 baseEnd_5300913 := by
    simpa [prefixWord, tailWord_5300913, baseEnd_5300913] using wordTrace_append hprefix tailTrace_5300913
  have hstable : (prefixWord ++ tailWord_5300913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5300913).length < 2 ^ (prefixWord ++ tailWord_5300913).sum := by decide
  have hdescent : baseEnd_5300913 < baseStart_5300913 := by decide
  rcases family_descends (prefixWord ++ tailWord_5300913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5300936 : List Nat := [2, 1, 3, 1, 2, 3, 3, 1, 2, 5]
def baseStart_5300936 : Nat := 118140960795 + 5300936 * 2 ^ 59
def prefixEnd_5300936 : Nat := 4983230072969 + 3 ^ 40 * 5300936 * 2
def baseEnd_5300936 : Nat := 907309362240659099073815

theorem tailTrace_5300936 : CollatzResearch.WordTrace tailWord_5300936 prefixEnd_5300936 907309362240659099073815 := by
  unfold tailWord_5300936
  simp only [CollatzResearch.WordTrace]
  refine ⟨96670509761810837318541331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128894013015747783091388441 96670509761810837318541331)
  ·
    refine ⟨145005764642716255977811997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96670509761810837318541331 145005764642716255977811997)
    ·
      refine ⟨54377161741018595991679499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145005764642716255977811997 54377161741018595991679499)
      ·
        refine ⟨81565742611527893987519249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54377161741018595991679499 81565742611527893987519249)
        ·
          refine ⟨61174306958645920490639437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81565742611527893987519249 61174306958645920490639437)
          ·
            refine ⟨22940365109492220183989789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61174306958645920490639437 22940365109492220183989789)
            ·
              refine ⟨8602636916059582568996171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22940365109492220183989789 8602636916059582568996171)
              ·
                refine ⟨12903955374089373853494257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8602636916059582568996171 12903955374089373853494257)
                ·
                  refine ⟨9677966530567030390120693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12903955374089373853494257 9677966530567030390120693)
                  ·
                    refine ⟨907309362240659099073815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9677966530567030390120693 907309362240659099073815)
                    ·
                      rfl

theorem cell23_5300936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 1, 2, 5].length) (baseStart_5300936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5300936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5300936 prefixEnd_5300936 := by exact prefixLift 5300936
  have htrace : WordTrace (prefixWord ++ tailWord_5300936) baseStart_5300936 baseEnd_5300936 := by
    simpa [prefixWord, tailWord_5300936, baseEnd_5300936] using wordTrace_append hprefix tailTrace_5300936
  have hstable : (prefixWord ++ tailWord_5300936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5300936).length < 2 ^ (prefixWord ++ tailWord_5300936).sum := by decide
  have hdescent : baseEnd_5300936 < baseStart_5300936 := by decide
  rcases family_descends (prefixWord ++ tailWord_5300936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5300973 : List Nat := [1, 5, 1, 2, 1, 1, 1, 3, 2, 4, 2]
def baseStart_5300973 : Nat := 118140960795 + 5300973 * 2 ^ 59
def prefixEnd_5300973 : Nat := 4983230072969 + 3 ^ 40 * 5300973 * 2
def baseEnd_5300973 : Nat := 2721947085506193652458775

theorem tailTrace_5300973 : CollatzResearch.WordTrace tailWord_5300973 prefixEnd_5300973 2721947085506193652458775 := by
  unfold tailWord_5300973
  simp only [CollatzResearch.WordTrace]
  refine ⟨193342369024487629956179573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128894912682991753304119715 193342369024487629956179573)
  ·
    refine ⟨18125847096045715308391835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 193342369024487629956179573 18125847096045715308391835)
    ·
      refine ⟨27188770644068572962587753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18125847096045715308391835 27188770644068572962587753)
      ·
        refine ⟨20391577983051429721940815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27188770644068572962587753 20391577983051429721940815)
        ·
          refine ⟨30587366974577144582911223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20391577983051429721940815 30587366974577144582911223)
          ·
            refine ⟨45881050461865716874366835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30587366974577144582911223 45881050461865716874366835)
            ·
              refine ⟨68821575692798575311550253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45881050461865716874366835 68821575692798575311550253)
              ·
                refine ⟨25808090884799465741831345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68821575692798575311550253 25808090884799465741831345)
                ·
                  refine ⟨19356068163599599306373509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25808090884799465741831345 19356068163599599306373509)
                  ·
                    refine ⟨3629262780674924869945033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19356068163599599306373509 3629262780674924869945033)
                    ·
                      refine ⟨2721947085506193652458775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3629262780674924869945033 2721947085506193652458775)
                      ·
                        rfl

theorem cell23_5300973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 3, 2, 4, 2].length) (baseStart_5300973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5300973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5300973 prefixEnd_5300973 := by exact prefixLift 5300973
  have htrace : WordTrace (prefixWord ++ tailWord_5300973) baseStart_5300973 baseEnd_5300973 := by
    simpa [prefixWord, tailWord_5300973, baseEnd_5300973] using wordTrace_append hprefix tailTrace_5300973
  have hstable : (prefixWord ++ tailWord_5300973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5300973).length < 2 ^ (prefixWord ++ tailWord_5300973).sum := by decide
  have hdescent : baseEnd_5300973 < baseStart_5300973 := by decide
  rcases family_descends (prefixWord ++ tailWord_5300973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5301000 : List Nat := [2, 1, 3, 2, 2, 2, 3, 3, 1, 4]
def baseStart_5301000 : Nat := 118140960795 + 5301000 * 2 ^ 59
def prefixEnd_5301000 : Nat := 4983230072969 + 3 ^ 40 * 5301000 * 2
def baseEnd_5301000 : Nat := 907320316494621682273717

theorem tailTrace_5301000 : CollatzResearch.WordTrace tailWord_5301000 prefixEnd_5301000 907320316494621682273717 := by
  unfold tailWord_5301000
  simp only [CollatzResearch.WordTrace]
  refine ⟨96671676897694906783706227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128895569196926542378274969 96671676897694906783706227)
  ·
    refine ⟨145007515346542360175559341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96671676897694906783706227 145007515346542360175559341)
    ·
      refine ⟨54377818254953385065834753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145007515346542360175559341 54377818254953385065834753)
      ·
        refine ⟨40783363691215038799376065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54377818254953385065834753 40783363691215038799376065)
        ·
          refine ⟨30587522768411279099532049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40783363691215038799376065 30587522768411279099532049)
          ·
            refine ⟨22940642076308459324649037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30587522768411279099532049 22940642076308459324649037)
            ·
              refine ⟨8602740778615672246743389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22940642076308459324649037 8602740778615672246743389)
              ·
                refine ⟨3226027791980877092528771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8602740778615672246743389 3226027791980877092528771)
                ·
                  refine ⟨4839041687971315638793157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3226027791980877092528771 4839041687971315638793157)
                  ·
                    refine ⟨907320316494621682273717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4839041687971315638793157 907320316494621682273717)
                    ·
                      rfl

theorem cell23_5301000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 3, 1, 4].length) (baseStart_5301000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5301000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5301000 prefixEnd_5301000 := by exact prefixLift 5301000
  have htrace : WordTrace (prefixWord ++ tailWord_5301000) baseStart_5301000 baseEnd_5301000 := by
    simpa [prefixWord, tailWord_5301000, baseEnd_5301000] using wordTrace_append hprefix tailTrace_5301000
  have hstable : (prefixWord ++ tailWord_5301000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5301000).length < 2 ^ (prefixWord ++ tailWord_5301000).sum := by decide
  have hdescent : baseEnd_5301000 < baseStart_5301000 := by decide
  rcases family_descends (prefixWord ++ tailWord_5301000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5301043 : List Nat := [1, 1, 1, 2, 6, 1, 3, 2, 1, 5]
def baseStart_5301043 : Nat := 118140960795 + 5301043 * 2 ^ 59
def prefixEnd_5301043 : Nat := 4983230072969 + 3 ^ 40 * 5301043 * 2
def baseEnd_5301043 : Nat := 907327676384002792861151

theorem tailTrace_5301043 : CollatzResearch.WordTrace tailWord_5301043 prefixEnd_5301043 907327676384002792861151 := by
  unfold tailWord_5301043
  simp only [CollatzResearch.WordTrace]
  refine ⟨193344922134234031911227783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128896614756156021274151855 193344922134234031911227783)
  ·
    refine ⟨290017383201351047866841675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193344922134234031911227783 290017383201351047866841675)
    ·
      refine ⟨435026074802026571800262513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290017383201351047866841675 435026074802026571800262513)
      ·
        refine ⟨326269556101519928850196885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 435026074802026571800262513 326269556101519928850196885)
        ·
          refine ⟨15293885442258746664852979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 326269556101519928850196885 15293885442258746664852979)
          ·
            refine ⟨22940828163388119997279469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15293885442258746664852979 22940828163388119997279469)
            ·
              refine ⟨8602810561270544998979801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22940828163388119997279469 8602810561270544998979801)
              ·
                refine ⟨6452107920952908749234851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8602810561270544998979801 6452107920952908749234851)
                ·
                  refine ⟨9678161881429363123852277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6452107920952908749234851 9678161881429363123852277)
                  ·
                    refine ⟨907327676384002792861151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9678161881429363123852277 907327676384002792861151)
                    ·
                      rfl

theorem cell23_5301043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 2, 1, 5].length) (baseStart_5301043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5301043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5301043 prefixEnd_5301043 := by exact prefixLift 5301043
  have htrace : WordTrace (prefixWord ++ tailWord_5301043) baseStart_5301043 baseEnd_5301043 := by
    simpa [prefixWord, tailWord_5301043, baseEnd_5301043] using wordTrace_append hprefix tailTrace_5301043
  have hstable : (prefixWord ++ tailWord_5301043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5301043).length < 2 ^ (prefixWord ++ tailWord_5301043).sum := by decide
  have hdescent : baseEnd_5301043 < baseStart_5301043 := by decide
  rcases family_descends (prefixWord ++ tailWord_5301043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5301056 : List Nat := [2, 1, 1, 2, 2, 1, 1, 3, 6, 4]
def baseStart_5301056 : Nat := 118140960795 + 5301056 * 2 ^ 59
def prefixEnd_5301056 : Nat := 4983230072969 + 3 ^ 40 * 5301056 * 2
def baseEnd_5301056 : Nat := 907329901466838942573631

theorem tailTrace_5301056 : CollatzResearch.WordTrace tailWord_5301056 prefixEnd_5301056 907329901466838942573631 := by
  unfold tailWord_5301056
  simp only [CollatzResearch.WordTrace]
  refine ⟨96672698141593467565725511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128896930855457956754300681 96672698141593467565725511)
  ·
    refine ⟨145009047212390201348588267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96672698141593467565725511 145009047212390201348588267)
    ·
      refine ⟨217513570818585302022882401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145009047212390201348588267 217513570818585302022882401)
      ·
        refine ⟨163135178113938976517161801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 217513570818585302022882401 163135178113938976517161801)
        ·
          refine ⟨122351383585454232387871351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163135178113938976517161801 122351383585454232387871351)
          ·
            refine ⟨183527075378181348581807027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122351383585454232387871351 183527075378181348581807027)
            ·
              refine ⟨275290613067272022872710541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 183527075378181348581807027 275290613067272022872710541)
              ·
                refine ⟨103233979900227008577266453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 275290613067272022872710541 103233979900227008577266453)
                ·
                  refine ⟨4839092807823141027059365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 103233979900227008577266453 4839092807823141027059365)
                  ·
                    refine ⟨907329901466838942573631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4839092807823141027059365 907329901466838942573631)
                    ·
                      rfl

theorem cell23_5301056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 6, 4].length) (baseStart_5301056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5301056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5301056 prefixEnd_5301056 := by exact prefixLift 5301056
  have htrace : WordTrace (prefixWord ++ tailWord_5301056) baseStart_5301056 baseEnd_5301056 := by
    simpa [prefixWord, tailWord_5301056, baseEnd_5301056] using wordTrace_append hprefix tailTrace_5301056
  have hstable : (prefixWord ++ tailWord_5301056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5301056).length < 2 ^ (prefixWord ++ tailWord_5301056).sum := by decide
  have hdescent : baseEnd_5301056 < baseStart_5301056 := by decide
  rcases family_descends (prefixWord ++ tailWord_5301056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5301066 : List Nat := [3, 1, 2, 1, 1, 1, 2, 5, 1, 1, 5]
def baseStart_5301066 : Nat := 118140960795 + 5301066 * 2 ^ 59
def prefixEnd_5301066 : Nat := 4983230072969 + 3 ^ 40 * 5301066 * 2
def baseEnd_5301066 : Nat := 2721994839207061788595847

theorem tailTrace_5301066 : CollatzResearch.WordTrace tailWord_5301066 prefixEnd_5301066 2721994839207061788595847 := by
  unfold tailWord_5301066
  simp only [CollatzResearch.WordTrace]
  refine ⟨48336440253287676709828763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128897174008767137892876701 48336440253287676709828763)
  ·
    refine ⟨72504660379931515064743145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48336440253287676709828763 72504660379931515064743145)
    ·
      refine ⟨54378495284948636298557359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72504660379931515064743145 54378495284948636298557359)
      ·
        refine ⟨81567742927422954447836039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54378495284948636298557359 81567742927422954447836039)
        ·
          refine ⟨122351614391134431671754059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81567742927422954447836039 122351614391134431671754059)
          ·
            refine ⟨183527421586701647507631089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122351614391134431671754059 183527421586701647507631089)
            ·
              refine ⟨137645566190026235630723317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 183527421586701647507631089 137645566190026235630723317)
              ·
                refine ⟨12904271830314959590380311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 137645566190026235630723317 12904271830314959590380311)
                ·
                  refine ⟨19356407745472439385570467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12904271830314959590380311 19356407745472439385570467)
                  ·
                    refine ⟨29034611618208659078355701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19356407745472439385570467 29034611618208659078355701)
                    ·
                      refine ⟨2721994839207061788595847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29034611618208659078355701 2721994839207061788595847)
                      ·
                        rfl

theorem cell23_5301066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 5, 1, 1, 5].length) (baseStart_5301066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5301066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5301066 prefixEnd_5301066 := by exact prefixLift 5301066
  have htrace : WordTrace (prefixWord ++ tailWord_5301066) baseStart_5301066 baseEnd_5301066 := by
    simpa [prefixWord, tailWord_5301066, baseEnd_5301066] using wordTrace_append hprefix tailTrace_5301066
  have hstable : (prefixWord ++ tailWord_5301066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5301066).length < 2 ^ (prefixWord ++ tailWord_5301066).sum := by decide
  have hdescent : baseEnd_5301066 < baseStart_5301066 := by decide
  rcases family_descends (prefixWord ++ tailWord_5301066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5301090 : List Nat := [3, 3, 2, 1, 3, 1, 2, 1, 1, 6]
def baseStart_5301090 : Nat := 118140960795 + 5301090 * 2 ^ 59
def prefixEnd_5301090 : Nat := 4983230072969 + 3 ^ 40 * 5301090 * 2
def baseEnd_5301090 : Nat := 907335720914256564898579

theorem tailTrace_5301090 : CollatzResearch.WordTrace tailWord_5301090 prefixEnd_5301090 907335720914256564898579 := by
  unfold tailWord_5301090
  simp only [CollatzResearch.WordTrace]
  refine ⟨48336659091265939734547181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128897757576709172625459149 48336659091265939734547181)
  ·
    refine ⟨18126247159224727400455193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48336659091265939734547181 18126247159224727400455193)
    ·
      refine ⟨13594685369418545550341395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18126247159224727400455193 13594685369418545550341395)
      ·
        refine ⟨20392028054127818325512093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13594685369418545550341395 20392028054127818325512093)
        ·
          refine ⟨7647010520297931872067035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20392028054127818325512093 7647010520297931872067035)
          ·
            refine ⟨11470515780446897808100553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7647010520297931872067035 11470515780446897808100553)
            ·
              refine ⟨8602886835335173356075415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11470515780446897808100553 8602886835335173356075415)
              ·
                refine ⟨12904330253002760034113123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8602886835335173356075415 12904330253002760034113123)
                ·
                  refine ⟨19356495379504140051169685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12904330253002760034113123 19356495379504140051169685)
                  ·
                    refine ⟨907335720914256564898579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19356495379504140051169685 907335720914256564898579)
                    ·
                      rfl

theorem cell23_5301090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_5301090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5301090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5301090 prefixEnd_5301090 := by exact prefixLift 5301090
  have htrace : WordTrace (prefixWord ++ tailWord_5301090) baseStart_5301090 baseEnd_5301090 := by
    simpa [prefixWord, tailWord_5301090, baseEnd_5301090] using wordTrace_append hprefix tailTrace_5301090
  have hstable : (prefixWord ++ tailWord_5301090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5301090).length < 2 ^ (prefixWord ++ tailWord_5301090).sum := by decide
  have hdescent : baseEnd_5301090 < baseStart_5301090 := by decide
  rcases family_descends (prefixWord ++ tailWord_5301090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5301110 : List Nat := [5, 1, 1, 3, 1, 1, 2, 2, 1, 2, 4]
def baseStart_5301110 : Nat := 118140960795 + 5301110 * 2 ^ 59
def prefixEnd_5301110 : Nat := 4983230072969 + 3 ^ 40 * 5301110 * 2
def baseEnd_5301110 : Nat := 2722017432355859616445645

theorem tailTrace_5301110 : CollatzResearch.WordTrace tailWord_5301110 prefixEnd_5301110 2722017432355859616445645 := by
  unfold tailWord_5301110
  simp only [CollatzResearch.WordTrace]
  refine ⟨12084210364061956397119799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 128898243883327534902611189 12084210364061956397119799)
  ·
    refine ⟨18126315546092934595679699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12084210364061956397119799 18126315546092934595679699)
    ·
      refine ⟨27189473319139401893519549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18126315546092934595679699 27189473319139401893519549)
      ·
        refine ⟨10196052494677275710069831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27189473319139401893519549 10196052494677275710069831)
        ·
          refine ⟨15294078742015913565104747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10196052494677275710069831 15294078742015913565104747)
          ·
            refine ⟨22941118113023870347657121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15294078742015913565104747 22941118113023870347657121)
            ·
              refine ⟨17205838584767902760742841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22941118113023870347657121 17205838584767902760742841)
              ·
                refine ⟨12904378938575927070557131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17205838584767902760742841 12904378938575927070557131)
                ·
                  refine ⟨19356568407863890605835697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12904378938575927070557131 19356568407863890605835697)
                  ·
                    refine ⟨14517426305897917954376773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19356568407863890605835697 14517426305897917954376773)
                    ·
                      refine ⟨2722017432355859616445645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14517426305897917954376773 2722017432355859616445645)
                      ·
                        rfl

theorem cell23_5301110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_5301110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5301110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5301110 prefixEnd_5301110 := by exact prefixLift 5301110
  have htrace : WordTrace (prefixWord ++ tailWord_5301110) baseStart_5301110 baseEnd_5301110 := by
    simpa [prefixWord, tailWord_5301110, baseEnd_5301110] using wordTrace_append hprefix tailTrace_5301110
  have hstable : (prefixWord ++ tailWord_5301110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5301110).length < 2 ^ (prefixWord ++ tailWord_5301110).sum := by decide
  have hdescent : baseEnd_5301110 < baseStart_5301110 := by decide
  rcases family_descends (prefixWord ++ tailWord_5301110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5301113 : List Nat := [1, 2, 1, 3, 2, 3, 2, 2, 1, 3, 3]
def baseStart_5301113 : Nat := 118140960795 + 5301113 * 2 ^ 59
def prefixEnd_5301113 : Nat := 4983230072969 + 3 ^ 40 * 5301113 * 2
def baseEnd_5301113 : Nat := 2722018972797823104708131

theorem tailTrace_5301113 : CollatzResearch.WordTrace tailWord_5301113 prefixEnd_5301113 2722018972797823104708131 := by
  unfold tailWord_5301113
  simp only [CollatzResearch.WordTrace]
  refine ⟨193347475243980433866275993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128898316829320289244183995 193347475243980433866275993)
  ·
    refine ⟨145010606432985325399706995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193347475243980433866275993 145010606432985325399706995)
    ·
      refine ⟨217515909649477988099560493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145010606432985325399706995 217515909649477988099560493)
      ·
        refine ⟨81568466118554245537335185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 217515909649477988099560493 81568466118554245537335185)
        ·
          refine ⟨61176349588915684153001389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81568466118554245537335185 61176349588915684153001389)
          ·
            refine ⟨22941131095843381557375521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61176349588915684153001389 22941131095843381557375521)
            ·
              refine ⟨17205848321882536168031641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22941131095843381557375521 17205848321882536168031641)
              ·
                refine ⟨12904386241411902126023731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17205848321882536168031641 12904386241411902126023731)
                ·
                  refine ⟨19356579362117853189035597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12904386241411902126023731 19356579362117853189035597)
                  ·
                    refine ⟨7258717260794194945888349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19356579362117853189035597 7258717260794194945888349)
                    ·
                      refine ⟨2722018972797823104708131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7258717260794194945888349 2722018972797823104708131)
                      ·
                        rfl

theorem cell23_5301113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 2, 1, 3, 3].length) (baseStart_5301113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5301113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5301113 prefixEnd_5301113 := by exact prefixLift 5301113
  have htrace : WordTrace (prefixWord ++ tailWord_5301113) baseStart_5301113 baseEnd_5301113 := by
    simpa [prefixWord, tailWord_5301113, baseEnd_5301113] using wordTrace_append hprefix tailTrace_5301113
  have hstable : (prefixWord ++ tailWord_5301113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5301113).length < 2 ^ (prefixWord ++ tailWord_5301113).sum := by decide
  have hdescent : baseEnd_5301113 < baseStart_5301113 := by decide
  rcases family_descends (prefixWord ++ tailWord_5301113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5301165 : List Nat := [1, 5, 2, 3, 2, 1, 1, 3, 1, 2, 2]
def baseStart_5301165 : Nat := 118140960795 + 5301165 * 2 ^ 59
def prefixEnd_5301165 : Nat := 4983230072969 + 3 ^ 40 * 5301165 * 2
def baseEnd_5301165 : Nat := 2722045673791856901257893

theorem tailTrace_5301165 : CollatzResearch.WordTrace tailWord_5301165 prefixEnd_5301165 2722045673791856901257893 := by
  unfold tailWord_5301165
  simp only [CollatzResearch.WordTrace]
  refine ⟨193349371839792046747168949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128899581226528031164779299 193349371839792046747168949)
  ·
    refine ⟨18126503609980504382547089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 193349371839792046747168949 18126503609980504382547089)
    ·
      refine ⟨13594877707485378286910317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18126503609980504382547089 13594877707485378286910317)
      ·
        refine ⟨5098079140307016857591369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13594877707485378286910317 5098079140307016857591369)
        ·
          refine ⟨3823559355230262643193527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5098079140307016857591369 3823559355230262643193527)
          ·
            refine ⟨5735339032845393964790291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3823559355230262643193527 5735339032845393964790291)
            ·
              refine ⟨8603008549268090947185437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5735339032845393964790291 8603008549268090947185437)
              ·
                refine ⟨3226128205975534105194539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8603008549268090947185437 3226128205975534105194539)
                ·
                  refine ⟨4839192308963301157791809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3226128205975534105194539 4839192308963301157791809)
                  ·
                    refine ⟨3629394231722475868343857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4839192308963301157791809 3629394231722475868343857)
                    ·
                      refine ⟨2722045673791856901257893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3629394231722475868343857 2722045673791856901257893)
                      ·
                        rfl

theorem cell23_5301165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_5301165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5301165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5301165 prefixEnd_5301165 := by exact prefixLift 5301165
  have htrace : WordTrace (prefixWord ++ tailWord_5301165) baseStart_5301165 baseEnd_5301165 := by
    simpa [prefixWord, tailWord_5301165, baseEnd_5301165] using wordTrace_append hprefix tailTrace_5301165
  have hstable : (prefixWord ++ tailWord_5301165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5301165).length < 2 ^ (prefixWord ++ tailWord_5301165).sum := by decide
  have hdescent : baseEnd_5301165 < baseStart_5301165 := by decide
  rcases family_descends (prefixWord ++ tailWord_5301165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5301173 : List Nat := [1, 3, 3, 2, 1, 1, 3, 1, 2, 1, 5]
def baseStart_5301173 : Nat := 118140960795 + 5301173 * 2 ^ 59
def prefixEnd_5301173 : Nat := 4983230072969 + 3 ^ 40 * 5301173 * 2
def baseEnd_5301173 : Nat := 2722049781637092869957855

theorem tailTrace_5301173 : CollatzResearch.WordTrace tailWord_5301173 prefixEnd_5301173 2722049781637092869957855 := by
  unfold tailWord_5301173
  simp only [CollatzResearch.WordTrace]
  refine ⟨193349663623763064113460173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128899775749175376075640115 193349663623763064113460173)
  ·
    refine ⟨72506123858911149042547565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 193349663623763064113460173 72506123858911149042547565)
    ·
      refine ⟨27189796447091680890955337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72506123858911149042547565 27189796447091680890955337)
      ·
        refine ⟨20392347335318760668216503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27189796447091680890955337 20392347335318760668216503)
        ·
          refine ⟨30588521002978141002324755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20392347335318760668216503 30588521002978141002324755)
          ·
            refine ⟨45882781504467211503487133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30588521002978141002324755 45882781504467211503487133)
            ·
              refine ⟨17206043064175204313807675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45882781504467211503487133 17206043064175204313807675)
              ·
                refine ⟨25809064596262806470711513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17206043064175204313807675 25809064596262806470711513)
                ·
                  refine ⟨19356798447197104853033635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25809064596262806470711513 19356798447197104853033635)
                  ·
                    refine ⟨29035197670795657279550453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19356798447197104853033635 29035197670795657279550453)
                    ·
                      refine ⟨2722049781637092869957855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29035197670795657279550453 2722049781637092869957855)
                      ·
                        rfl

theorem cell23_5301173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_5301173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5301173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5301173 prefixEnd_5301173 := by exact prefixLift 5301173
  have htrace : WordTrace (prefixWord ++ tailWord_5301173) baseStart_5301173 baseEnd_5301173 := by
    simpa [prefixWord, tailWord_5301173, baseEnd_5301173] using wordTrace_append hprefix tailTrace_5301173
  have hstable : (prefixWord ++ tailWord_5301173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5301173).length < 2 ^ (prefixWord ++ tailWord_5301173).sum := by decide
  have hdescent : baseEnd_5301173 < baseStart_5301173 := by decide
  rcases family_descends (prefixWord ++ tailWord_5301173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5301204 : List Nat := [2, 4, 1, 2, 1, 3, 1, 3, 2, 2, 2]
def baseStart_5301204 : Nat := 118140960795 + 5301204 * 2 ^ 59
def prefixEnd_5301204 : Nat := 4983230072969 + 3 ^ 40 * 5301204 * 2
def baseEnd_5301204 : Nat := 2722065699537382248670213

theorem tailTrace_5301204 : CollatzResearch.WordTrace tailWord_5301204 prefixEnd_5301204 2722065699537382248670213 := by
  unfold tailWord_5301204
  simp only [CollatzResearch.WordTrace]
  refine ⟨96675397143325378203919333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128900529524433837605225777 96675397143325378203919333)
  ·
    refine ⟨18126636964373508413234875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96675397143325378203919333 18126636964373508413234875)
    ·
      refine ⟨27189955446560262619852313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18126636964373508413234875 27189955446560262619852313)
      ·
        refine ⟨20392466584920196964889235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27189955446560262619852313 20392466584920196964889235)
        ·
          refine ⟨30588699877380295447333853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20392466584920196964889235 30588699877380295447333853)
          ·
            refine ⟨11470762454017610792750195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30588699877380295447333853 11470762454017610792750195)
            ·
              refine ⟨17206143681026416189125293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11470762454017610792750195 17206143681026416189125293)
              ·
                refine ⟨6452303880384906070921985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17206143681026416189125293 6452303880384906070921985)
                ·
                  refine ⟨4839227910288679553191489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6452303880384906070921985 4839227910288679553191489)
                  ·
                    refine ⟨3629420932716509664893617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4839227910288679553191489 3629420932716509664893617)
                    ·
                      refine ⟨2722065699537382248670213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3629420932716509664893617 2722065699537382248670213)
                      ·
                        rfl

theorem cell23_5301204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 3, 2, 2, 2].length) (baseStart_5301204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5301204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5301204 prefixEnd_5301204 := by exact prefixLift 5301204
  have htrace : WordTrace (prefixWord ++ tailWord_5301204) baseStart_5301204 baseEnd_5301204 := by
    simpa [prefixWord, tailWord_5301204, baseEnd_5301204] using wordTrace_append hprefix tailTrace_5301204
  have hstable : (prefixWord ++ tailWord_5301204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5301204).length < 2 ^ (prefixWord ++ tailWord_5301204).sum := by decide
  have hdescent : baseEnd_5301204 < baseStart_5301204 := by decide
  rcases family_descends (prefixWord ++ tailWord_5301204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5301233 : List Nat := [1, 2, 2, 2, 4, 1, 1, 2, 1, 2, 5]
def baseStart_5301233 : Nat := 118140960795 + 5301233 * 2 ^ 59
def prefixEnd_5301233 : Nat := 4983230072969 + 3 ^ 40 * 5301233 * 2
def baseEnd_5301233 : Nat := 2722080590476362635207579

theorem tailTrace_5301233 : CollatzResearch.WordTrace tailWord_5301233 prefixEnd_5301233 2722080590476362635207579 := by
  unfold tailWord_5301233
  simp only [CollatzResearch.WordTrace]
  refine ⟨193351852003545694360644353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128901234669030462907096235 193351852003545694360644353)
  ·
    refine ⟨145013889002659270770483265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193351852003545694360644353 145013889002659270770483265)
    ·
      refine ⟨108760416751994453077862449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145013889002659270770483265 108760416751994453077862449)
      ·
        refine ⟨81570312563995839808396837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108760416751994453077862449 81570312563995839808396837)
        ·
          refine ⟨15294433605749219964074407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81570312563995839808396837 15294433605749219964074407)
          ·
            refine ⟨22941650408623829946111611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15294433605749219964074407 22941650408623829946111611)
            ·
              refine ⟨34412475612935744919167417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22941650408623829946111611 34412475612935744919167417)
              ·
                refine ⟨25809356709701808689375563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34412475612935744919167417 25809356709701808689375563)
                ·
                  refine ⟨38714035064552713034063345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25809356709701808689375563 38714035064552713034063345)
                  ·
                    refine ⟨29035526298414534775547509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38714035064552713034063345 29035526298414534775547509)
                    ·
                      refine ⟨2722080590476362635207579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29035526298414534775547509 2722080590476362635207579)
                      ·
                        rfl

theorem cell23_5301233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 2, 1, 2, 5].length) (baseStart_5301233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5301233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5301233 prefixEnd_5301233 := by exact prefixLift 5301233
  have htrace : WordTrace (prefixWord ++ tailWord_5301233) baseStart_5301233 baseEnd_5301233 := by
    simpa [prefixWord, tailWord_5301233, baseEnd_5301233] using wordTrace_append hprefix tailTrace_5301233
  have hstable : (prefixWord ++ tailWord_5301233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5301233).length < 2 ^ (prefixWord ++ tailWord_5301233).sum := by decide
  have hdescent : baseEnd_5301233 < baseStart_5301233 := by decide
  rcases family_descends (prefixWord ++ tailWord_5301233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5301260 : List Nat := [2, 2, 1, 2, 3, 2, 1, 1, 1, 6, 2]
def baseStart_5301260 : Nat := 118140960795 + 5301260 * 2 ^ 59
def prefixEnd_5301260 : Nat := 4983230072969 + 3 ^ 40 * 5301260 * 2
def baseEnd_5301260 : Nat := 2722094454454034029569955

theorem tailTrace_5301260 : CollatzResearch.WordTrace tailWord_5301260 prefixEnd_5301260 2722094454454034029569955 := by
  unfold tailWord_5301260
  simp only [CollatzResearch.WordTrace]
  refine ⟨96676418387223938985938617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128901891182965251981251489 96676418387223938985938617)
  ·
    refine ⟨72507313790417954239453963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96676418387223938985938617 72507313790417954239453963)
    ·
      refine ⟨108760970685626931359180945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72507313790417954239453963 108760970685626931359180945)
      ·
        refine ⟨81570728014220198519385709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108760970685626931359180945 81570728014220198519385709)
        ·
          refine ⟨30589023005332574444769641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81570728014220198519385709 30589023005332574444769641)
          ·
            refine ⟨22941767253999430833577231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30589023005332574444769641 22941767253999430833577231)
            ·
              refine ⟨34412650880999146250365847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22941767253999430833577231 34412650880999146250365847)
              ·
                refine ⟨51618976321498719375548771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34412650880999146250365847 51618976321498719375548771)
                ·
                  refine ⟨77428464482248079063323157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51618976321498719375548771 77428464482248079063323157)
                  ·
                    refine ⟨3629459272605378706093273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 77428464482248079063323157 3629459272605378706093273)
                    ·
                      refine ⟨2722094454454034029569955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3629459272605378706093273 2722094454454034029569955)
                      ·
                        rfl

theorem cell23_5301260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 1, 6, 2].length) (baseStart_5301260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5301260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5301260 prefixEnd_5301260 := by exact prefixLift 5301260
  have htrace : WordTrace (prefixWord ++ tailWord_5301260) baseStart_5301260 baseEnd_5301260 := by
    simpa [prefixWord, tailWord_5301260, baseEnd_5301260] using wordTrace_append hprefix tailTrace_5301260
  have hstable : (prefixWord ++ tailWord_5301260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5301260).length < 2 ^ (prefixWord ++ tailWord_5301260).sum := by decide
  have hdescent : baseEnd_5301260 < baseStart_5301260 := by decide
  rcases family_descends (prefixWord ++ tailWord_5301260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5301320 : List Nat := [2, 1, 3, 1, 1, 1, 3, 1, 3, 5, 2]
def baseStart_5301320 : Nat := 118140960795 + 5301320 * 2 ^ 59
def prefixEnd_5301320 : Nat := 4983230072969 + 3 ^ 40 * 5301320 * 2
def baseEnd_5301320 : Nat := 2722125263293303794819679

theorem tailTrace_5301320 : CollatzResearch.WordTrace tailWord_5301320 prefixEnd_5301320 2722125263293303794819679 := by
  unfold tailWord_5301320
  simp only [CollatzResearch.WordTrace]
  refine ⟨96677512577115254109530707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128903350102820338812707609 96677512577115254109530707)
  ·
    refine ⟨145016268865672881164296061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96677512577115254109530707 145016268865672881164296061)
    ·
      refine ⟨54381100824627330436611023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145016268865672881164296061 54381100824627330436611023)
      ·
        refine ⟨81571651236940995654916535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54381100824627330436611023 81571651236940995654916535)
        ·
          refine ⟨122357476855411493482374803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81571651236940995654916535 122357476855411493482374803)
          ·
            refine ⟨183536215283117240223562205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122357476855411493482374803 183536215283117240223562205)
            ·
              refine ⟨68826080731168965083835827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 183536215283117240223562205 68826080731168965083835827)
              ·
                refine ⟨103239121096753447625753741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68826080731168965083835827 103239121096753447625753741)
                ·
                  refine ⟨38714670411282542859657653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 103239121096753447625753741 38714670411282542859657653)
                  ·
                    refine ⟨3629500351057738393092905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38714670411282542859657653 3629500351057738393092905)
                    ·
                      refine ⟨2722125263293303794819679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3629500351057738393092905 2722125263293303794819679)
                      ·
                        rfl

theorem cell23_5301320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 3, 5, 2].length) (baseStart_5301320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5301320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5301320 prefixEnd_5301320 := by exact prefixLift 5301320
  have htrace : WordTrace (prefixWord ++ tailWord_5301320) baseStart_5301320 baseEnd_5301320 := by
    simpa [prefixWord, tailWord_5301320, baseEnd_5301320] using wordTrace_append hprefix tailTrace_5301320
  have hstable : (prefixWord ++ tailWord_5301320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5301320).length < 2 ^ (prefixWord ++ tailWord_5301320).sum := by decide
  have hdescent : baseEnd_5301320 < baseStart_5301320 := by decide
  rcases family_descends (prefixWord ++ tailWord_5301320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5301343 : List Nat := [1, 1, 2, 3, 1, 1, 4, 1, 3, 6]
def baseStart_5301343 : Nat := 118140960795 + 5301343 * 2 ^ 59
def prefixEnd_5301343 : Nat := 4983230072969 + 3 ^ 40 * 5301343 * 2
def baseEnd_5301343 : Nat := 907379024449452401610691

theorem tailTrace_5301343 : CollatzResearch.WordTrace tailWord_5301343 prefixEnd_5301343 907379024449452401610691 := by
  unfold tailWord_5301343
  simp only [CollatzResearch.WordTrace]
  refine ⟨193355864033147183147148683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128903909355431455431432455 193355864033147183147148683)
  ·
    refine ⟨290033796049720774720723025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193355864033147183147148683 290033796049720774720723025)
    ·
      refine ⟨217525347037290581040542269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 290033796049720774720723025 217525347037290581040542269)
      ·
        refine ⟨81572005138983967890203351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 217525347037290581040542269 81572005138983967890203351)
        ·
          refine ⟨122358007708475951835305027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81572005138983967890203351 122358007708475951835305027)
          ·
            refine ⟨183537011562713927752957541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122358007708475951835305027 183537011562713927752957541)
            ·
              refine ⟨34413189668008861453679539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 183537011562713927752957541 34413189668008861453679539)
              ·
                refine ⟨51619784502013292180519309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34413189668008861453679539 51619784502013292180519309)
                ·
                  refine ⟨19357419188254984567694741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51619784502013292180519309 19357419188254984567694741)
                  ·
                    refine ⟨907379024449452401610691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19357419188254984567694741 907379024449452401610691)
                    ·
                      rfl

theorem cell23_5301343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 3, 6].length) (baseStart_5301343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5301343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5301343 prefixEnd_5301343 := by exact prefixLift 5301343
  have htrace : WordTrace (prefixWord ++ tailWord_5301343) baseStart_5301343 baseEnd_5301343 := by
    simpa [prefixWord, tailWord_5301343, baseEnd_5301343] using wordTrace_append hprefix tailTrace_5301343
  have hstable : (prefixWord ++ tailWord_5301343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5301343).length < 2 ^ (prefixWord ++ tailWord_5301343).sum := by decide
  have hdescent : baseEnd_5301343 < baseStart_5301343 := by decide
  rcases family_descends (prefixWord ++ tailWord_5301343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5301354 : List Nat := [3, 1, 3, 2, 2, 2, 1, 2, 2, 3, 2]
def baseStart_5301354 : Nat := 118140960795 + 5301354 * 2 ^ 59
def prefixEnd_5301354 : Nat := 4983230072969 + 3 ^ 40 * 5301354 * 2
def baseEnd_5301354 : Nat := 2722142721635556661794523

theorem tailTrace_5301354 : CollatzResearch.WordTrace tailWord_5301354 prefixEnd_5301354 2722142721635556661794523 := by
  unfold tailWord_5301354
  simp only [CollatzResearch.WordTrace]
  refine ⟨48339066309026833006449779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128904176824071554683866077 48339066309026833006449779)
  ·
    refine ⟨72508599463540249509674669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48339066309026833006449779 72508599463540249509674669)
    ·
      refine ⟨27190724798827593566128001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72508599463540249509674669 27190724798827593566128001)
      ·
        refine ⟨20393043599120695174596001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27190724798827593566128001 20393043599120695174596001)
        ·
          refine ⟨15294782699340521380947001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20393043599120695174596001 15294782699340521380947001)
          ·
            refine ⟨11471087024505391035710251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15294782699340521380947001 11471087024505391035710251)
            ·
              refine ⟨17206630536758086553565377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11471087024505391035710251 17206630536758086553565377)
              ·
                refine ⟨12904972902568564915174033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17206630536758086553565377 12904972902568564915174033)
                ·
                  refine ⟨9678729676926423686380525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12904972902568564915174033 9678729676926423686380525)
                  ·
                    refine ⟨3629523628847408882392697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9678729676926423686380525 3629523628847408882392697)
                    ·
                      refine ⟨2722142721635556661794523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3629523628847408882392697 2722142721635556661794523)
                      ·
                        rfl

theorem cell23_5301354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 2, 2, 3, 2].length) (baseStart_5301354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5301354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5301354 prefixEnd_5301354 := by exact prefixLift 5301354
  have htrace : WordTrace (prefixWord ++ tailWord_5301354) baseStart_5301354 baseEnd_5301354 := by
    simpa [prefixWord, tailWord_5301354, baseEnd_5301354] using wordTrace_append hprefix tailTrace_5301354
  have hstable : (prefixWord ++ tailWord_5301354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5301354).length < 2 ^ (prefixWord ++ tailWord_5301354).sum := by decide
  have hdescent : baseEnd_5301354 < baseStart_5301354 := by decide
  rcases family_descends (prefixWord ++ tailWord_5301354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5301360 : List Nat := [2, 1, 1, 1, 5, 1, 1, 3, 4, 4]
def baseStart_5301360 : Nat := 118140960795 + 5301360 * 2 ^ 59
def prefixEnd_5301360 : Nat := 4983230072969 + 3 ^ 40 * 5301360 * 2
def baseEnd_5301360 : Nat := 907381934173161212773165

theorem tailTrace_5301360 : CollatzResearch.WordTrace tailWord_5301360 prefixEnd_5301360 907381934173161212773165 := by
  unfold tailWord_5301360
  simp only [CollatzResearch.WordTrace]
  refine ⟨96678242037042797525258767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128904322716057063367011689 96678242037042797525258767)
  ·
    refine ⟨145017363055564196287888151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96678242037042797525258767 145017363055564196287888151)
    ·
      refine ⟨217526044583346294431832227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145017363055564196287888151 217526044583346294431832227)
      ·
        refine ⟨326289066875019441647748341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217526044583346294431832227 326289066875019441647748341)
        ·
          refine ⟨30589600019533072654476407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 326289066875019441647748341 30589600019533072654476407)
          ·
            refine ⟨45884400029299608981714611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30589600019533072654476407 45884400029299608981714611)
            ·
              refine ⟨68826600043949413472571917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45884400029299608981714611 68826600043949413472571917)
              ·
                refine ⟨25809975016481030052214469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68826600043949413472571917 25809975016481030052214469)
                ·
                  refine ⟨4839370315590193134790213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25809975016481030052214469 4839370315590193134790213)
                  ·
                    refine ⟨907381934173161212773165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4839370315590193134790213 907381934173161212773165)
                    ·
                      rfl

theorem cell23_5301360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 3, 4, 4].length) (baseStart_5301360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5301360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5301360 prefixEnd_5301360 := by exact prefixLift 5301360
  have htrace : WordTrace (prefixWord ++ tailWord_5301360) baseStart_5301360 baseEnd_5301360 := by
    simpa [prefixWord, tailWord_5301360, baseEnd_5301360] using wordTrace_append hprefix tailTrace_5301360
  have hstable : (prefixWord ++ tailWord_5301360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5301360).length < 2 ^ (prefixWord ++ tailWord_5301360).sum := by decide
  have hdescent : baseEnd_5301360 < baseStart_5301360 := by decide
  rcases family_descends (prefixWord ++ tailWord_5301360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5301380 : List Nat := [2, 3, 2, 1, 2, 2, 2, 1, 1, 1, 6]
def baseStart_5301380 : Nat := 118140960795 + 5301380 * 2 ^ 59
def prefixEnd_5301380 : Nat := 4983230072969 + 3 ^ 40 * 5301380 * 2
def baseEnd_5301380 : Nat := 2722156072132573560069403

theorem tailTrace_5301380 : CollatzResearch.WordTrace tailWord_5301380 prefixEnd_5301380 2722156072132573560069403 := by
  unfold tailWord_5301380
  simp only [CollatzResearch.WordTrace]
  refine ⟨96678606767006569233122797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128904809022675425644163729 96678606767006569233122797)
  ·
    refine ⟨36254477537627463462421049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96678606767006569233122797 36254477537627463462421049)
    ·
      refine ⟨27190858153220597596815787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36254477537627463462421049 27190858153220597596815787)
      ·
        refine ⟨40786287229830896395223681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27190858153220597596815787 40786287229830896395223681)
        ·
          refine ⟨30589715422373172296417761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40786287229830896395223681 30589715422373172296417761)
          ·
            refine ⟨22942286566779879222313321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30589715422373172296417761 22942286566779879222313321)
            ·
              refine ⟨17206714925084909416734991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22942286566779879222313321 17206714925084909416734991)
              ·
                refine ⟨25810072387627364125102487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17206714925084909416734991 25810072387627364125102487)
                ·
                  refine ⟨38715108581441046187653731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25810072387627364125102487 38715108581441046187653731)
                  ·
                    refine ⟨58072662872161569281480597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38715108581441046187653731 58072662872161569281480597)
                    ·
                      refine ⟨2722156072132573560069403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58072662872161569281480597 2722156072132573560069403)
                      ·
                        rfl

theorem cell23_5301380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_5301380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5301380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5301380 prefixEnd_5301380 := by exact prefixLift 5301380
  have htrace : WordTrace (prefixWord ++ tailWord_5301380) baseStart_5301380 baseEnd_5301380 := by
    simpa [prefixWord, tailWord_5301380, baseEnd_5301380] using wordTrace_append hprefix tailTrace_5301380
  have hstable : (prefixWord ++ tailWord_5301380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5301380).length < 2 ^ (prefixWord ++ tailWord_5301380).sum := by decide
  have hdescent : baseEnd_5301380 < baseStart_5301380 := by decide
  rcases family_descends (prefixWord ++ tailWord_5301380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5301390 : List Nat := [4, 1, 1, 3, 2, 1, 2, 9]
def baseStart_5301390 : Nat := 118140960795 + 5301390 * 2 ^ 59
def prefixEnd_5301390 : Nat := 4983230072969 + 3 ^ 40 * 5301390 * 2
def baseEnd_5301390 : Nat := 100820785442189574849791

theorem tailTrace_5301390 : CollatzResearch.WordTrace tailWord_5301390 prefixEnd_5301390 100820785442189574849791 := by
  unfold tailWord_5301390
  simp only [CollatzResearch.WordTrace]
  refine ⟨24169697282997113771763703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128905052175984606782739749 24169697282997113771763703)
  ·
    refine ⟨36254545924495670657645555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24169697282997113771763703 36254545924495670657645555)
    ·
      refine ⟨54381818886743505986468333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36254545924495670657645555 54381818886743505986468333)
      ·
        refine ⟨20393182082528814744925625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54381818886743505986468333 20393182082528814744925625)
        ·
          refine ⟨15294886561896611058694219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20393182082528814744925625 15294886561896611058694219)
          ·
            refine ⟨22942329842844916588041329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15294886561896611058694219 22942329842844916588041329)
            ·
              refine ⟨17206747382133687441030997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22942329842844916588041329 17206747382133687441030997)
              ·
                refine ⟨100820785442189574849791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17206747382133687441030997 100820785442189574849791)
                ·
                  rfl

theorem cell23_5301390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 9].length) (baseStart_5301390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5301390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5301390 prefixEnd_5301390 := by exact prefixLift 5301390
  have htrace : WordTrace (prefixWord ++ tailWord_5301390) baseStart_5301390 baseEnd_5301390 := by
    simpa [prefixWord, tailWord_5301390, baseEnd_5301390] using wordTrace_append hprefix tailTrace_5301390
  have hstable : (prefixWord ++ tailWord_5301390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5301390).length < 2 ^ (prefixWord ++ tailWord_5301390).sum := by decide
  have hdescent : baseEnd_5301390 < baseStart_5301390 := by decide
  rcases family_descends (prefixWord ++ tailWord_5301390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5301427 : List Nat := [1, 1, 1, 2, 3, 2, 3, 2, 3, 3, 2]
def baseStart_5301427 : Nat := 118140960795 + 5301427 * 2 ^ 59
def prefixEnd_5301427 : Nat := 4983230072969 + 3 ^ 40 * 5301427 * 2
def baseEnd_5301427 : Nat := 2722180205723334876181687

theorem tailTrace_5301427 : CollatzResearch.WordTrace tailWord_5301427 prefixEnd_5301427 2722180205723334876181687 := by
  unfold tailWord_5301427
  simp only [CollatzResearch.WordTrace]
  refine ⟨193358927764842865493206535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128905951843228576995471023 193358927764842865493206535)
  ·
    refine ⟨290038391647264298239809803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193358927764842865493206535 290038391647264298239809803)
    ·
      refine ⟨435057587470896447359714705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290038391647264298239809803 435057587470896447359714705)
      ·
        refine ⟨326293190603172335519786029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 435057587470896447359714705 326293190603172335519786029)
        ·
          refine ⟨122359946476189625819919761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 326293190603172335519786029 122359946476189625819919761)
          ·
            refine ⟨91769959857142219364939821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122359946476189625819919761 91769959857142219364939821)
            ·
              refine ⟨34413734946428332261852433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91769959857142219364939821 34413734946428332261852433)
              ·
                refine ⟨25810301209821249196389325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34413734946428332261852433 25810301209821249196389325)
                ·
                  refine ⟨9678862953682968448645997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25810301209821249196389325 9678862953682968448645997)
                  ·
                    refine ⟨3629573607631113168242249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9678862953682968448645997 3629573607631113168242249)
                    ·
                      refine ⟨2722180205723334876181687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3629573607631113168242249 2722180205723334876181687)
                      ·
                        rfl

theorem cell23_5301427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 2, 3, 3, 2].length) (baseStart_5301427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5301427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5301427 prefixEnd_5301427 := by exact prefixLift 5301427
  have htrace : WordTrace (prefixWord ++ tailWord_5301427) baseStart_5301427 baseEnd_5301427 := by
    simpa [prefixWord, tailWord_5301427, baseEnd_5301427] using wordTrace_append hprefix tailTrace_5301427
  have hstable : (prefixWord ++ tailWord_5301427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5301427).length < 2 ^ (prefixWord ++ tailWord_5301427).sum := by decide
  have hdescent : baseEnd_5301427 < baseStart_5301427 := by decide
  rcases family_descends (prefixWord ++ tailWord_5301427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5301461 : List Nat := [1, 3, 2, 4, 1, 2, 1, 3, 1, 3, 2]
def baseStart_5301461 : Nat := 118140960795 + 5301461 * 2 ^ 59
def prefixEnd_5301461 : Nat := 4983230072969 + 3 ^ 40 * 5301461 * 2
def baseEnd_5301461 : Nat := 2722197664065587743156531

theorem tailTrace_5301461 : CollatzResearch.WordTrace tailWord_5301461 prefixEnd_5301461 2722197664065587743156531 := by
  unfold tailWord_5301461
  simp only [CollatzResearch.WordTrace]
  refine ⟨193360167846719689299944237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128906778564479792866629491 193360167846719689299944237)
  ·
    refine ⟨72510062942519883487479089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 193360167846719689299944237 72510062942519883487479089)
    ·
      refine ⟨54382547206889912615609317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72510062942519883487479089 54382547206889912615609317)
      ·
        refine ⟨10196727601291858615426747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54382547206889912615609317 10196727601291858615426747)
        ·
          refine ⟨15295091401937787923140121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10196727601291858615426747 15295091401937787923140121)
          ·
            refine ⟨11471318551453340942355091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15295091401937787923140121 11471318551453340942355091)
            ·
              refine ⟨17206977827180011413532637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11471318551453340942355091 17206977827180011413532637)
              ·
                refine ⟨6452616685192504280074739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17206977827180011413532637 6452616685192504280074739)
                ·
                  refine ⟨9678925027788756420112109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6452616685192504280074739 9678925027788756420112109)
                  ·
                    refine ⟨3629596885420783657542041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9678925027788756420112109 3629596885420783657542041)
                    ·
                      refine ⟨2722197664065587743156531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3629596885420783657542041 2722197664065587743156531)
                      ·
                        rfl

theorem cell23_5301461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_5301461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5301461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5301461 prefixEnd_5301461 := by exact prefixLift 5301461
  have htrace : WordTrace (prefixWord ++ tailWord_5301461) baseStart_5301461 baseEnd_5301461 := by
    simpa [prefixWord, tailWord_5301461, baseEnd_5301461] using wordTrace_append hprefix tailTrace_5301461
  have hstable : (prefixWord ++ tailWord_5301461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5301461).length < 2 ^ (prefixWord ++ tailWord_5301461).sum := by decide
  have hdescent : baseEnd_5301461 < baseStart_5301461 := by decide
  rcases family_descends (prefixWord ++ tailWord_5301461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5301527 : List Nat := [1, 1, 3, 4, 1, 1, 3, 2, 2, 5]
def baseStart_5301527 : Nat := 118140960795 + 5301527 * 2 ^ 59
def prefixEnd_5301527 : Nat := 4983230072969 + 3 ^ 40 * 5301527 * 2
def baseEnd_5301527 : Nat := 907410517929594828310409

theorem tailTrace_5301527 : CollatzResearch.WordTrace tailWord_5301527 prefixEnd_5301527 907410517929594828310409 := by
  unfold tailWord_5301527
  simp only [CollatzResearch.WordTrace]
  refine ⟨193362575064480582571846835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128908383376320388381231223 193362575064480582571846835)
  ·
    refine ⟨290043862596720873857770253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193362575064480582571846835 290043862596720873857770253)
    ·
      refine ⟨108766448473770327696663845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 290043862596720873857770253 108766448473770327696663845)
      ·
        refine ⟨20393709088831936443124471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 108766448473770327696663845 20393709088831936443124471)
        ·
          refine ⟨30590563633247904664686707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20393709088831936443124471 30590563633247904664686707)
          ·
            refine ⟨45885845449871856997030061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30590563633247904664686707 45885845449871856997030061)
            ·
              refine ⟨17207192043701946373886273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45885845449871856997030061 17207192043701946373886273)
              ·
                refine ⟨12905394032776459780414705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17207192043701946373886273 12905394032776459780414705)
                ·
                  refine ⟨9679045524582344835311029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12905394032776459780414705 9679045524582344835311029)
                  ·
                    refine ⟨907410517929594828310409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9679045524582344835311029 907410517929594828310409)
                    ·
                      rfl

theorem cell23_5301527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 2, 2, 5].length) (baseStart_5301527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5301527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5301527 prefixEnd_5301527 := by exact prefixLift 5301527
  have htrace : WordTrace (prefixWord ++ tailWord_5301527) baseStart_5301527 baseEnd_5301527 := by
    simpa [prefixWord, tailWord_5301527, baseEnd_5301527] using wordTrace_append hprefix tailTrace_5301527
  have hstable : (prefixWord ++ tailWord_5301527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5301527).length < 2 ^ (prefixWord ++ tailWord_5301527).sum := by decide
  have hdescent : baseEnd_5301527 < baseStart_5301527 := by decide
  rcases family_descends (prefixWord ++ tailWord_5301527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5301560 : List Nat := [2, 1, 2, 1, 3, 1, 1, 2, 1, 3, 6]
def baseStart_5301560 : Nat := 118140960795 + 5301560 * 2 ^ 59
def prefixEnd_5301560 : Nat := 4983230072969 + 3 ^ 40 * 5301560 * 2
def baseEnd_5301560 : Nat := 2722248498650382855818575

theorem tailTrace_5301560 : CollatzResearch.WordTrace tailWord_5301560 prefixEnd_5301560 2722248498650382855818575 := by
  unfold tailWord_5301560
  simp only [CollatzResearch.WordTrace]
  refine ⟨96681889336680514603899067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128909185782240686138532089 96681889336680514603899067)
  ·
    refine ⟨145022834005020771905848601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96681889336680514603899067 145022834005020771905848601)
    ·
      refine ⟨108767125503765578929386451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145022834005020771905848601 108767125503765578929386451)
      ·
        refine ⟨163150688255648368394079677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108767125503765578929386451 163150688255648368394079677)
        ·
          refine ⟨61181508095868138147779879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 163150688255648368394079677 61181508095868138147779879)
          ·
            refine ⟨91772262143802207221669819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61181508095868138147779879 91772262143802207221669819)
            ·
              refine ⟨137658393215703310832504729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91772262143802207221669819 137658393215703310832504729)
              ·
                refine ⟨103243794911777483124378547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 137658393215703310832504729 103243794911777483124378547)
                ·
                  refine ⟨154865692367666224686567821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 103243794911777483124378547 154865692367666224686567821)
                  ·
                    refine ⟨58074634637874834257462933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 154865692367666224686567821 58074634637874834257462933)
                    ·
                      refine ⟨2722248498650382855818575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58074634637874834257462933 2722248498650382855818575)
                      ·
                        rfl

theorem cell23_5301560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 1, 3, 6].length) (baseStart_5301560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5301560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5301560 prefixEnd_5301560 := by exact prefixLift 5301560
  have htrace : WordTrace (prefixWord ++ tailWord_5301560) baseStart_5301560 baseEnd_5301560 := by
    simpa [prefixWord, tailWord_5301560, baseEnd_5301560] using wordTrace_append hprefix tailTrace_5301560
  have hstable : (prefixWord ++ tailWord_5301560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5301560).length < 2 ^ (prefixWord ++ tailWord_5301560).sum := by decide
  have hdescent : baseEnd_5301560 < baseStart_5301560 := by decide
  rcases family_descends (prefixWord ++ tailWord_5301560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5301564 : List Nat := [2, 2, 2, 2, 1, 4, 2, 1, 2, 1, 4]
def baseStart_5301564 : Nat := 118140960795 + 5301564 * 2 ^ 59
def prefixEnd_5301564 : Nat := 4983230072969 + 3 ^ 40 * 5301564 * 2
def baseEnd_5301564 : Nat := 2722250552573000840168557

theorem tailTrace_5301564 : CollatzResearch.WordTrace tailWord_5301564 prefixEnd_5301564 2722250552573000840168557 := by
  unfold tailWord_5301564
  simp only [CollatzResearch.WordTrace]
  refine ⟨96681962282673268945471873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128909283043564358593962497 96681962282673268945471873)
  ·
    refine ⟨72511471712004951709103905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96681962282673268945471873 72511471712004951709103905)
    ·
      refine ⟨54383603784003713781827929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72511471712004951709103905 54383603784003713781827929)
      ·
        refine ⟨40787702838002785336370947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54383603784003713781827929 40787702838002785336370947)
        ·
          refine ⟨61181554257004178004556421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40787702838002785336370947 61181554257004178004556421)
          ·
            refine ⟨11471541423188283375854329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61181554257004178004556421 11471541423188283375854329)
            ·
              refine ⟨8603656067391212531890747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11471541423188283375854329 8603656067391212531890747)
              ·
                refine ⟨12905484101086818797836121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8603656067391212531890747 12905484101086818797836121)
                ·
                  refine ⟨9679113075815114098377091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12905484101086818797836121 9679113075815114098377091)
                  ·
                    refine ⟨14518669613722671147565637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9679113075815114098377091 14518669613722671147565637)
                    ·
                      refine ⟨2722250552573000840168557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14518669613722671147565637 2722250552573000840168557)
                      ·
                        rfl

theorem cell23_5301564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 1, 2, 1, 4].length) (baseStart_5301564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5301564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5301564 prefixEnd_5301564 := by exact prefixLift 5301564
  have htrace : WordTrace (prefixWord ++ tailWord_5301564) baseStart_5301564 baseEnd_5301564 := by
    simpa [prefixWord, tailWord_5301564, baseEnd_5301564] using wordTrace_append hprefix tailTrace_5301564
  have hstable : (prefixWord ++ tailWord_5301564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5301564).length < 2 ^ (prefixWord ++ tailWord_5301564).sum := by decide
  have hdescent : baseEnd_5301564 < baseStart_5301564 := by decide
  rcases family_descends (prefixWord ++ tailWord_5301564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5301587 : List Nat := [1, 1, 1, 2, 1, 1, 8, 2, 6]
def baseStart_5301587 : Nat := 118140960795 + 5301587 * 2 ^ 59
def prefixEnd_5301587 : Nat := 4983230072969 + 3 ^ 40 * 5301587 * 2
def baseEnd_5301587 : Nat := 302473595847561583353439

theorem tailTrace_5301587 : CollatzResearch.WordTrace tailWord_5301587 prefixEnd_5301587 302473595847561583353439 := by
  unfold tailWord_5301587
  simp only [CollatzResearch.WordTrace]
  refine ⟨193364763444263212819031015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128909842296175475212687343 193364763444263212819031015)
  ·
    refine ⟨290047145166394819228546523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193364763444263212819031015 290047145166394819228546523)
    ·
      refine ⟨435070717749592228842819785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290047145166394819228546523 435070717749592228842819785)
      ·
        refine ⟨326303038312194171632114839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 435070717749592228842819785 326303038312194171632114839)
        ·
          refine ⟨489454557468291257448172259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 326303038312194171632114839 489454557468291257448172259)
          ·
            refine ⟨734181836202436886172258389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 489454557468291257448172259 734181836202436886172258389)
            ·
              refine ⟨8603693392997307259831153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 734181836202436886172258389 8603693392997307259831153)
              ·
                refine ⟨6452770044747980444873365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8603693392997307259831153 6452770044747980444873365)
                ·
                  refine ⟨302473595847561583353439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6452770044747980444873365 302473595847561583353439)
                  ·
                    rfl

theorem cell23_5301587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 2, 6].length) (baseStart_5301587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5301587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5301587 prefixEnd_5301587 := by exact prefixLift 5301587
  have htrace : WordTrace (prefixWord ++ tailWord_5301587) baseStart_5301587 baseEnd_5301587 := by
    simpa [prefixWord, tailWord_5301587, baseEnd_5301587] using wordTrace_append hprefix tailTrace_5301587
  have hstable : (prefixWord ++ tailWord_5301587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5301587).length < 2 ^ (prefixWord ++ tailWord_5301587).sum := by decide
  have hdescent : baseEnd_5301587 < baseStart_5301587 := by decide
  rcases family_descends (prefixWord ++ tailWord_5301587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5301591 : List Nat := [1, 1, 3, 2, 3, 3, 1, 4, 1, 4]
def baseStart_5301591 : Nat := 118140960795 + 5301591 * 2 ^ 59
def prefixEnd_5301591 : Nat := 4983230072969 + 3 ^ 40 * 5301591 * 2
def baseEnd_5301591 : Nat := 907421472183557411510311

theorem tailTrace_5301591 : CollatzResearch.WordTrace tailWord_5301591 prefixEnd_5301591 907421472183557411510311 := by
  unfold tailWord_5301591
  simp only [CollatzResearch.WordTrace]
  refine ⟨193364909336248721502176627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128909939557499147668117751 193364909336248721502176627)
  ·
    refine ⟨290047364004373082253264941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193364909336248721502176627 290047364004373082253264941)
    ·
      refine ⟨108767761501639905844974353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 290047364004373082253264941 108767761501639905844974353)
      ·
        refine ⟨81575821126229929383730765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108767761501639905844974353 81575821126229929383730765)
        ·
          refine ⟨30590932922336223518899037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81575821126229929383730765 30590932922336223518899037)
          ·
            refine ⟨11471599845876083819587139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30590932922336223518899037 11471599845876083819587139)
            ·
              refine ⟨17207399768814125729380709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11471599845876083819587139 17207399768814125729380709)
              ·
                refine ⟨3226387456652648574258883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17207399768814125729380709 3226387456652648574258883)
                ·
                  refine ⟨4839581184978972861388325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3226387456652648574258883 4839581184978972861388325)
                  ·
                    refine ⟨907421472183557411510311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4839581184978972861388325 907421472183557411510311)
                    ·
                      rfl

theorem cell23_5301591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 4, 1, 4].length) (baseStart_5301591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5301591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5301591 prefixEnd_5301591 := by exact prefixLift 5301591
  have htrace : WordTrace (prefixWord ++ tailWord_5301591) baseStart_5301591 baseEnd_5301591 := by
    simpa [prefixWord, tailWord_5301591, baseEnd_5301591] using wordTrace_append hprefix tailTrace_5301591
  have hstable : (prefixWord ++ tailWord_5301591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5301591).length < 2 ^ (prefixWord ++ tailWord_5301591).sum := by decide
  have hdescent : baseEnd_5301591 < baseStart_5301591 := by decide
  rcases family_descends (prefixWord ++ tailWord_5301591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5301617 : List Nat := [1, 2, 2, 2, 1, 2, 4, 1, 3, 5]
def baseStart_5301617 : Nat := 118140960795 + 5301617 * 2 ^ 59
def prefixEnd_5301617 : Nat := 4983230072969 + 3 ^ 40 * 5301617 * 2
def baseEnd_5301617 : Nat := 907425922349229710935271

theorem tailTrace_5301617 : CollatzResearch.WordTrace tailWord_5301617 prefixEnd_5301617 907425922349229710935271 := by
  unfold tailWord_5301617
  simp only [CollatzResearch.WordTrace]
  refine ⟨193365857634154527942623105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128910571756103018628415403 193365857634154527942623105)
  ·
    refine ⟨145024393225615895956967329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193365857634154527942623105 145024393225615895956967329)
    ·
      refine ⟨108768294919211921967725497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145024393225615895956967329 108768294919211921967725497)
      ·
        refine ⟨81576221189408941475794123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108768294919211921967725497 81576221189408941475794123)
        ·
          refine ⟨122364331784113412213691185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81576221189408941475794123 122364331784113412213691185)
          ·
            refine ⟨91773248838085059160268389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122364331784113412213691185 91773248838085059160268389)
            ·
              refine ⟨17207484157140948592550323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91773248838085059160268389 17207484157140948592550323)
              ·
                refine ⟨25811226235711422888825485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17207484157140948592550323 25811226235711422888825485)
                ·
                  refine ⟨9679209838391783583309557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25811226235711422888825485 9679209838391783583309557)
                  ·
                    refine ⟨907425922349229710935271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9679209838391783583309557 907425922349229710935271)
                    ·
                      rfl

theorem cell23_5301617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 1, 3, 5].length) (baseStart_5301617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5301617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5301617 prefixEnd_5301617 := by exact prefixLift 5301617
  have htrace : WordTrace (prefixWord ++ tailWord_5301617) baseStart_5301617 baseEnd_5301617 := by
    simpa [prefixWord, tailWord_5301617, baseEnd_5301617] using wordTrace_append hprefix tailTrace_5301617
  have hstable : (prefixWord ++ tailWord_5301617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5301617).length < 2 ^ (prefixWord ++ tailWord_5301617).sum := by decide
  have hdescent : baseEnd_5301617 < baseStart_5301617 := by decide
  rcases family_descends (prefixWord ++ tailWord_5301617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5301657 : List Nat := [1, 2, 1, 2, 1, 5, 1, 1, 3, 1, 5]
def baseStart_5301657 : Nat := 118140960795 + 5301657 * 2 ^ 59
def prefixEnd_5301657 : Nat := 4983230072969 + 3 ^ 40 * 5301657 * 2
def baseEnd_5301657 : Nat := 2722298306273868976305629

theorem tailTrace_5301657 : CollatzResearch.WordTrace tailWord_5301657 prefixEnd_5301657 2722298306273868976305629 := by
  unfold tailWord_5301657
  simp only [CollatzResearch.WordTrace]
  refine ⟨193367316554009614774079225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128911544369339743182719483 193367316554009614774079225)
  ·
    refine ⟨145025487415507211080559419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193367316554009614774079225 145025487415507211080559419)
    ·
      refine ⟨217538231123260816620839129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145025487415507211080559419 217538231123260816620839129)
      ·
        refine ⟨163153673342445612465629347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 217538231123260816620839129 163153673342445612465629347)
        ·
          refine ⟨244730510013668418698444021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163153673342445612465629347 244730510013668418698444021)
          ·
            refine ⟨22943485313781414252979127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 244730510013668418698444021 22943485313781414252979127)
            ·
              refine ⟨34415227970672121379468691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22943485313781414252979127 34415227970672121379468691)
              ·
                refine ⟨51622841956008182069203037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34415227970672121379468691 51622841956008182069203037)
                ·
                  refine ⟨19358565733503068275951139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51622841956008182069203037 19358565733503068275951139)
                  ·
                    refine ⟨29037848600254602413926709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19358565733503068275951139 29037848600254602413926709)
                    ·
                      refine ⟨2722298306273868976305629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29037848600254602413926709 2722298306273868976305629)
                      ·
                        rfl

theorem cell23_5301657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 3, 1, 5].length) (baseStart_5301657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5301657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5301657 prefixEnd_5301657 := by exact prefixLift 5301657
  have htrace : WordTrace (prefixWord ++ tailWord_5301657) baseStart_5301657 baseEnd_5301657 := by
    simpa [prefixWord, tailWord_5301657, baseEnd_5301657] using wordTrace_append hprefix tailTrace_5301657
  have hstable : (prefixWord ++ tailWord_5301657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5301657).length < 2 ^ (prefixWord ++ tailWord_5301657).sum := by decide
  have hdescent : baseEnd_5301657 < baseStart_5301657 := by decide
  rcases family_descends (prefixWord ++ tailWord_5301657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5301667 : List Nat := [1, 1, 1, 4, 1, 3, 3, 1, 1, 1, 6]
def baseStart_5301667 : Nat := 118140960795 + 5301667 * 2 ^ 59
def prefixEnd_5301667 : Nat := 4983230072969 + 3 ^ 40 * 5301667 * 2
def baseEnd_5301667 : Nat := 2722303441080413937180583

theorem tailTrace_5301667 : CollatzResearch.WordTrace tailWord_5301667 prefixEnd_5301667 2722303441080413937180583 := by
  unfold tailWord_5301667
  simp only [CollatzResearch.WordTrace]
  refine ⟨193367681283973386481943255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128911787522648924321295503 193367681283973386481943255)
  ·
    refine ⟨290051521925960079722914883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193367681283973386481943255 290051521925960079722914883)
    ·
      refine ⟨435077282888940119584372325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290051521925960079722914883 435077282888940119584372325)
      ·
        refine ⟨81576990541676272422069811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 435077282888940119584372325 81576990541676272422069811)
        ·
          refine ⟨122365485812514408633104717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81576990541676272422069811 122365485812514408633104717)
          ·
            refine ⟨45887057179692903237414269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 122365485812514408633104717 45887057179692903237414269)
            ·
              refine ⟨17207646442384838714030351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45887057179692903237414269 17207646442384838714030351)
              ·
                refine ⟨25811469663577258071045527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17207646442384838714030351 25811469663577258071045527)
                ·
                  refine ⟨38717204495365887106568291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25811469663577258071045527 38717204495365887106568291)
                  ·
                    refine ⟨58075806743048830659852437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38717204495365887106568291 58075806743048830659852437)
                    ·
                      refine ⟨2722303441080413937180583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58075806743048830659852437 2722303441080413937180583)
                      ·
                        rfl

theorem cell23_5301667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 1, 1, 1, 6].length) (baseStart_5301667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5301667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5301667 prefixEnd_5301667 := by exact prefixLift 5301667
  have htrace : WordTrace (prefixWord ++ tailWord_5301667) baseStart_5301667 baseEnd_5301667 := by
    simpa [prefixWord, tailWord_5301667, baseEnd_5301667] using wordTrace_append hprefix tailTrace_5301667
  have hstable : (prefixWord ++ tailWord_5301667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5301667).length < 2 ^ (prefixWord ++ tailWord_5301667).sum := by decide
  have hdescent : baseEnd_5301667 < baseStart_5301667 := by decide
  rcases family_descends (prefixWord ++ tailWord_5301667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5301671 : List Nat := [1, 1, 6, 1, 1, 1, 4, 2, 1, 1, 4]
def baseStart_5301671 : Nat := 118140960795 + 5301671 * 2 ^ 59
def prefixEnd_5301671 : Nat := 4983230072969 + 3 ^ 40 * 5301671 * 2
def baseEnd_5301671 : Nat := 2722305495003031921530565

theorem tailTrace_5301671 : CollatzResearch.WordTrace tailWord_5301671 prefixEnd_5301671 2722305495003031921530565 := by
  unfold tailWord_5301671
  simp only [CollatzResearch.WordTrace]
  refine ⟨193367827175958895165088867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128911884783972596776725911 193367827175958895165088867)
  ·
    refine ⟨290051740763938342747633301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193367827175958895165088867 290051740763938342747633301)
    ·
      refine ⟨13596175348309609816295311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 290051740763938342747633301 13596175348309609816295311)
      ·
        refine ⟨20394263022464414724442967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13596175348309609816295311 20394263022464414724442967)
        ·
          refine ⟨30591394533696622086664451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20394263022464414724442967 30591394533696622086664451)
          ·
            refine ⟨45887091800544933129996677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30591394533696622086664451 45887091800544933129996677)
            ·
              refine ⟨8603829712602174961874377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45887091800544933129996677 8603829712602174961874377)
              ·
                refine ⟨6452872284451631221405783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8603829712602174961874377 6452872284451631221405783)
                ·
                  refine ⟨9679308426677446832108675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6452872284451631221405783 9679308426677446832108675)
                  ·
                    refine ⟨14518962640016170248163013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9679308426677446832108675 14518962640016170248163013)
                    ·
                      refine ⟨2722305495003031921530565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14518962640016170248163013 2722305495003031921530565)
                      ·
                        rfl

theorem cell23_5301671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 2, 1, 1, 4].length) (baseStart_5301671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5301671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5301671 prefixEnd_5301671 := by exact prefixLift 5301671
  have htrace : WordTrace (prefixWord ++ tailWord_5301671) baseStart_5301671 baseEnd_5301671 := by
    simpa [prefixWord, tailWord_5301671, baseEnd_5301671] using wordTrace_append hprefix tailTrace_5301671
  have hstable : (prefixWord ++ tailWord_5301671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5301671).length < 2 ^ (prefixWord ++ tailWord_5301671).sum := by decide
  have hdescent : baseEnd_5301671 < baseStart_5301671 := by decide
  rcases family_descends (prefixWord ++ tailWord_5301671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5301747 : List Nat := [1, 1, 1, 2, 2, 2, 2, 3, 1, 3, 5]
def baseStart_5301747 : Nat := 118140960795 + 5301747 * 2 ^ 59
def prefixEnd_5301747 : Nat := 4983230072969 + 3 ^ 40 * 5301747 * 2
def baseEnd_5301747 : Nat := 2722344519532773624180215

theorem tailTrace_5301747 : CollatzResearch.WordTrace tailWord_5301747 prefixEnd_5301747 2722344519532773624180215 := by
  unfold tailWord_5301747
  simp only [CollatzResearch.WordTrace]
  refine ⟨193370599123683560144855495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128913732749122373429903663 193370599123683560144855495)
  ·
    refine ⟨290055898685525340217283243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193370599123683560144855495 290055898685525340217283243)
    ·
      refine ⟨435083848028288010325924865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290055898685525340217283243 435083848028288010325924865)
      ·
        refine ⟨326312886021216007744443649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 435083848028288010325924865 326312886021216007744443649)
        ·
          refine ⟨244734664515912005808332737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 326312886021216007744443649 244734664515912005808332737)
          ·
            refine ⟨183550998386934004356249553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 244734664515912005808332737 183550998386934004356249553)
            ·
              refine ⟨137663248790200503267187165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 183550998386934004356249553 137663248790200503267187165)
              ·
                refine ⟨51623718296325188725195187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 137663248790200503267187165 51623718296325188725195187)
                ·
                  refine ⟨77435577444487783087792781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51623718296325188725195187 77435577444487783087792781)
                  ·
                    refine ⟨29038341541682918657922293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 77435577444487783087792781 29038341541682918657922293)
                    ·
                      refine ⟨2722344519532773624180215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29038341541682918657922293 2722344519532773624180215)
                      ·
                        rfl

theorem cell23_5301747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 3, 5].length) (baseStart_5301747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5301747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5301747 prefixEnd_5301747 := by exact prefixLift 5301747
  have htrace : WordTrace (prefixWord ++ tailWord_5301747) baseStart_5301747 baseEnd_5301747 := by
    simpa [prefixWord, tailWord_5301747, baseEnd_5301747] using wordTrace_append hprefix tailTrace_5301747
  have hstable : (prefixWord ++ tailWord_5301747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5301747).length < 2 ^ (prefixWord ++ tailWord_5301747).sum := by decide
  have hdescent : baseEnd_5301747 < baseStart_5301747 := by decide
  rcases family_descends (prefixWord ++ tailWord_5301747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5301834 : List Nat := [3, 1, 2, 1, 1, 3, 1, 1, 3, 3, 4]
def baseStart_5301834 : Nat := 118140960795 + 5301834 * 2 ^ 59
def prefixEnd_5301834 : Nat := 4983230072969 + 3 ^ 40 * 5301834 * 2
def baseEnd_5301834 : Nat := 2722389192349714783792315

theorem tailTrace_5301834 : CollatzResearch.WordTrace tailWord_5301834 prefixEnd_5301834 2722389192349714783792315 := by
  unfold tailWord_5301834
  simp only [CollatzResearch.WordTrace]
  refine ⟨48343443068592093500818139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128915848182912249335515037 48343443068592093500818139)
  ·
    refine ⟨72515164602888140251227209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48343443068592093500818139 72515164602888140251227209)
    ·
      refine ⟨54386373452166105188420407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72515164602888140251227209 54386373452166105188420407)
      ·
        refine ⟨81579560178249157782630611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54386373452166105188420407 81579560178249157782630611)
        ·
          refine ⟨122369340267373736673945917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81579560178249157782630611 122369340267373736673945917)
          ·
            refine ⟨45888502600265151252729719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 122369340267373736673945917 45888502600265151252729719)
            ·
              refine ⟨68832753900397726879094579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45888502600265151252729719 68832753900397726879094579)
              ·
                refine ⟨103249130850596590318641869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68832753900397726879094579 103249130850596590318641869)
                ·
                  refine ⟨38718424068973721369490701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 103249130850596590318641869 38718424068973721369490701)
                  ·
                    refine ⟨14519409025865145513559013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38718424068973721369490701 14519409025865145513559013)
                    ·
                      refine ⟨2722389192349714783792315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14519409025865145513559013 2722389192349714783792315)
                      ·
                        rfl

theorem cell23_5301834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 3, 3, 4].length) (baseStart_5301834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5301834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5301834 prefixEnd_5301834 := by exact prefixLift 5301834
  have htrace : WordTrace (prefixWord ++ tailWord_5301834) baseStart_5301834 baseEnd_5301834 := by
    simpa [prefixWord, tailWord_5301834, baseEnd_5301834] using wordTrace_append hprefix tailTrace_5301834
  have hstable : (prefixWord ++ tailWord_5301834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5301834).length < 2 ^ (prefixWord ++ tailWord_5301834).sum := by decide
  have hdescent : baseEnd_5301834 < baseStart_5301834 := by decide
  rcases family_descends (prefixWord ++ tailWord_5301834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5301844 : List Nat := [2, 4, 1, 1, 1, 2, 1, 1, 2, 8]
def baseStart_5301844 : Nat := 118140960795 + 5301844 * 2 ^ 59
def prefixEnd_5301844 : Nat := 4983230072969 + 3 ^ 40 * 5301844 * 2
def baseEnd_5301844 : Nat := 907464775718753248222423

theorem tailTrace_5301844 : CollatzResearch.WordTrace tailWord_5301844 prefixEnd_5301844 907464775718753248222423 := by
  unfold tailWord_5301844
  simp only [CollatzResearch.WordTrace]
  refine ⟨96687068502166072855568293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128916091336221430474091057 96687068502166072855568293)
  ·
    refine ⟨18128825344156138660419055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96687068502166072855568293 18128825344156138660419055)
    ·
      refine ⟨27193238016234207990628583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18128825344156138660419055 27193238016234207990628583)
      ·
        refine ⟨40789857024351311985942875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27193238016234207990628583 40789857024351311985942875)
        ·
          refine ⟨61184785536526967978914313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40789857024351311985942875 61184785536526967978914313)
          ·
            refine ⟨45888589152395225984185735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61184785536526967978914313 45888589152395225984185735)
            ·
              refine ⟨68832883728592838976278603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45888589152395225984185735 68832883728592838976278603)
              ·
                refine ⟨103249325592889258464417905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68832883728592838976278603 103249325592889258464417905)
                ·
                  refine ⟨77436994194666943848313429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 103249325592889258464417905 77436994194666943848313429)
                  ·
                    refine ⟨907464775718753248222423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 77436994194666943848313429 907464775718753248222423)
                    ·
                      rfl

theorem cell23_5301844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 2, 8].length) (baseStart_5301844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5301844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5301844 prefixEnd_5301844 := by exact prefixLift 5301844
  have htrace : WordTrace (prefixWord ++ tailWord_5301844) baseStart_5301844 baseEnd_5301844 := by
    simpa [prefixWord, tailWord_5301844, baseEnd_5301844] using wordTrace_append hprefix tailTrace_5301844
  have hstable : (prefixWord ++ tailWord_5301844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5301844).length < 2 ^ (prefixWord ++ tailWord_5301844).sum := by decide
  have hdescent : baseEnd_5301844 < baseStart_5301844 := by decide
  rcases family_descends (prefixWord ++ tailWord_5301844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5301935 : List Nat := [1, 1, 2, 1, 2, 4, 3, 4, 1, 1, 3]
def baseStart_5301935 : Nat := 118140960795 + 5301935 * 2 ^ 59
def prefixEnd_5301935 : Nat := 4983230072969 + 3 ^ 40 * 5301935 * 2
def baseEnd_5301935 : Nat := 2722441053895818888629351

theorem tailTrace_5301935 : CollatzResearch.WordTrace tailWord_5301935 prefixEnd_5301935 2722441053895818888629351 := by
  unfold tailWord_5301935
  simp only [CollatzResearch.WordTrace]
  refine ⟨193377456047002468252699259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128918304031334978835132839 193377456047002468252699259)
  ·
    refine ⟨290066184070503702379048889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193377456047002468252699259 290066184070503702379048889)
    ·
      refine ⟨217549638052877776784286667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 290066184070503702379048889 217549638052877776784286667)
      ·
        refine ⟨326324457079316665176430001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217549638052877776784286667 326324457079316665176430001)
        ·
          refine ⟨244743342809487498882322501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 326324457079316665176430001 244743342809487498882322501)
          ·
            refine ⟨45889376776778906040435469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 244743342809487498882322501 45889376776778906040435469)
            ·
              refine ⟨17208516291292089765163301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45889376776778906040435469 17208516291292089765163301)
              ·
                refine ⟨3226596804617266830968119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17208516291292089765163301 3226596804617266830968119)
                ·
                  refine ⟨4839895206925900246452179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3226596804617266830968119 4839895206925900246452179)
                  ·
                    refine ⟨7259842810388850369678269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4839895206925900246452179 7259842810388850369678269)
                    ·
                      refine ⟨2722441053895818888629351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7259842810388850369678269 2722441053895818888629351)
                      ·
                        rfl

theorem cell23_5301935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 4, 1, 1, 3].length) (baseStart_5301935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5301935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5301935 prefixEnd_5301935 := by exact prefixLift 5301935
  have htrace : WordTrace (prefixWord ++ tailWord_5301935) baseStart_5301935 baseEnd_5301935 := by
    simpa [prefixWord, tailWord_5301935, baseEnd_5301935] using wordTrace_append hprefix tailTrace_5301935
  have hstable : (prefixWord ++ tailWord_5301935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5301935).length < 2 ^ (prefixWord ++ tailWord_5301935).sum := by decide
  have hdescent : baseEnd_5301935 < baseStart_5301935 := by decide
  rcases family_descends (prefixWord ++ tailWord_5301935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5301951 : List Nat := [1, 1, 2, 2, 2, 3, 4, 1, 1, 6]
def baseStart_5301951 : Nat := 118140960795 + 5301951 * 2 ^ 59
def prefixEnd_5301951 : Nat := 4983230072969 + 3 ^ 40 * 5301951 * 2
def baseEnd_5301951 : Nat := 907483089862096942009759

theorem tailTrace_5301951 : CollatzResearch.WordTrace tailWord_5301951 prefixEnd_5301951 907483089862096942009759 := by
  unfold tailWord_5301951
  simp only [CollatzResearch.WordTrace]
  refine ⟨193378039614944502985281707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128918693076629668656854471 193378039614944502985281707)
  ·
    refine ⟨290067059422416754477922561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193378039614944502985281707 290067059422416754477922561)
    ·
      refine ⟨217550294566812565858441921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 290067059422416754477922561 217550294566812565858441921)
      ·
        refine ⟨163162720925109424393831441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 217550294566812565858441921 163162720925109424393831441)
        ·
          refine ⟨122372040693832068295373581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163162720925109424393831441 122372040693832068295373581)
          ·
            refine ⟨45889515260187025610765093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 122372040693832068295373581 45889515260187025610765093)
            ·
              refine ⟨8604284111285067302018455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45889515260187025610765093 8604284111285067302018455)
              ·
                refine ⟨12906426166927600953027683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8604284111285067302018455 12906426166927600953027683)
                ·
                  refine ⟨19359639250391401429541525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12906426166927600953027683 19359639250391401429541525)
                  ·
                    refine ⟨907483089862096942009759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19359639250391401429541525 907483089862096942009759)
                    ·
                      rfl

theorem cell23_5301951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 1, 1, 6].length) (baseStart_5301951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5301951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5301951 prefixEnd_5301951 := by exact prefixLift 5301951
  have htrace : WordTrace (prefixWord ++ tailWord_5301951) baseStart_5301951 baseEnd_5301951 := by
    simpa [prefixWord, tailWord_5301951, baseEnd_5301951] using wordTrace_append hprefix tailTrace_5301951
  have hstable : (prefixWord ++ tailWord_5301951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5301951).length < 2 ^ (prefixWord ++ tailWord_5301951).sum := by decide
  have hdescent : baseEnd_5301951 < baseStart_5301951 := by decide
  rcases family_descends (prefixWord ++ tailWord_5301951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5301962 : List Nat := [3, 1, 2, 1, 5, 2, 1, 1, 2, 3, 2]
def baseStart_5301962 : Nat := 118140960795 + 5301962 * 2 ^ 59
def prefixEnd_5301962 : Nat := 4983230072969 + 3 ^ 40 * 5301962 * 2
def baseEnd_5301962 : Nat := 2722454917873490282991727

theorem tailTrace_5301962 : CollatzResearch.WordTrace tailWord_5301962 prefixEnd_5301962 2722454917873490282991727 := by
  unfold tailWord_5301962
  simp only [CollatzResearch.WordTrace]
  refine ⟨48344610204476162965983035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128918960545269767909288093 48344610204476162965983035)
  ·
    refine ⟨72516915306714244448974553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48344610204476162965983035 72516915306714244448974553)
    ·
      refine ⟨54387686480035683336730915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72516915306714244448974553 54387686480035683336730915)
      ·
        refine ⟨81581529720053525005096373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54387686480035683336730915 81581529720053525005096373)
        ·
          refine ⟨7648268411255017969227785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 81581529720053525005096373 7648268411255017969227785)
          ·
            refine ⟨5736201308441263476920839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7648268411255017969227785 5736201308441263476920839)
            ·
              refine ⟨8604301962661895215381259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5736201308441263476920839 8604301962661895215381259)
              ·
                refine ⟨12906452943992842823071889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8604301962661895215381259 12906452943992842823071889)
                ·
                  refine ⟨9679839707994632117303917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12906452943992842823071889 9679839707994632117303917)
                  ·
                    refine ⟨3629939890497987043988969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9679839707994632117303917 3629939890497987043988969)
                    ·
                      refine ⟨2722454917873490282991727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3629939890497987043988969 2722454917873490282991727)
                      ·
                        rfl

theorem cell23_5301962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 1, 2, 3, 2].length) (baseStart_5301962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5301962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5301962 prefixEnd_5301962 := by exact prefixLift 5301962
  have htrace : WordTrace (prefixWord ++ tailWord_5301962) baseStart_5301962 baseEnd_5301962 := by
    simpa [prefixWord, tailWord_5301962, baseEnd_5301962] using wordTrace_append hprefix tailTrace_5301962
  have hstable : (prefixWord ++ tailWord_5301962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5301962).length < 2 ^ (prefixWord ++ tailWord_5301962).sum := by decide
  have hdescent : baseEnd_5301962 < baseStart_5301962 := by decide
  rcases family_descends (prefixWord ++ tailWord_5301962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5301972 : List Nat := [2, 4, 1, 3, 1, 3, 2, 1, 1, 5]
def baseStart_5301972 : Nat := 118140960795 + 5301972 * 2 ^ 59
def prefixEnd_5301972 : Nat := 4983230072969 + 3 ^ 40 * 5301972 * 2
def baseEnd_5301972 : Nat := 907486684226678414622227

theorem tailTrace_5301972 : CollatzResearch.WordTrace tailWord_5301972 prefixEnd_5301972 907486684226678414622227 := by
  unfold tailWord_5301972
  simp only [CollatzResearch.WordTrace]
  refine ⟨96689402773934211785898085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128919203698578949047864113 96689402773934211785898085)
  ·
    refine ⟨18129263020112664709855891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96689402773934211785898085 18129263020112664709855891)
    ·
      refine ⟨27193894530168997064783837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18129263020112664709855891 27193894530168997064783837)
      ·
        refine ⟨10197710448813373899293939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27193894530168997064783837 10197710448813373899293939)
        ·
          refine ⟨15296565673220060848940909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10197710448813373899293939 15296565673220060848940909)
          ·
            refine ⟨5736212127457522818352841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15296565673220060848940909 5736212127457522818352841)
            ·
              refine ⟨4302159095593142113764631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5736212127457522818352841 4302159095593142113764631)
              ·
                refine ⟨6453238643389713170646947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4302159095593142113764631 6453238643389713170646947)
                ·
                  refine ⟨9679857965084569755970421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6453238643389713170646947 9679857965084569755970421)
                  ·
                    refine ⟨907486684226678414622227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9679857965084569755970421 907486684226678414622227)
                    ·
                      rfl

theorem cell23_5301972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 2, 1, 1, 5].length) (baseStart_5301972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5301972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5301972 prefixEnd_5301972 := by exact prefixLift 5301972
  have htrace : WordTrace (prefixWord ++ tailWord_5301972) baseStart_5301972 baseEnd_5301972 := by
    simpa [prefixWord, tailWord_5301972, baseEnd_5301972] using wordTrace_append hprefix tailTrace_5301972
  have hstable : (prefixWord ++ tailWord_5301972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5301972).length < 2 ^ (prefixWord ++ tailWord_5301972).sum := by decide
  have hdescent : baseEnd_5301972 < baseStart_5301972 := by decide
  rcases family_descends (prefixWord ++ tailWord_5301972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5301992 : List Nat := [2, 1, 4, 1, 3, 2, 2, 1, 3, 2, 2]
def baseStart_5301992 : Nat := 118140960795 + 5301992 * 2 ^ 59
def prefixEnd_5301992 : Nat := 4983230072969 + 3 ^ 40 * 5301992 * 2
def baseEnd_5301992 : Nat := 2722470322293125165616589

theorem tailTrace_5301992 : CollatzResearch.WordTrace tailWord_5301992 prefixEnd_5301992 2722470322293125165616589 := by
  unfold tailWord_5301992
  simp only [CollatzResearch.WordTrace]
  refine ⟨96689767503897983493762115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128919690005197311325016153 96689767503897983493762115)
  ·
    refine ⟨145034651255846975240643173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96689767503897983493762115 145034651255846975240643173)
    ·
      refine ⟨27193997110471307857620595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 145034651255846975240643173 27193997110471307857620595)
      ·
        refine ⟨40790995665706961786430893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27193997110471307857620595 40790995665706961786430893)
        ·
          refine ⟨15296623374640110669911585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40790995665706961786430893 15296623374640110669911585)
          ·
            refine ⟨11472467530980083002433689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15296623374640110669911585 11472467530980083002433689)
            ·
              refine ⟨8604350648235062251825267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11472467530980083002433689 8604350648235062251825267)
              ·
                refine ⟨12906525972352593377737901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8604350648235062251825267 12906525972352593377737901)
                ·
                  refine ⟨4839947239632222516651713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12906525972352593377737901 4839947239632222516651713)
                  ·
                    refine ⟨3629960429724166887488785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4839947239632222516651713 3629960429724166887488785)
                    ·
                      refine ⟨2722470322293125165616589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3629960429724166887488785 2722470322293125165616589)
                      ·
                        rfl

theorem cell23_5301992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 1, 3, 2, 2].length) (baseStart_5301992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5301992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5301992 prefixEnd_5301992 := by exact prefixLift 5301992
  have htrace : WordTrace (prefixWord ++ tailWord_5301992) baseStart_5301992 baseEnd_5301992 := by
    simpa [prefixWord, tailWord_5301992, baseEnd_5301992] using wordTrace_append hprefix tailTrace_5301992
  have hstable : (prefixWord ++ tailWord_5301992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5301992).length < 2 ^ (prefixWord ++ tailWord_5301992).sum := by decide
  have hdescent : baseEnd_5301992 < baseStart_5301992 := by decide
  rcases family_descends (prefixWord ++ tailWord_5301992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5302069 : List Nat := [1, 3, 3, 1, 4, 2, 1, 2, 1, 3, 2]
def baseStart_5302069 : Nat := 118140960795 + 5302069 * 2 ^ 59
def prefixEnd_5302069 : Nat := 4983230072969 + 3 ^ 40 * 5302069 * 2
def baseEnd_5302069 : Nat := 2722509860303521364353735

theorem tailTrace_5302069 : CollatzResearch.WordTrace tailWord_5302069 prefixEnd_5302069 2722509860303521364353735 := by
  unfold tailWord_5302069
  simp only [CollatzResearch.WordTrace]
  refine ⟨193382343428517009138077261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128921562285678006092051507 193382343428517009138077261)
  ·
    refine ⟨72518378785693878426778973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 193382343428517009138077261 72518378785693878426778973)
    ·
      refine ⟨27194392044635204410042115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72518378785693878426778973 27194392044635204410042115)
      ·
        refine ⟨40791588066952806615063173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27194392044635204410042115 40791588066952806615063173)
        ·
          refine ⟨7648422762553651240324345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40791588066952806615063173 7648422762553651240324345)
          ·
            refine ⟨5736317071915238430243259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7648422762553651240324345 5736317071915238430243259)
            ·
              refine ⟨8604475607872857645364889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5736317071915238430243259 8604475607872857645364889)
              ·
                refine ⟨6453356705904643234023667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8604475607872857645364889 6453356705904643234023667)
                ·
                  refine ⟨9680035058856964851035501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6453356705904643234023667 9680035058856964851035501)
                  ·
                    refine ⟨3630013147071361819138313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9680035058856964851035501 3630013147071361819138313)
                    ·
                      refine ⟨2722509860303521364353735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3630013147071361819138313 2722509860303521364353735)
                      ·
                        rfl

theorem cell23_5302069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 2, 1, 3, 2].length) (baseStart_5302069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5302069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5302069 prefixEnd_5302069 := by exact prefixLift 5302069
  have htrace : WordTrace (prefixWord ++ tailWord_5302069) baseStart_5302069 baseEnd_5302069 := by
    simpa [prefixWord, tailWord_5302069, baseEnd_5302069] using wordTrace_append hprefix tailTrace_5302069
  have hstable : (prefixWord ++ tailWord_5302069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5302069).length < 2 ^ (prefixWord ++ tailWord_5302069).sum := by decide
  have hdescent : baseEnd_5302069 < baseStart_5302069 := by decide
  rcases family_descends (prefixWord ++ tailWord_5302069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5302115 : List Nat := [1, 1, 1, 5, 4, 1, 1, 1, 2, 3, 3]
def baseStart_5302115 : Nat := 118140960795 + 5302115 * 2 ^ 59
def prefixEnd_5302115 : Nat := 4983230072969 + 3 ^ 40 * 5302115 * 2
def baseEnd_5302115 : Nat := 2722533480413628184378523

theorem tailTrace_5302115 : CollatzResearch.WordTrace tailWord_5302115 prefixEnd_5302115 2722533480413628184378523 := by
  unfold tailWord_5302115
  simp only [CollatzResearch.WordTrace]
  refine ⟨193384021186350358994251799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128922680790900239329501199 193384021186350358994251799)
  ·
    refine ⟨290076031779525538491377699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193384021186350358994251799 290076031779525538491377699)
    ·
      refine ⟨435114047669288307737066549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290076031779525538491377699 435114047669288307737066549)
      ·
        refine ⟨40791941968995778850349989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 435114047669288307737066549 40791941968995778850349989)
        ·
          refine ⟨7648489119186708534440623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40791941968995778850349989 7648489119186708534440623)
          ·
            refine ⟨11472733678780062801660935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7648489119186708534440623 11472733678780062801660935)
            ·
              refine ⟨17209100518170094202491403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11472733678780062801660935 17209100518170094202491403)
              ·
                refine ⟨25813650777255141303737105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17209100518170094202491403 25813650777255141303737105)
                ·
                  refine ⟨19360238082941355977802829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25813650777255141303737105 19360238082941355977802829)
                  ·
                    refine ⟨7260089281103008491676061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19360238082941355977802829 7260089281103008491676061)
                    ·
                      refine ⟨2722533480413628184378523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7260089281103008491676061 2722533480413628184378523)
                      ·
                        rfl

theorem cell23_5302115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 1, 2, 3, 3].length) (baseStart_5302115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5302115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5302115 prefixEnd_5302115 := by exact prefixLift 5302115
  have htrace : WordTrace (prefixWord ++ tailWord_5302115) baseStart_5302115 baseEnd_5302115 := by
    simpa [prefixWord, tailWord_5302115, baseEnd_5302115] using wordTrace_append hprefix tailTrace_5302115
  have hstable : (prefixWord ++ tailWord_5302115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5302115).length < 2 ^ (prefixWord ++ tailWord_5302115).sum := by decide
  have hdescent : baseEnd_5302115 < baseStart_5302115 := by decide
  rcases family_descends (prefixWord ++ tailWord_5302115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5302165 : List Nat := [1, 3, 2, 1, 1, 3, 4, 1, 3, 4]
def baseStart_5302165 : Nat := 118140960795 + 5302165 * 2 ^ 59
def prefixEnd_5302165 : Nat := 4983230072969 + 3 ^ 40 * 5302165 * 2
def baseEnd_5302165 : Nat := 907519718148784329584431

theorem tailTrace_5302165 : CollatzResearch.WordTrace tailWord_5302165 prefixEnd_5302165 907519718148784329584431 := by
  unfold tailWord_5302165
  simp only [CollatzResearch.WordTrace]
  refine ⟨193385844836169217533571949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128923896557446145022381299 193385844836169217533571949)
  ·
    refine ⟨72519691813563456575089481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 193385844836169217533571949 72519691813563456575089481)
    ·
      refine ⟨54389768860172592431317111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72519691813563456575089481 54389768860172592431317111)
      ·
        refine ⟨81584653290258888646975667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54389768860172592431317111 81584653290258888646975667)
        ·
          refine ⟨122376979935388332970463501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81584653290258888646975667 122376979935388332970463501)
          ·
            refine ⟨45891367475770624863923813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 122376979935388332970463501 45891367475770624863923813)
            ·
              refine ⟨8604631401706992161985715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45891367475770624863923813 8604631401706992161985715)
              ·
                refine ⟨12906947102560488242978573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8604631401706992161985715 12906947102560488242978573)
                ·
                  refine ⟨4840105163460183091116965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12906947102560488242978573 4840105163460183091116965)
                  ·
                    refine ⟨907519718148784329584431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4840105163460183091116965 907519718148784329584431)
                    ·
                      rfl

theorem cell23_5302165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 1, 3, 4].length) (baseStart_5302165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5302165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5302165 prefixEnd_5302165 := by exact prefixLift 5302165
  have htrace : WordTrace (prefixWord ++ tailWord_5302165) baseStart_5302165 baseEnd_5302165 := by
    simpa [prefixWord, tailWord_5302165, baseEnd_5302165] using wordTrace_append hprefix tailTrace_5302165
  have hstable : (prefixWord ++ tailWord_5302165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5302165).length < 2 ^ (prefixWord ++ tailWord_5302165).sum := by decide
  have hdescent : baseEnd_5302165 < baseStart_5302165 := by decide
  rcases family_descends (prefixWord ++ tailWord_5302165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5302172 : List Nat := [2, 2, 3, 3, 1, 1, 2, 1, 2, 4, 2]
def baseStart_5302172 : Nat := 118140960795 + 5302172 * 2 ^ 59
def prefixEnd_5302172 : Nat := 4983230072969 + 3 ^ 40 * 5302172 * 2
def baseEnd_5302172 : Nat := 2722562748810934461365761

theorem tailTrace_5302172 : CollatzResearch.WordTrace tailWord_5302172 prefixEnd_5302172 2722562748810934461365761 := by
  unfold tailWord_5302172
  simp only [CollatzResearch.WordTrace]
  refine ⟨96693050073571928864538385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128924066764762571819384513 96693050073571928864538385)
  ·
    refine ⟨72519787555178946648403789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96693050073571928864538385 72519787555178946648403789)
    ·
      refine ⟨27194920333192104993151421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72519787555178946648403789 27194920333192104993151421)
      ·
        refine ⟨10198095124947039372431783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27194920333192104993151421 10198095124947039372431783)
        ·
          refine ⟨15297142687420559058647675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10198095124947039372431783 15297142687420559058647675)
          ·
            refine ⟨22945714031130838587971513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15297142687420559058647675 22945714031130838587971513)
            ·
              refine ⟨17209285523348128940978635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22945714031130838587971513 17209285523348128940978635)
              ·
                refine ⟨25813928285022193411467953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17209285523348128940978635 25813928285022193411467953)
                ·
                  refine ⟨19360446213766645058600965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25813928285022193411467953 19360446213766645058600965)
                  ·
                    refine ⟨3630083665081245948487681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19360446213766645058600965 3630083665081245948487681)
                    ·
                      refine ⟨2722562748810934461365761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3630083665081245948487681 2722562748810934461365761)
                      ·
                        rfl

theorem cell23_5302172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_5302172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5302172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5302172 prefixEnd_5302172 := by exact prefixLift 5302172
  have htrace : WordTrace (prefixWord ++ tailWord_5302172) baseStart_5302172 baseEnd_5302172 := by
    simpa [prefixWord, tailWord_5302172, baseEnd_5302172] using wordTrace_append hprefix tailTrace_5302172
  have hstable : (prefixWord ++ tailWord_5302172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5302172).length < 2 ^ (prefixWord ++ tailWord_5302172).sum := by decide
  have hdescent : baseEnd_5302172 < baseStart_5302172 := by decide
  rcases family_descends (prefixWord ++ tailWord_5302172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5302265 : List Nat := [1, 2, 1, 3, 1, 4, 3, 1, 1, 1, 5]
def baseStart_5302265 : Nat := 118140960795 + 5302265 * 2 ^ 59
def prefixEnd_5302265 : Nat := 4983230072969 + 3 ^ 40 * 5302265 * 2
def baseEnd_5302265 : Nat := 2722610502511802597502833

theorem tailTrace_5302265 : CollatzResearch.WordTrace tailWord_5302265 prefixEnd_5302265 2722610502511802597502833 := by
  unfold tailWord_5302265
  simp only [CollatzResearch.WordTrace]
  refine ⟨193389492135806934612212249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128926328090537956408141499 193389492135806934612212249)
  ·
    refine ⟨145042119101855200959159187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193389492135806934612212249 145042119101855200959159187)
    ·
      refine ⟨217563178652782801438738781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145042119101855200959159187 217563178652782801438738781)
      ·
        refine ⟨81586191994793550539527043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 217563178652782801438738781 81586191994793550539527043)
        ·
          refine ⟨122379287992190325809290565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81586191994793550539527043 122379287992190325809290565)
          ·
            refine ⟨22946116498535686089241981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 122379287992190325809290565 22946116498535686089241981)
            ·
              refine ⟨8604793686950882283465743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22946116498535686089241981 8604793686950882283465743)
              ·
                refine ⟨12907190530426323425198615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8604793686950882283465743 12907190530426323425198615)
                ·
                  refine ⟨19360785795639485137797923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12907190530426323425198615 19360785795639485137797923)
                  ·
                    refine ⟨29041178693459227706696885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19360785795639485137797923 29041178693459227706696885)
                    ·
                      refine ⟨2722610502511802597502833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29041178693459227706696885 2722610502511802597502833)
                      ·
                        rfl

theorem cell23_5302265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 1, 1, 1, 5].length) (baseStart_5302265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5302265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5302265 prefixEnd_5302265 := by exact prefixLift 5302265
  have htrace : WordTrace (prefixWord ++ tailWord_5302265) baseStart_5302265 baseEnd_5302265 := by
    simpa [prefixWord, tailWord_5302265, baseEnd_5302265] using wordTrace_append hprefix tailTrace_5302265
  have hstable : (prefixWord ++ tailWord_5302265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5302265).length < 2 ^ (prefixWord ++ tailWord_5302265).sum := by decide
  have hdescent : baseEnd_5302265 < baseStart_5302265 := by decide
  rcases family_descends (prefixWord ++ tailWord_5302265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5302329 : List Nat := [1, 2, 1, 5, 3, 1, 1, 1, 4, 1, 3]
def baseStart_5302329 : Nat := 118140960795 + 5302329 * 2 ^ 59
def prefixEnd_5302329 : Nat := 4983230072969 + 3 ^ 40 * 5302329 * 2
def baseEnd_5302329 : Nat := 2722643365273690347102539

theorem tailTrace_5302329 : CollatzResearch.WordTrace tailWord_5302329 prefixEnd_5302329 2722643365273690347102539 := by
  unfold tailWord_5302329
  simp only [CollatzResearch.WordTrace]
  refine ⟨193391826407575073542542041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128927884271716715695028027 193391826407575073542542041)
  ·
    refine ⟨145043869805681305156906531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193391826407575073542542041 145043869805681305156906531)
    ·
      refine ⟨217565804708521957735359797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145043869805681305156906531 217565804708521957735359797)
      ·
        refine ⟨20396794191423933537689981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 217565804708521957735359797 20396794191423933537689981)
        ·
          refine ⟨7648797821783975076633743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20396794191423933537689981 7648797821783975076633743)
          ·
            refine ⟨11473196732675962614950615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7648797821783975076633743 11473196732675962614950615)
            ·
              refine ⟨17209795099013943922425923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11473196732675962614950615 17209795099013943922425923)
              ·
                refine ⟨25814692648520915883638885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17209795099013943922425923 25814692648520915883638885)
                ·
                  refine ⟨4840254871597671728182291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25814692648520915883638885 4840254871597671728182291)
                  ·
                    refine ⟨7260382307396507592273437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4840254871597671728182291 7260382307396507592273437)
                    ·
                      refine ⟨2722643365273690347102539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7260382307396507592273437 2722643365273690347102539)
                      ·
                        rfl

theorem cell23_5302329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 1, 4, 1, 3].length) (baseStart_5302329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5302329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5302329 prefixEnd_5302329 := by exact prefixLift 5302329
  have htrace : WordTrace (prefixWord ++ tailWord_5302329) baseStart_5302329 baseEnd_5302329 := by
    simpa [prefixWord, tailWord_5302329, baseEnd_5302329] using wordTrace_append hprefix tailTrace_5302329
  have hstable : (prefixWord ++ tailWord_5302329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5302329).length < 2 ^ (prefixWord ++ tailWord_5302329).sum := by decide
  have hdescent : baseEnd_5302329 < baseStart_5302329 := by decide
  rcases family_descends (prefixWord ++ tailWord_5302329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5302403 : List Nat := [1, 1, 1, 3, 3, 5, 2, 1, 2, 2, 2]
def baseStart_5302403 : Nat := 118140960795 + 5302403 * 2 ^ 59
def prefixEnd_5302403 : Nat := 4983230072969 + 3 ^ 40 * 5302403 * 2
def baseEnd_5302403 : Nat := 2722681362842123057577199

theorem tailTrace_5302403 : CollatzResearch.WordTrace tailWord_5302403 prefixEnd_5302403 2722681362842123057577199 := by
  unfold tailWord_5302403
  simp only [CollatzResearch.WordTrace]
  refine ⟨193394525409306984180735863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128929683606204656120490575 193394525409306984180735863)
  ·
    refine ⟨290091788113960476271103795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193394525409306984180735863 290091788113960476271103795)
    ·
      refine ⟨435137682170940714406655693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290091788113960476271103795 435137682170940714406655693)
      ·
        refine ⟨163176630814102767902495885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 435137682170940714406655693 163176630814102767902495885)
        ·
          refine ⟨61191236555288537963435957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 163176630814102767902495885 61191236555288537963435957)
          ·
            refine ⟨5736678427058300434072121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 61191236555288537963435957 5736678427058300434072121)
            ·
              refine ⟨4302508820293725325554091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5736678427058300434072121 4302508820293725325554091)
              ·
                refine ⟨6453763230440587988331137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4302508820293725325554091 6453763230440587988331137)
                ·
                  refine ⟨4840322422830440991248353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6453763230440587988331137 4840322422830440991248353)
                  ·
                    refine ⟨3630241817122830743436265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4840322422830440991248353 3630241817122830743436265)
                    ·
                      refine ⟨2722681362842123057577199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3630241817122830743436265 2722681362842123057577199)
                      ·
                        rfl

theorem cell23_5302403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 2, 1, 2, 2, 2].length) (baseStart_5302403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5302403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5302403 prefixEnd_5302403 := by exact prefixLift 5302403
  have htrace : WordTrace (prefixWord ++ tailWord_5302403) baseStart_5302403 baseEnd_5302403 := by
    simpa [prefixWord, tailWord_5302403, baseEnd_5302403] using wordTrace_append hprefix tailTrace_5302403
  have hstable : (prefixWord ++ tailWord_5302403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5302403).length < 2 ^ (prefixWord ++ tailWord_5302403).sum := by decide
  have hdescent : baseEnd_5302403 < baseStart_5302403 := by decide
  rcases family_descends (prefixWord ++ tailWord_5302403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5302425 : List Nat := [1, 2, 1, 2, 1, 2, 1, 5, 1, 3, 4]
def baseStart_5302425 : Nat := 118140960795 + 5302425 * 2 ^ 59
def prefixEnd_5302425 : Nat := 4983230072969 + 3 ^ 40 * 5302425 * 2
def baseEnd_5302425 : Nat := 2722692659416521971502097

theorem tailTrace_5302425 : CollatzResearch.WordTrace tailWord_5302425 prefixEnd_5302425 2722692659416521971502097 := by
  unfold tailWord_5302425
  simp only [CollatzResearch.WordTrace]
  refine ⟨193395327815227281938036729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128930218543484854625357819 193395327815227281938036729)
  ·
    refine ⟨145046495861420461453527547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193395327815227281938036729 145046495861420461453527547)
    ·
      refine ⟨217569743792130692180291321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145046495861420461453527547 217569743792130692180291321)
      ·
        refine ⟨163177307844098019135218491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 217569743792130692180291321 163177307844098019135218491)
        ·
          refine ⟨244765961766147028702827737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163177307844098019135218491 244765961766147028702827737)
          ·
            refine ⟨183574471324610271527120803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 244765961766147028702827737 183574471324610271527120803)
            ·
              refine ⟨275361706986915407290681205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 183574471324610271527120803 275361706986915407290681205)
              ·
                refine ⟨25815160030023319433501363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 275361706986915407290681205 25815160030023319433501363)
                ·
                  refine ⟨38722740045034979150252045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25815160030023319433501363 38722740045034979150252045)
                  ·
                    refine ⟨14521027516888117181344517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38722740045034979150252045 14521027516888117181344517)
                    ·
                      refine ⟨2722692659416521971502097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14521027516888117181344517 2722692659416521971502097)
                      ·
                        rfl

theorem cell23_5302425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 5, 1, 3, 4].length) (baseStart_5302425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5302425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5302425 prefixEnd_5302425 := by exact prefixLift 5302425
  have htrace : WordTrace (prefixWord ++ tailWord_5302425) baseStart_5302425 baseEnd_5302425 := by
    simpa [prefixWord, tailWord_5302425, baseEnd_5302425] using wordTrace_append hprefix tailTrace_5302425
  have hstable : (prefixWord ++ tailWord_5302425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5302425).length < 2 ^ (prefixWord ++ tailWord_5302425).sum := by decide
  have hdescent : baseEnd_5302425 < baseStart_5302425 := by decide
  rcases family_descends (prefixWord ++ tailWord_5302425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5302499 : List Nat := [1, 1, 1, 8, 1, 1, 1, 1, 8]
def baseStart_5302499 : Nat := 118140960795 + 5302499 * 2 ^ 59
def prefixEnd_5302499 : Nat := 4983230072969 + 3 ^ 40 * 5302499 * 2
def baseEnd_5302499 : Nat := 302525628553883853552973

theorem tailTrace_5302499 : CollatzResearch.WordTrace tailWord_5302499 prefixEnd_5302499 302525628553883853552973 := by
  unfold tailWord_5302499
  simp only [CollatzResearch.WordTrace]
  refine ⟨193398026816959192576230551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128932017877972795050820367 193398026816959192576230551)
  ·
    refine ⟨290097040225438788864345827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193398026816959192576230551 290097040225438788864345827)
    ·
      refine ⟨435145560338158183296518741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290097040225438788864345827 435145560338158183296518741)
      ·
        refine ⟨5099362035212791210506079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 435145560338158183296518741 5099362035212791210506079)
        ·
          refine ⟨7649043052819186815759119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5099362035212791210506079 7649043052819186815759119)
          ·
            refine ⟨11473564579228780223638679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7649043052819186815759119 11473564579228780223638679)
            ·
              refine ⟨17210346868843170335458019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11473564579228780223638679 17210346868843170335458019)
              ·
                refine ⟨25815520303264755503187029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17210346868843170335458019 25815520303264755503187029)
                ·
                  refine ⟨302525628553883853552973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25815520303264755503187029 302525628553883853552973)
                  ·
                    rfl

theorem cell23_5302499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 1, 8].length) (baseStart_5302499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5302499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5302499 prefixEnd_5302499 := by exact prefixLift 5302499
  have htrace : WordTrace (prefixWord ++ tailWord_5302499) baseStart_5302499 baseEnd_5302499 := by
    simpa [prefixWord, tailWord_5302499, baseEnd_5302499] using wordTrace_append hprefix tailTrace_5302499
  have hstable : (prefixWord ++ tailWord_5302499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5302499).length < 2 ^ (prefixWord ++ tailWord_5302499).sum := by decide
  have hdescent : baseEnd_5302499 < baseStart_5302499 := by decide
  rcases family_descends (prefixWord ++ tailWord_5302499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5302505 : List Nat := [1, 2, 1, 1, 1, 2, 2, 2, 2, 4, 5]
def baseStart_5302505 : Nat := 118140960795 + 5302505 * 2 ^ 59
def prefixEnd_5302505 : Nat := 4983230072969 + 3 ^ 40 * 5302505 * 2
def baseEnd_5302505 : Nat := 2722733737868881658501729

theorem tailTrace_5302505 : CollatzResearch.WordTrace tailWord_5302505 prefixEnd_5302505 2722733737868881658501729 := by
  unfold tailWord_5302505
  simp only [CollatzResearch.WordTrace]
  refine ⟨193398245654937455600948969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128932163769958303733965979 193398245654937455600948969)
  ·
    refine ⟨145048684241203091700711727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193398245654937455600948969 145048684241203091700711727)
    ·
      refine ⟨217573026361804637551067591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145048684241203091700711727 217573026361804637551067591)
      ·
        refine ⟨326359539542706956326601387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217573026361804637551067591 326359539542706956326601387)
        ·
          refine ⟨489539309314060434489902081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 326359539542706956326601387 489539309314060434489902081)
          ·
            refine ⟨367154481985545325867426561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 489539309314060434489902081 367154481985545325867426561)
            ·
              refine ⟨275365861489158994400569921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 367154481985545325867426561 275365861489158994400569921)
              ·
                refine ⟨206524396116869245800427441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 275365861489158994400569921 206524396116869245800427441)
                ·
                  refine ⟨154893297087651934350320581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 206524396116869245800427441 154893297087651934350320581)
                  ·
                    refine ⟨29042493203934737690685109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 154893297087651934350320581 29042493203934737690685109)
                    ·
                      refine ⟨2722733737868881658501729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29042493203934737690685109 2722733737868881658501729)
                      ·
                        rfl

theorem cell23_5302505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 4, 5].length) (baseStart_5302505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5302505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5302505 prefixEnd_5302505 := by exact prefixLift 5302505
  have htrace : WordTrace (prefixWord ++ tailWord_5302505) baseStart_5302505 baseEnd_5302505 := by
    simpa [prefixWord, tailWord_5302505, baseEnd_5302505] using wordTrace_append hprefix tailTrace_5302505
  have hstable : (prefixWord ++ tailWord_5302505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5302505).length < 2 ^ (prefixWord ++ tailWord_5302505).sum := by decide
  have hdescent : baseEnd_5302505 < baseStart_5302505 := by decide
  rcases family_descends (prefixWord ++ tailWord_5302505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5302526 : List Nat := [4, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3]
def baseStart_5302526 : Nat := 118140960795 + 5302526 * 2 ^ 59
def prefixEnd_5302526 : Nat := 4983230072969 + 3 ^ 40 * 5302526 * 2
def baseEnd_5302526 : Nat := 2722744520962626076339133

theorem tailTrace_5302526 : CollatzResearch.WordTrace tailWord_5302526 prefixEnd_5302526 2722744520962626076339133 := by
  unfold tailWord_5302526
  simp only [CollatzResearch.WordTrace]
  refine ⟨24174876448482672023432929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128932674391907584124975621 24174876448482672023432929)
  ·
    refine ⟨18131157336362004017574697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24174876448482672023432929 18131157336362004017574697)
    ·
      refine ⟨13598368002271503013181023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18131157336362004017574697 13598368002271503013181023)
      ·
        refine ⟨20397552003407254519771535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13598368002271503013181023 20397552003407254519771535)
        ·
          refine ⟨30596328005110881779657303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20397552003407254519771535 30596328005110881779657303)
          ·
            refine ⟨45894492007666322669485955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30596328005110881779657303 45894492007666322669485955)
            ·
              refine ⟨68841738011499484004228933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45894492007666322669485955 68841738011499484004228933)
              ·
                refine ⟨12907825877156153250792925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68841738011499484004228933 12907825877156153250792925)
                ·
                  refine ⟨4840434703933557469047347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12907825877156153250792925 4840434703933557469047347)
                  ·
                    refine ⟨7260652055900336203571021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4840434703933557469047347 7260652055900336203571021)
                    ·
                      refine ⟨2722744520962626076339133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7260652055900336203571021 2722744520962626076339133)
                      ·
                        rfl

theorem cell23_5302526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3].length) (baseStart_5302526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5302526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5302526 prefixEnd_5302526 := by exact prefixLift 5302526
  have htrace : WordTrace (prefixWord ++ tailWord_5302526) baseStart_5302526 baseEnd_5302526 := by
    simpa [prefixWord, tailWord_5302526, baseEnd_5302526] using wordTrace_append hprefix tailTrace_5302526
  have hstable : (prefixWord ++ tailWord_5302526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5302526).length < 2 ^ (prefixWord ++ tailWord_5302526).sum := by decide
  have hdescent : baseEnd_5302526 < baseStart_5302526 := by decide
  rcases family_descends (prefixWord ++ tailWord_5302526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5302529 : List Nat := [1, 2, 4, 1, 1, 2, 4, 2, 1, 5]
def baseStart_5302529 : Nat := 118140960795 + 5302529 * 2 ^ 59
def prefixEnd_5302529 : Nat := 4983230072969 + 3 ^ 40 * 5302529 * 2
def baseEnd_5302529 : Nat := 907582020468196521533873

theorem tailTrace_5302529 : CollatzResearch.WordTrace tailWord_5302529 prefixEnd_5302529 907582020468196521533873 := by
  unfold tailWord_5302529
  simp only [CollatzResearch.WordTrace]
  refine ⟨193399121006850507699822641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128932747337900338466548427 193399121006850507699822641)
  ·
    refine ⟨145049340755137880774866981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193399121006850507699822641 145049340755137880774866981)
    ·
      refine ⟨27196751391588352645287559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 145049340755137880774866981 27196751391588352645287559)
      ·
        refine ⟨40795127087382528967931339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27196751391588352645287559 40795127087382528967931339)
        ·
          refine ⟨61192690631073793451897009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40795127087382528967931339 61192690631073793451897009)
          ·
            refine ⟨45894517973305345088922757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61192690631073793451897009 45894517973305345088922757)
            ·
              refine ⟨8605222119994752204173017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45894517973305345088922757 8605222119994752204173017)
              ·
                refine ⟨6453916589996064153129763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8605222119994752204173017 6453916589996064153129763)
                ·
                  refine ⟨9680874884994096229694645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6453916589996064153129763 9680874884994096229694645)
                  ·
                    refine ⟨907582020468196521533873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9680874884994096229694645 907582020468196521533873)
                    ·
                      rfl

theorem cell23_5302529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 2, 1, 5].length) (baseStart_5302529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5302529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5302529 prefixEnd_5302529 := by exact prefixLift 5302529
  have htrace : WordTrace (prefixWord ++ tailWord_5302529) baseStart_5302529 baseEnd_5302529 := by
    simpa [prefixWord, tailWord_5302529, baseEnd_5302529] using wordTrace_append hprefix tailTrace_5302529
  have hstable : (prefixWord ++ tailWord_5302529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5302529).length < 2 ^ (prefixWord ++ tailWord_5302529).sum := by decide
  have hdescent : baseEnd_5302529 < baseStart_5302529 := by decide
  rcases family_descends (prefixWord ++ tailWord_5302529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5302542 : List Nat := [4, 1, 1, 2, 1, 2, 2, 1, 3, 6]
def baseStart_5302542 : Nat := 118140960795 + 5302542 * 2 ^ 59
def prefixEnd_5302542 : Nat := 4983230072969 + 3 ^ 40 * 5302542 * 2
def baseEnd_5302542 : Nat := 907584245551032671246353

theorem tailTrace_5302542 : CollatzResearch.WordTrace tailWord_5302542 prefixEnd_5302542 907584245551032671246353 := by
  unfold tailWord_5302542
  simp only [CollatzResearch.WordTrace]
  refine ⟨24174949394475426365005735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128933063437202273946697253 24174949394475426365005735)
  ·
    refine ⟨36262424091713139547508603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24174949394475426365005735 36262424091713139547508603)
    ·
      refine ⟨54393636137569709321262905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36262424091713139547508603 54393636137569709321262905)
      ·
        refine ⟨40795227103177281990947179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54393636137569709321262905 40795227103177281990947179)
        ·
          refine ⟨61192840654765922986420769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40795227103177281990947179 61192840654765922986420769)
          ·
            refine ⟨45894630491074442239815577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61192840654765922986420769 45894630491074442239815577)
            ·
              refine ⟨34420972868305831679861683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45894630491074442239815577 34420972868305831679861683)
              ·
                refine ⟨51631459302458747519792525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34420972868305831679861683 51631459302458747519792525)
                ·
                  refine ⟨19361797238422030319922197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51631459302458747519792525 19361797238422030319922197)
                  ·
                    refine ⟨907584245551032671246353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19361797238422030319922197 907584245551032671246353)
                    ·
                      rfl

theorem cell23_5302542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 3, 6].length) (baseStart_5302542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5302542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5302542 prefixEnd_5302542 := by exact prefixLift 5302542
  have htrace : WordTrace (prefixWord ++ tailWord_5302542) baseStart_5302542 baseEnd_5302542 := by
    simpa [prefixWord, tailWord_5302542, baseEnd_5302542] using wordTrace_append hprefix tailTrace_5302542
  have hstable : (prefixWord ++ tailWord_5302542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5302542).length < 2 ^ (prefixWord ++ tailWord_5302542).sum := by decide
  have hdescent : baseEnd_5302542 < baseStart_5302542 := by decide
  rcases family_descends (prefixWord ++ tailWord_5302542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5302549 : List Nat := [1, 3, 2, 1, 2, 1, 4, 3, 1, 1, 4]
def baseStart_5302549 : Nat := 118140960795 + 5302549 * 2 ^ 59
def prefixEnd_5302549 : Nat := 4983230072969 + 3 ^ 40 * 5302549 * 2
def baseEnd_5302549 : Nat := 2722756331017679486351527

theorem tailTrace_5302549 : CollatzResearch.WordTrace tailWord_5302549 prefixEnd_5302549 2722756331017679486351527 := by
  unfold tailWord_5302549
  simp only [CollatzResearch.WordTrace]
  refine ⟨193399850466778051115550701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128933233644518700743700467 193399850466778051115550701)
  ·
    refine ⟨72524943925041769168331513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 193399850466778051115550701 72524943925041769168331513)
    ·
      refine ⟨54393707943781326876248635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72524943925041769168331513 54393707943781326876248635)
      ·
        refine ⟨81590561915671990314372953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54393707943781326876248635 81590561915671990314372953)
        ·
          refine ⟨61192921436753992735779715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81590561915671990314372953 61192921436753992735779715)
          ·
            refine ⟨91789382155130989103669573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61192921436753992735779715 91789382155130989103669573)
            ·
              refine ⟨17210509154087060456938045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91789382155130989103669573 17210509154087060456938045)
              ·
                refine ⟨6453940932782647671351767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17210509154087060456938045 6453940932782647671351767)
                ·
                  refine ⟨9680911399173971507027651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6453940932782647671351767 9680911399173971507027651)
                  ·
                    refine ⟨14521367098760957260541477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9680911399173971507027651 14521367098760957260541477)
                    ·
                      refine ⟨2722756331017679486351527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14521367098760957260541477 2722756331017679486351527)
                      ·
                        rfl

theorem cell23_5302549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 3, 1, 1, 4].length) (baseStart_5302549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5302549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5302549 prefixEnd_5302549 := by exact prefixLift 5302549
  have htrace : WordTrace (prefixWord ++ tailWord_5302549) baseStart_5302549 baseEnd_5302549 := by
    simpa [prefixWord, tailWord_5302549, baseEnd_5302549] using wordTrace_append hprefix tailTrace_5302549
  have hstable : (prefixWord ++ tailWord_5302549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5302549).length < 2 ^ (prefixWord ++ tailWord_5302549).sum := by decide
  have hdescent : baseEnd_5302549 < baseStart_5302549 := by decide
  rcases family_descends (prefixWord ++ tailWord_5302549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5302555 : List Nat := [1, 1, 1, 1, 1, 1, 17]
def baseStart_5302555 : Nat := 118140960795 + 5302555 * 2 ^ 59
def prefixEnd_5302555 : Nat := 4983230072969 + 3 ^ 40 * 5302555 * 2
def baseEnd_5302555 : Nat := 33614313727180326702179

theorem tailTrace_5302555 : CollatzResearch.WordTrace tailWord_5302555 prefixEnd_5302555 33614313727180326702179 := by
  unfold tailWord_5302555
  simp only [CollatzResearch.WordTrace]
  refine ⟨193400069304756314140269119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128933379536504209426846079 193400069304756314140269119)
  ·
    refine ⟨290100103957134471210403679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193400069304756314140269119 290100103957134471210403679)
    ·
      refine ⟨435150155935701706815605519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290100103957134471210403679 435150155935701706815605519)
      ·
        refine ⟨652725233903552560223408279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 435150155935701706815605519 652725233903552560223408279)
        ·
          refine ⟨979087850855328840335112419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 652725233903552560223408279 979087850855328840335112419)
          ·
            refine ⟨1468631776282993260502668629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 979087850855328840335112419 1468631776282993260502668629)
            ·
              refine ⟨33614313727180326702179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 17 1468631776282993260502668629 33614313727180326702179)
              ·
                rfl

theorem cell23_5302555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 17].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 17].length) (baseStart_5302555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5302555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5302555 prefixEnd_5302555 := by exact prefixLift 5302555
  have htrace : WordTrace (prefixWord ++ tailWord_5302555) baseStart_5302555 baseEnd_5302555 := by
    simpa [prefixWord, tailWord_5302555, baseEnd_5302555] using wordTrace_append hprefix tailTrace_5302555
  have hstable : (prefixWord ++ tailWord_5302555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5302555).length < 2 ^ (prefixWord ++ tailWord_5302555).sum := by decide
  have hdescent : baseEnd_5302555 < baseStart_5302555 := by decide
  rcases family_descends (prefixWord ++ tailWord_5302555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5302559 : List Nat := [1, 1, 2, 4, 3, 1, 2, 1, 4, 4]
def baseStart_5302559 : Nat := 118140960795 + 5302559 * 2 ^ 59
def prefixEnd_5302559 : Nat := 4983230072969 + 3 ^ 40 * 5302559 * 2
def baseEnd_5302559 : Nat := 907587155274741482408827

theorem tailTrace_5302559 : CollatzResearch.WordTrace tailWord_5302559 prefixEnd_5302559 907587155274741482408827 := by
  unfold tailWord_5302559
  simp only [CollatzResearch.WordTrace]
  refine ⟨193400215196741822823414731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128933476797827881882276487 193400215196741822823414731)
  ·
    refine ⟨290100322795112734235122097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193400215196741822823414731 290100322795112734235122097)
    ·
      refine ⟨217575242096334550676341573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 290100322795112734235122097 217575242096334550676341573)
      ·
        refine ⟨40795357893062728251814045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 217575242096334550676341573 40795357893062728251814045)
        ·
          refine ⟨15298259209898523094430267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40795357893062728251814045 15298259209898523094430267)
          ·
            refine ⟨22947388814847784641645401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15298259209898523094430267 22947388814847784641645401)
            ·
              refine ⟨17210541611135838481234051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22947388814847784641645401 17210541611135838481234051)
              ·
                refine ⟨25815812416703757721851077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17210541611135838481234051 25815812416703757721851077)
                ·
                  refine ⟨4840464828131954572847077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25815812416703757721851077 4840464828131954572847077)
                  ·
                    refine ⟨907587155274741482408827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4840464828131954572847077 907587155274741482408827)
                    ·
                      rfl

theorem cell23_5302559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 1, 4, 4].length) (baseStart_5302559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5302559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5302559 prefixEnd_5302559 := by exact prefixLift 5302559
  have htrace : WordTrace (prefixWord ++ tailWord_5302559) baseStart_5302559 baseEnd_5302559 := by
    simpa [prefixWord, tailWord_5302559, baseEnd_5302559] using wordTrace_append hprefix tailTrace_5302559
  have hstable : (prefixWord ++ tailWord_5302559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5302559).length < 2 ^ (prefixWord ++ tailWord_5302559).sum := by decide
  have hdescent : baseEnd_5302559 < baseStart_5302559 := by decide
  rcases family_descends (prefixWord ++ tailWord_5302559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5302560 : List Nat := [2, 1, 1, 5, 2, 2, 3, 2, 1, 1, 3]
def baseStart_5302560 : Nat := 118140960795 + 5302560 * 2 ^ 59
def prefixEnd_5302560 : Nat := 4983230072969 + 3 ^ 40 * 5302560 * 2
def baseEnd_5302560 : Nat := 2722761979304878943313977

theorem tailTrace_5302560 : CollatzResearch.WordTrace tailWord_5302560 prefixEnd_5302560 2722761979304878943313977 := by
  unfold tailWord_5302560
  simp only [CollatzResearch.WordTrace]
  refine ⟨96700125834869099997100567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128933501113158799996134089 96700125834869099997100567)
  ·
    refine ⟨145050188752303649995650851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96700125834869099997100567 145050188752303649995650851)
    ·
      refine ⟨217575283128455474993476277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145050188752303649995650851 217575283128455474993476277)
      ·
        refine ⟨20397682793292700780638401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 217575283128455474993476277 20397682793292700780638401)
        ·
          refine ⟨15298262094969525585478801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20397682793292700780638401 15298262094969525585478801)
          ·
            refine ⟨11473696571227144189109101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15298262094969525585478801 11473696571227144189109101)
            ·
              refine ⟨4302636214210179070915913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11473696571227144189109101 4302636214210179070915913)
              ·
                refine ⟨3226977160657634303186935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4302636214210179070915913 3226977160657634303186935)
                ·
                  refine ⟨4840465740986451454780403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3226977160657634303186935 4840465740986451454780403)
                  ·
                    refine ⟨7260698611479677182170605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4840465740986451454780403 7260698611479677182170605)
                    ·
                      refine ⟨2722761979304878943313977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7260698611479677182170605 2722761979304878943313977)
                      ·
                        rfl

theorem cell23_5302560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 3, 2, 1, 1, 3].length) (baseStart_5302560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5302560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5302560 prefixEnd_5302560 := by exact prefixLift 5302560
  have htrace : WordTrace (prefixWord ++ tailWord_5302560) baseStart_5302560 baseEnd_5302560 := by
    simpa [prefixWord, tailWord_5302560, baseEnd_5302560] using wordTrace_append hprefix tailTrace_5302560
  have hstable : (prefixWord ++ tailWord_5302560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5302560).length < 2 ^ (prefixWord ++ tailWord_5302560).sum := by decide
  have hdescent : baseEnd_5302560 < baseStart_5302560 := by decide
  rcases family_descends (prefixWord ++ tailWord_5302560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5302567 : List Nat := [1, 1, 8, 1, 2, 1, 2, 1, 6]
def baseStart_5302567 : Nat := 118140960795 + 5302567 * 2 ^ 59
def prefixEnd_5302567 : Nat := 4983230072969 + 3 ^ 40 * 5302567 * 2
def baseEnd_5302567 : Nat := 302529508185495601769605

theorem tailTrace_5302567 : CollatzResearch.WordTrace tailWord_5302567 prefixEnd_5302567 302529508185495601769605 := by
  unfold tailWord_5302567
  simp only [CollatzResearch.WordTrace]
  refine ⟨193400506980712840189705955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128933671320475226793137303 193400506980712840189705955)
  ·
    refine ⟨290100760471069260284558933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193400506980712840189705955 290100760471069260284558933)
    ·
      refine ⟨3399618286770342893959675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 290100760471069260284558933 3399618286770342893959675)
      ·
        refine ⟨5099427430155514340939513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3399618286770342893959675 5099427430155514340939513)
        ·
          refine ⟨3824570572616635755704635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5099427430155514340939513 3824570572616635755704635)
          ·
            refine ⟨5736855858924953633556953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3824570572616635755704635 5736855858924953633556953)
            ·
              refine ⟨4302641894193715225167715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5736855858924953633556953 4302641894193715225167715)
              ·
                refine ⟨6453962841290572837751573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4302641894193715225167715 6453962841290572837751573)
                ·
                  refine ⟨302529508185495601769605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6453962841290572837751573 302529508185495601769605)
                  ·
                    rfl

theorem cell23_5302567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 2, 1, 6].length) (baseStart_5302567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5302567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5302567 prefixEnd_5302567 := by exact prefixLift 5302567
  have htrace : WordTrace (prefixWord ++ tailWord_5302567) baseStart_5302567 baseEnd_5302567 := by
    simpa [prefixWord, tailWord_5302567, baseEnd_5302567] using wordTrace_append hprefix tailTrace_5302567
  have hstable : (prefixWord ++ tailWord_5302567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5302567).length < 2 ^ (prefixWord ++ tailWord_5302567).sum := by decide
  have hdescent : baseEnd_5302567 < baseStart_5302567 := by decide
  rcases family_descends (prefixWord ++ tailWord_5302567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5302586 : List Nat := [3, 1, 1, 1, 4, 2, 3, 2, 1, 2, 3]
def baseStart_5302586 : Nat := 118140960795 + 5302586 * 2 ^ 59
def prefixEnd_5302586 : Nat := 4983230072969 + 3 ^ 40 * 5302586 * 2
def baseEnd_5302586 : Nat := 2722775329801895841588857

theorem tailTrace_5302586 : CollatzResearch.WordTrace tailWord_5302586 prefixEnd_5302586 2722775329801895841588857 := by
  unfold tailWord_5302586
  simp only [CollatzResearch.WordTrace]
  refine ⟨48350299991911001608661903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128934133311762670956431741 48350299991911001608661903)
  ·
    refine ⟨72525449987866502412992855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48350299991911001608661903 72525449987866502412992855)
    ·
      refine ⟨108788174981799753619489283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72525449987866502412992855 108788174981799753619489283)
      ·
        refine ⟨163182262472699630429233925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108788174981799753619489283 163182262472699630429233925)
        ·
          refine ⟨30596674213631180705481361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 163182262472699630429233925 30596674213631180705481361)
          ·
            refine ⟨22947505660223385529111021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30596674213631180705481361 22947505660223385529111021)
            ·
              refine ⟨8605314622583769573416633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22947505660223385529111021 8605314622583769573416633)
              ·
                refine ⟨6453985966937827180062475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8605314622583769573416633 6453985966937827180062475)
                ·
                  refine ⟨9680978950406740770093713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6453985966937827180062475 9680978950406740770093713)
                  ·
                    refine ⟨7260734212805055577570285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9680978950406740770093713 7260734212805055577570285)
                    ·
                      refine ⟨2722775329801895841588857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7260734212805055577570285 2722775329801895841588857)
                      ·
                        rfl

theorem cell23_5302586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 2, 1, 2, 3].length) (baseStart_5302586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5302586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5302586 prefixEnd_5302586 := by exact prefixLift 5302586
  have htrace : WordTrace (prefixWord ++ tailWord_5302586) baseStart_5302586 baseEnd_5302586 := by
    simpa [prefixWord, tailWord_5302586, baseEnd_5302586] using wordTrace_append hprefix tailTrace_5302586
  have hstable : (prefixWord ++ tailWord_5302586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5302586).length < 2 ^ (prefixWord ++ tailWord_5302586).sum := by decide
  have hdescent : baseEnd_5302586 < baseStart_5302586 := by decide
  rcases family_descends (prefixWord ++ tailWord_5302586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5302599 : List Nat := [1, 1, 4, 1, 2, 2, 3, 2, 1, 3, 3]
def baseStart_5302599 : Nat := 118140960795 + 5302599 * 2 ^ 59
def prefixEnd_5302599 : Nat := 4983230072969 + 3 ^ 40 * 5302599 * 2
def baseEnd_5302599 : Nat := 2722782005050404290726297

theorem tailTrace_5302599 : CollatzResearch.WordTrace tailWord_5302599 prefixEnd_5302599 2722782005050404290726297 := by
  unfold tailWord_5302599
  simp only [CollatzResearch.WordTrace]
  refine ⟨193401674116596909654870851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128934449411064606436580567 193401674116596909654870851)
  ·
    refine ⟨290102511174895364482306277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193401674116596909654870851 290102511174895364482306277)
    ·
      refine ⟨54394220845292880840432427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 290102511174895364482306277 54394220845292880840432427)
      ·
        refine ⟨81591331267939321260648641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54394220845292880840432427 81591331267939321260648641)
        ·
          refine ⟨61193498450954490945486481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81591331267939321260648641 61193498450954490945486481)
          ·
            refine ⟨45895123838215868209114861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61193498450954490945486481 45895123838215868209114861)
            ·
              refine ⟨17210671439330950578418073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45895123838215868209114861 17210671439330950578418073)
              ·
                refine ⟨12908003579498212933813555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17210671439330950578418073 12908003579498212933813555)
                ·
                  refine ⟨19362005369247319400720333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12908003579498212933813555 19362005369247319400720333)
                  ·
                    refine ⟨7260752013467744775270125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19362005369247319400720333 7260752013467744775270125)
                    ·
                      refine ⟨2722782005050404290726297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7260752013467744775270125 2722782005050404290726297)
                      ·
                        rfl

theorem cell23_5302599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 2, 1, 3, 3].length) (baseStart_5302599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5302599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5302599 prefixEnd_5302599 := by exact prefixLift 5302599
  have htrace : WordTrace (prefixWord ++ tailWord_5302599) baseStart_5302599 baseEnd_5302599 := by
    simpa [prefixWord, tailWord_5302599, baseEnd_5302599] using wordTrace_append hprefix tailTrace_5302599
  have hstable : (prefixWord ++ tailWord_5302599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5302599).length < 2 ^ (prefixWord ++ tailWord_5302599).sum := by decide
  have hdescent : baseEnd_5302599 < baseStart_5302599 := by decide
  rcases family_descends (prefixWord ++ tailWord_5302599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5302696 : List Nat := [2, 1, 6, 1, 1, 1, 2, 2, 7]
def baseStart_5302696 : Nat := 118140960795 + 5302696 * 2 ^ 59
def prefixEnd_5302696 : Nat := 4983230072969 + 3 ^ 40 * 5302696 * 2
def baseEnd_5302696 : Nat := 302536868074876712357039

theorem tailTrace_5302696 : CollatzResearch.WordTrace tailWord_5302696 prefixEnd_5302696 302536868074876712357039 := by
  unfold tailWord_5302696
  simp only [CollatzResearch.WordTrace]
  refine ⟨96702605998622747610575971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128936807998163663480767961 96702605998622747610575971)
  ·
    refine ⟨145053908997934121415863957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96702605998622747610575971 145053908997934121415863957)
    ·
      refine ⟨6799401984278161941368623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 145053908997934121415863957 6799401984278161941368623)
      ·
        refine ⟨10199102976417242912052935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6799401984278161941368623 10199102976417242912052935)
        ·
          refine ⟨15298654464625864368079403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10199102976417242912052935 15298654464625864368079403)
          ·
            refine ⟨22947981696938796552119105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15298654464625864368079403 22947981696938796552119105)
            ·
              refine ⟨17210986272704097414089329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22947981696938796552119105 17210986272704097414089329)
              ·
                refine ⟨12908239704528073060566997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17210986272704097414089329 12908239704528073060566997)
                ·
                  refine ⟨302536868074876712357039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12908239704528073060566997 302536868074876712357039)
                  ·
                    rfl

theorem cell23_5302696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 2, 7].length) (baseStart_5302696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5302696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5302696 prefixEnd_5302696 := by exact prefixLift 5302696
  have htrace : WordTrace (prefixWord ++ tailWord_5302696) baseStart_5302696 baseEnd_5302696 := by
    simpa [prefixWord, tailWord_5302696, baseEnd_5302696] using wordTrace_append hprefix tailTrace_5302696
  have hstable : (prefixWord ++ tailWord_5302696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5302696).length < 2 ^ (prefixWord ++ tailWord_5302696).sum := by decide
  have hdescent : baseEnd_5302696 < baseStart_5302696 := by decide
  rcases family_descends (prefixWord ++ tailWord_5302696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5302713 : List Nat := [1, 2, 1, 4, 3, 3, 1, 3, 5]
def baseStart_5302713 : Nat := 118140960795 + 5302713 * 2 ^ 59
def prefixEnd_5302713 : Nat := 4983230072969 + 3 ^ 40 * 5302713 * 2
def baseEnd_5302713 : Nat := 302537837982779649411197

theorem tailTrace_5302713 : CollatzResearch.WordTrace tailWord_5302713 prefixEnd_5302713 302537837982779649411197 := by
  unfold tailWord_5302713
  simp only [CollatzResearch.WordTrace]
  refine ⟨193405832038183907124520793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128937221358789271416347195 193405832038183907124520793)
  ·
    refine ⟨145054374028637930343390595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193405832038183907124520793 145054374028637930343390595)
    ·
      refine ⟨217581561042956895515085893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145054374028637930343390595 217581561042956895515085893)
      ·
        refine ⟨40796542695554417909078605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 217581561042956895515085893 40796542695554417909078605)
        ·
          refine ⟨15298703510832906715904477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40796542695554417909078605 15298703510832906715904477)
          ·
            refine ⟨5737013816562340018464179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15298703510832906715904477 5737013816562340018464179)
            ·
              refine ⟨8605520724843510027696269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5737013816562340018464179 8605520724843510027696269)
              ·
                refine ⟨3227070271816316260386101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8605520724843510027696269 3227070271816316260386101)
                ·
                  refine ⟨302537837982779649411197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3227070271816316260386101 302537837982779649411197)
                  ·
                    rfl

theorem cell23_5302713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 3, 5].length) (baseStart_5302713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5302713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5302713 prefixEnd_5302713 := by exact prefixLift 5302713
  have htrace : WordTrace (prefixWord ++ tailWord_5302713) baseStart_5302713 baseEnd_5302713 := by
    simpa [prefixWord, tailWord_5302713, baseEnd_5302713] using wordTrace_append hprefix tailTrace_5302713
  have hstable : (prefixWord ++ tailWord_5302713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5302713).length < 2 ^ (prefixWord ++ tailWord_5302713).sum := by decide
  have hdescent : baseEnd_5302713 < baseStart_5302713 := by decide
  rcases family_descends (prefixWord ++ tailWord_5302713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5302729 : List Nat := [1, 2, 1, 1, 2, 1, 5, 1, 4, 1, 4]
def baseStart_5302729 : Nat := 118140960795 + 5302729 * 2 ^ 59
def prefixEnd_5302729 : Nat := 4983230072969 + 3 ^ 40 * 5302729 * 2
def baseEnd_5302729 : Nat := 2722848757535488782100699

theorem tailTrace_5302729 : CollatzResearch.WordTrace tailWord_5302729 prefixEnd_5302729 2722848757535488782100699 := by
  unfold tailWord_5302729
  simp only [CollatzResearch.WordTrace]
  refine ⟨193406415606125941857103241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128937610404083961238068827 193406415606125941857103241)
  ·
    refine ⟨145054811704594456392827431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193406415606125941857103241 145054811704594456392827431)
    ·
      refine ⟨217582217556891684589241147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145054811704594456392827431 217582217556891684589241147)
      ·
        refine ⟨326373326335337526883861721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217582217556891684589241147 326373326335337526883861721)
        ·
          refine ⟨244779994751503145162896291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 326373326335337526883861721 244779994751503145162896291)
          ·
            refine ⟨367169992127254717744344437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 244779994751503145162896291 367169992127254717744344437)
            ·
              refine ⟨34422186761930129788532291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 367169992127254717744344437 34422186761930129788532291)
              ·
                refine ⟨51633280142895194682798437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34422186761930129788532291 51633280142895194682798437)
                ·
                  refine ⟨9681240026792849003024707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51633280142895194682798437 9681240026792849003024707)
                  ·
                    refine ⟨14521860040189273504537061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9681240026792849003024707 14521860040189273504537061)
                    ·
                      refine ⟨2722848757535488782100699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14521860040189273504537061 2722848757535488782100699)
                      ·
                        rfl

theorem cell23_5302729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 4, 1, 4].length) (baseStart_5302729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5302729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5302729 prefixEnd_5302729 := by exact prefixLift 5302729
  have htrace : WordTrace (prefixWord ++ tailWord_5302729) baseStart_5302729 baseEnd_5302729 := by
    simpa [prefixWord, tailWord_5302729, baseEnd_5302729] using wordTrace_append hprefix tailTrace_5302729
  have hstable : (prefixWord ++ tailWord_5302729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5302729).length < 2 ^ (prefixWord ++ tailWord_5302729).sum := by decide
  have hdescent : baseEnd_5302729 < baseStart_5302729 := by decide
  rcases family_descends (prefixWord ++ tailWord_5302729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5302746 : List Nat := [3, 1, 1, 2, 3, 1, 2, 1, 1, 6, 2]
def baseStart_5302746 : Nat := 118140960795 + 5302746 * 2 ^ 59
def prefixEnd_5302746 : Nat := 4983230072969 + 3 ^ 40 * 5302746 * 2
def baseEnd_5302746 : Nat := 2722857486706615215588121

theorem tailTrace_5302746 : CollatzResearch.WordTrace tailWord_5302746 prefixEnd_5302746 2722857486706615215588121 := by
  unfold tailWord_5302746
  simp only [CollatzResearch.WordTrace]
  refine ⟨48351758911766088440118023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128938023764709569173648061 48351758911766088440118023)
  ·
    refine ⟨72527638367649132660177035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48351758911766088440118023 72527638367649132660177035)
    ·
      refine ⟨108791457551473698990265553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72527638367649132660177035 108791457551473698990265553)
      ·
        refine ⟨81593593163605274242699165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108791457551473698990265553 81593593163605274242699165)
        ·
          refine ⟨30597597436351977841012187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81593593163605274242699165 30597597436351977841012187)
          ·
            refine ⟨45896396154527966761518281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30597597436351977841012187 45896396154527966761518281)
            ·
              refine ⟨34422297115895975071138711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45896396154527966761518281 34422297115895975071138711)
              ·
                refine ⟨51633445673843962606708067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34422297115895975071138711 51633445673843962606708067)
                ·
                  refine ⟨77450168510765943910062101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51633445673843962606708067 77450168510765943910062101)
                  ·
                    refine ⟨3630476648942153620784161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 77450168510765943910062101 3630476648942153620784161)
                    ·
                      refine ⟨2722857486706615215588121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3630476648942153620784161 2722857486706615215588121)
                      ·
                        rfl

theorem cell23_5302746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 1, 6, 2].length) (baseStart_5302746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5302746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5302746 prefixEnd_5302746 := by exact prefixLift 5302746
  have htrace : WordTrace (prefixWord ++ tailWord_5302746) baseStart_5302746 baseEnd_5302746 := by
    simpa [prefixWord, tailWord_5302746, baseEnd_5302746] using wordTrace_append hprefix tailTrace_5302746
  have hstable : (prefixWord ++ tailWord_5302746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5302746).length < 2 ^ (prefixWord ++ tailWord_5302746).sum := by decide
  have hdescent : baseEnd_5302746 < baseStart_5302746 := by decide
  rcases family_descends (prefixWord ++ tailWord_5302746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5302797 : List Nat := [1, 7, 1, 1, 1, 2, 1, 1, 2, 4, 2]
def baseStart_5302797 : Nat := 118140960795 + 5302797 * 2 ^ 59
def prefixEnd_5302797 : Nat := 4983230072969 + 3 ^ 40 * 5302797 * 2
def baseEnd_5302797 : Nat := 2722883674219994516050387

theorem tailTrace_5302797 : CollatzResearch.WordTrace tailWord_5302797 prefixEnd_5302797 2722883674219994516050387 := by
  unfold tailWord_5302797
  simp only [CollatzResearch.WordTrace]
  refine ⟨193408895769879589470578645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128939263846586392980385763 193408895769879589470578645)
  ·
    refine ⟨4533020994606552878216687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 193408895769879589470578645 4533020994606552878216687)
    ·
      refine ⟨6799531491909829317325031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4533020994606552878216687 6799531491909829317325031)
      ·
        refine ⟨10199297237864743975987547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6799531491909829317325031 10199297237864743975987547)
        ·
          refine ⟨15298945856797115963981321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10199297237864743975987547 15298945856797115963981321)
          ·
            refine ⟨11474209392597836972985991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15298945856797115963981321 11474209392597836972985991)
            ·
              refine ⟨17211314088896755459478987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11474209392597836972985991 17211314088896755459478987)
              ·
                refine ⟨25816971133345133189218481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17211314088896755459478987 25816971133345133189218481)
                ·
                  refine ⟨19362728350008849891913861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25816971133345133189218481 19362728350008849891913861)
                  ·
                    refine ⟨3630511565626659354733849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19362728350008849891913861 3630511565626659354733849)
                    ·
                      refine ⟨2722883674219994516050387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3630511565626659354733849 2722883674219994516050387)
                      ·
                        rfl

theorem cell23_5302797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_5302797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5302797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5302797 prefixEnd_5302797 := by exact prefixLift 5302797
  have htrace : WordTrace (prefixWord ++ tailWord_5302797) baseStart_5302797 baseEnd_5302797 := by
    simpa [prefixWord, tailWord_5302797, baseEnd_5302797] using wordTrace_append hprefix tailTrace_5302797
  have hstable : (prefixWord ++ tailWord_5302797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5302797).length < 2 ^ (prefixWord ++ tailWord_5302797).sum := by decide
  have hdescent : baseEnd_5302797 < baseStart_5302797 := by decide
  rcases family_descends (prefixWord ++ tailWord_5302797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5302799 : List Nat := [1, 1, 2, 1, 1, 1, 2, 6, 3, 5]
def baseStart_5302799 : Nat := 118140960795 + 5302799 * 2 ^ 59
def prefixEnd_5302799 : Nat := 4983230072969 + 3 ^ 40 * 5302799 * 2
def baseEnd_5302799 : Nat := 907628233727101169408459

theorem tailTrace_5302799 : CollatzResearch.WordTrace tailWord_5302799 prefixEnd_5302799 907628233727101169408459 := by
  unfold tailWord_5302799
  simp only [CollatzResearch.WordTrace]
  refine ⟨193408968715872343812151451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128939312477248229208100967 193408968715872343812151451)
  ·
    refine ⟨290113453073808515718227177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193408968715872343812151451 290113453073808515718227177)
    ·
      refine ⟨217585089805356386788670383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 290113453073808515718227177 217585089805356386788670383)
      ·
        refine ⟨326377634708034580183005575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217585089805356386788670383 326377634708034580183005575)
        ·
          refine ⟨489566452062051870274508363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 326377634708034580183005575 489566452062051870274508363)
          ·
            refine ⟨734349678093077805411762545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 489566452062051870274508363 734349678093077805411762545)
            ·
              refine ⟨550762258569808354058821909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 734349678093077805411762545 550762258569808354058821909)
              ·
                refine ⟨25816980870459766596507277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 550762258569808354058821909 25816980870459766596507277)
                ·
                  refine ⟨9681367826422412473690229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25816980870459766596507277 9681367826422412473690229)
                  ·
                    refine ⟨907628233727101169408459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9681367826422412473690229 907628233727101169408459)
                    ·
                      rfl

theorem cell23_5302799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 6, 3, 5].length) (baseStart_5302799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5302799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5302799 prefixEnd_5302799 := by exact prefixLift 5302799
  have htrace : WordTrace (prefixWord ++ tailWord_5302799) baseStart_5302799 baseEnd_5302799 := by
    simpa [prefixWord, tailWord_5302799, baseEnd_5302799] using wordTrace_append hprefix tailTrace_5302799
  have hstable : (prefixWord ++ tailWord_5302799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5302799).length < 2 ^ (prefixWord ++ tailWord_5302799).sum := by decide
  have hdescent : baseEnd_5302799 < baseStart_5302799 := by decide
  rcases family_descends (prefixWord ++ tailWord_5302799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5302813 : List Nat := [1, 4, 2, 2, 1, 2, 1, 1, 5, 1, 3]
def baseStart_5302813 : Nat := 118140960795 + 5302813 * 2 ^ 59
def prefixEnd_5302813 : Nat := 4983230072969 + 3 ^ 40 * 5302813 * 2
def baseEnd_5302813 : Nat := 2722891889910466453450313

theorem tailTrace_5302813 : CollatzResearch.WordTrace tailWord_5302813 prefixEnd_5302813 2722891889910466453450313 := by
  unfold tailWord_5302813
  simp only [CollatzResearch.WordTrace]
  refine ⟨193409479337821624203161093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128939652891881082802107395 193409479337821624203161093)
  ·
    refine ⟨36264277375841554538092705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 193409479337821624203161093 36264277375841554538092705)
    ·
      refine ⟨27198208031881165903569529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36264277375841554538092705 27198208031881165903569529)
      ·
        refine ⟨20398656023910874427677147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27198208031881165903569529 20398656023910874427677147)
        ·
          refine ⟨30597984035866311641515721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20398656023910874427677147 30597984035866311641515721)
          ·
            refine ⟨22948488026899733731136791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30597984035866311641515721 22948488026899733731136791)
            ·
              refine ⟨34422732040349600596705187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22948488026899733731136791 34422732040349600596705187)
              ·
                refine ⟨51634098060524400895057781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34422732040349600596705187 51634098060524400895057781)
                ·
                  refine ⟨4840696693174162583911667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51634098060524400895057781 4840696693174162583911667)
                  ·
                    refine ⟨7261045039761243875867501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4840696693174162583911667 7261045039761243875867501)
                    ·
                      refine ⟨2722891889910466453450313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7261045039761243875867501 2722891889910466453450313)
                      ·
                        rfl

theorem cell23_5302813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 5, 1, 3].length) (baseStart_5302813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5302813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5302813 prefixEnd_5302813 := by exact prefixLift 5302813
  have htrace : WordTrace (prefixWord ++ tailWord_5302813) baseStart_5302813 baseEnd_5302813 := by
    simpa [prefixWord, tailWord_5302813, baseEnd_5302813] using wordTrace_append hprefix tailTrace_5302813
  have hstable : (prefixWord ++ tailWord_5302813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5302813).length < 2 ^ (prefixWord ++ tailWord_5302813).sum := by decide
  have hdescent : baseEnd_5302813 < baseStart_5302813 := by decide
  rcases family_descends (prefixWord ++ tailWord_5302813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5302833 : List Nat := [1, 2, 2, 3, 1, 1, 6, 1, 1, 5]
def baseStart_5302833 : Nat := 118140960795 + 5302833 * 2 ^ 59
def prefixEnd_5302833 : Nat := 4983230072969 + 3 ^ 40 * 5302833 * 2
def baseEnd_5302833 : Nat := 907634053174518791733407

theorem tailTrace_5302833 : CollatzResearch.WordTrace tailWord_5302833 prefixEnd_5302833 907634053174518791733407 := by
  unfold tailWord_5302833
  simp only [CollatzResearch.WordTrace]
  refine ⟨193410208797749167618889153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128940139198499445079259435 193410208797749167618889153)
  ·
    refine ⟨145057656598311875714166865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193410208797749167618889153 145057656598311875714166865)
    ·
      refine ⟨108793242448733906785625149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145057656598311875714166865 108793242448733906785625149)
      ·
        refine ⟨40797465918275215044609431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108793242448733906785625149 40797465918275215044609431)
        ·
          refine ⟨61196198877412822566914147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40797465918275215044609431 61196198877412822566914147)
          ·
            refine ⟨91794298316119233850371221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61196198877412822566914147 91794298316119233850371221)
            ·
              refine ⟨4302857733568089086736151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 91794298316119233850371221 4302857733568089086736151)
              ·
                refine ⟨6454286600352133630104227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4302857733568089086736151 6454286600352133630104227)
                ·
                  refine ⟨9681429900528200445156341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6454286600352133630104227 9681429900528200445156341)
                  ·
                    refine ⟨907634053174518791733407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9681429900528200445156341 907634053174518791733407)
                    ·
                      rfl

theorem cell23_5302833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 6, 1, 1, 5].length) (baseStart_5302833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5302833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5302833 prefixEnd_5302833 := by exact prefixLift 5302833
  have htrace : WordTrace (prefixWord ++ tailWord_5302833) baseStart_5302833 baseEnd_5302833 := by
    simpa [prefixWord, tailWord_5302833, baseEnd_5302833] using wordTrace_append hprefix tailTrace_5302833
  have hstable : (prefixWord ++ tailWord_5302833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5302833).length < 2 ^ (prefixWord ++ tailWord_5302833).sum := by decide
  have hdescent : baseEnd_5302833 < baseStart_5302833 := by decide
  rcases family_descends (prefixWord ++ tailWord_5302833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5302856 : List Nat := [2, 1, 3, 1, 1, 1, 1, 3, 5, 2, 3]
def baseStart_5302856 : Nat := 118140960795 + 5302856 * 2 ^ 59
def prefixEnd_5302856 : Nat := 4983230072969 + 3 ^ 40 * 5302856 * 2
def baseEnd_5302856 : Nat := 2722913969578609785212615

theorem tailTrace_5302856 : CollatzResearch.WordTrace tailWord_5302856 prefixEnd_5302856 2722913969578609785212615 := by
  unfold tailWord_5302856
  simp only [CollatzResearch.WordTrace]
  refine ⟨96705523838332921273488211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128940698451110561697984281 96705523838332921273488211)
  ·
    refine ⟨145058285757499381910232317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96705523838332921273488211 145058285757499381910232317)
    ·
      refine ⟨54396857159062268216337119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145058285757499381910232317 54396857159062268216337119)
      ·
        refine ⟨81595285738593402324505679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54396857159062268216337119 81595285738593402324505679)
        ·
          refine ⟨122392928607890103486758519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81595285738593402324505679 122392928607890103486758519)
          ·
            refine ⟨183589392911835155230137779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122392928607890103486758519 183589392911835155230137779)
            ·
              refine ⟨275384089367752732845206669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 183589392911835155230137779 275384089367752732845206669)
              ·
                refine ⟨103269033512907274816952501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 275384089367752732845206669 103269033512907274816952501)
                ·
                  refine ⟨9681471891835057014089297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 103269033512907274816952501 9681471891835057014089297)
                  ·
                    refine ⟨7261103918876292760566973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9681471891835057014089297 7261103918876292760566973)
                    ·
                      refine ⟨2722913969578609785212615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7261103918876292760566973 2722913969578609785212615)
                      ·
                        rfl

theorem cell23_5302856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 5, 2, 3].length) (baseStart_5302856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5302856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5302856 prefixEnd_5302856 := by exact prefixLift 5302856
  have htrace : WordTrace (prefixWord ++ tailWord_5302856) baseStart_5302856 baseEnd_5302856 := by
    simpa [prefixWord, tailWord_5302856, baseEnd_5302856] using wordTrace_append hprefix tailTrace_5302856
  have hstable : (prefixWord ++ tailWord_5302856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5302856).length < 2 ^ (prefixWord ++ tailWord_5302856).sum := by decide
  have hdescent : baseEnd_5302856 < baseStart_5302856 := by decide
  rcases family_descends (prefixWord ++ tailWord_5302856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5302866 : List Nat := [3, 2, 2, 1, 2, 1, 3, 1, 1, 1, 6]
def baseStart_5302866 : Nat := 118140960795 + 5302866 * 2 ^ 59
def prefixEnd_5302866 : Nat := 4983230072969 + 3 ^ 40 * 5302866 * 2
def baseEnd_5302866 : Nat := 2722919104385154746087569

theorem tailTrace_5302866 : CollatzResearch.WordTrace tailWord_5302866 prefixEnd_5302866 2722919104385154746087569 := by
  unfold tailWord_5302866
  simp only [CollatzResearch.WordTrace]
  refine ⟨48352853101657403563710113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128940941604419742836560301 48352853101657403563710113)
  ·
    refine ⟨36264639826243052672782585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48352853101657403563710113 36264639826243052672782585)
    ·
      refine ⟨27198479869682289504586939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36264639826243052672782585 27198479869682289504586939)
      ·
        refine ⟨40797719804523434256880409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27198479869682289504586939 40797719804523434256880409)
        ·
          refine ⟨30598289853392575692660307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40797719804523434256880409 30598289853392575692660307)
          ·
            refine ⟨45897434780088863538990461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30598289853392575692660307 45897434780088863538990461)
            ·
              refine ⟨17211538042533323827121423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45897434780088863538990461 17211538042533323827121423)
              ·
                refine ⟨25817307063799985740682135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17211538042533323827121423 25817307063799985740682135)
                ·
                  refine ⟨38725960595699978611023203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25817307063799985740682135 38725960595699978611023203)
                  ·
                    refine ⟨58088940893549967916534805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38725960595699978611023203 58088940893549967916534805)
                    ·
                      refine ⟨2722919104385154746087569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58088940893549967916534805 2722919104385154746087569)
                      ·
                        rfl

theorem cell23_5302866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_5302866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5302866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5302866 prefixEnd_5302866 := by exact prefixLift 5302866
  have htrace : WordTrace (prefixWord ++ tailWord_5302866) baseStart_5302866 baseEnd_5302866 := by
    simpa [prefixWord, tailWord_5302866, baseEnd_5302866] using wordTrace_append hprefix tailTrace_5302866
  have hstable : (prefixWord ++ tailWord_5302866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5302866).length < 2 ^ (prefixWord ++ tailWord_5302866).sum := by decide
  have hdescent : baseEnd_5302866 < baseStart_5302866 := by decide
  rcases family_descends (prefixWord ++ tailWord_5302866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5302879 : List Nat := [1, 1, 2, 3, 1, 1, 1, 2, 1, 4, 6]
def baseStart_5302879 : Nat := 118140960795 + 5302879 * 2 ^ 59
def prefixEnd_5302879 : Nat := 4983230072969 + 3 ^ 40 * 5302879 * 2
def baseEnd_5302879 : Nat := 2722925779633663195225009

theorem tailTrace_5302879 : CollatzResearch.WordTrace tailWord_5302879 prefixEnd_5302879 2722925779633663195225009 := by
  unfold tailWord_5302879
  simp only [CollatzResearch.WordTrace]
  refine ⟨193411886555582517475063691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128941257703721678316709127 193411886555582517475063691)
  ·
    refine ⟨290117829833373776212595537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193411886555582517475063691 290117829833373776212595537)
    ·
      refine ⟨217588372375030332159446653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 290117829833373776212595537 217588372375030332159446653)
      ·
        refine ⟨81595639640636374559792495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 217588372375030332159446653 81595639640636374559792495)
        ·
          refine ⟨122393459460954561839688743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81595639640636374559792495 122393459460954561839688743)
          ·
            refine ⟨183590189191431842759533115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122393459460954561839688743 183590189191431842759533115)
            ·
              refine ⟨275385283787147764139299673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 183590189191431842759533115 275385283787147764139299673)
              ·
                refine ⟨206538962840360823104474755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 275385283787147764139299673 206538962840360823104474755)
                ·
                  refine ⟨309808444260541234656712133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 206538962840360823104474755 309808444260541234656712133)
                  ·
                    refine ⟨58089083298851481498133525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 309808444260541234656712133 58089083298851481498133525)
                    ·
                      refine ⟨2722925779633663195225009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58089083298851481498133525 2722925779633663195225009)
                      ·
                        rfl

theorem cell23_5302879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 4, 6].length) (baseStart_5302879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5302879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5302879 prefixEnd_5302879 := by exact prefixLift 5302879
  have htrace : WordTrace (prefixWord ++ tailWord_5302879) baseStart_5302879 baseEnd_5302879 := by
    simpa [prefixWord, tailWord_5302879, baseEnd_5302879] using wordTrace_append hprefix tailTrace_5302879
  have hstable : (prefixWord ++ tailWord_5302879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5302879).length < 2 ^ (prefixWord ++ tailWord_5302879).sum := by decide
  have hdescent : baseEnd_5302879 < baseStart_5302879 := by decide
  rcases family_descends (prefixWord ++ tailWord_5302879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5302889 : List Nat := [1, 2, 1, 1, 1, 4, 1, 2, 1, 9]
def baseStart_5302889 : Nat := 118140960795 + 5302889 * 2 ^ 59
def prefixEnd_5302889 : Nat := 4983230072969 + 3 ^ 40 * 5302889 * 2
def baseEnd_5302889 : Nat := 907643638146736052033321

theorem tailTrace_5302889 : CollatzResearch.WordTrace tailWord_5302889 prefixEnd_5302889 907643638146736052033321 := by
  unfold tailWord_5302889
  simp only [CollatzResearch.WordTrace]
  refine ⟨193412251285546289182927721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128941500857030859455285147 193412251285546289182927721)
  ·
    refine ⟨145059188464159716887195791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193412251285546289182927721 145059188464159716887195791)
    ·
      refine ⟨217588782696239575330793687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145059188464159716887195791 217588782696239575330793687)
      ·
        refine ⟨326383174044359362996190531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217588782696239575330793687 326383174044359362996190531)
        ·
          refine ⟨489574761066539044494285797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 326383174044359362996190531 489574761066539044494285797)
          ·
            refine ⟨91795267699976070842678587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 489574761066539044494285797 91795267699976070842678587)
            ·
              refine ⟨137692901549964106264017881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91795267699976070842678587 137692901549964106264017881)
              ·
                refine ⟨103269676162473079698013411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 137692901549964106264017881 103269676162473079698013411)
                ·
                  refine ⟨154904514243709619547020117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 103269676162473079698013411 154904514243709619547020117)
                  ·
                    refine ⟨907643638146736052033321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 154904514243709619547020117 907643638146736052033321)
                    ·
                      rfl

theorem cell23_5302889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 9].length) (baseStart_5302889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5302889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5302889 prefixEnd_5302889 := by exact prefixLift 5302889
  have htrace : WordTrace (prefixWord ++ tailWord_5302889) baseStart_5302889 baseEnd_5302889 := by
    simpa [prefixWord, tailWord_5302889, baseEnd_5302889] using wordTrace_append hprefix tailTrace_5302889
  have hstable : (prefixWord ++ tailWord_5302889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5302889).length < 2 ^ (prefixWord ++ tailWord_5302889).sum := by decide
  have hdescent : baseEnd_5302889 < baseStart_5302889 := by decide
  rcases family_descends (prefixWord ++ tailWord_5302889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5302903 : List Nat := [1, 1, 3, 1, 1, 3, 4, 1, 4, 1, 3]
def baseStart_5302903 : Nat := 118140960795 + 5302903 * 2 ^ 59
def prefixEnd_5302903 : Nat := 4983230072969 + 3 ^ 40 * 5302903 * 2
def baseEnd_5302903 : Nat := 2722938103169371101324899

theorem tailTrace_5302903 : CollatzResearch.WordTrace tailWord_5302903 prefixEnd_5302903 2722938103169371101324899 := by
  unfold tailWord_5302903
  simp only [CollatzResearch.WordTrace]
  refine ⟨193412761907495569573937363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128941841271663713049291575 193412761907495569573937363)
  ·
    refine ⟨290119142861243354360906045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193412761907495569573937363 290119142861243354360906045)
    ·
      refine ⟨108794678572966257885339767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 290119142861243354360906045 108794678572966257885339767)
      ·
        refine ⟨163192017859449386828009651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108794678572966257885339767 163192017859449386828009651)
        ·
          refine ⟨244788026789174080242014477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163192017859449386828009651 244788026789174080242014477)
          ·
            refine ⟨91795510045940280090755429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 244788026789174080242014477 91795510045940280090755429)
            ·
              refine ⟨17211658133613802517016643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91795510045940280090755429 17211658133613802517016643)
              ·
                refine ⟨25817487200420703775524965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17211658133613802517016643 25817487200420703775524965)
                ·
                  refine ⟨4840778850078881957910931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25817487200420703775524965 4840778850078881957910931)
                  ·
                    refine ⟨7261168275118322936866397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4840778850078881957910931 7261168275118322936866397)
                    ·
                      refine ⟨2722938103169371101324899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7261168275118322936866397 2722938103169371101324899)
                      ·
                        rfl

theorem cell23_5302903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 1, 4, 1, 3].length) (baseStart_5302903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5302903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5302903 prefixEnd_5302903 := by exact prefixLift 5302903
  have htrace : WordTrace (prefixWord ++ tailWord_5302903) baseStart_5302903 baseEnd_5302903 := by
    simpa [prefixWord, tailWord_5302903, baseEnd_5302903] using wordTrace_append hprefix tailTrace_5302903
  have hstable : (prefixWord ++ tailWord_5302903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5302903).length < 2 ^ (prefixWord ++ tailWord_5302903).sum := by decide
  have hdescent : baseEnd_5302903 < baseStart_5302903 := by decide
  rcases family_descends (prefixWord ++ tailWord_5302903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5302973 : List Nat := [1, 4, 1, 2, 1, 4, 1, 1, 2, 2, 4]
def baseStart_5302973 : Nat := 118140960795 + 5302973 * 2 ^ 59
def prefixEnd_5302973 : Nat := 4983230072969 + 3 ^ 40 * 5302973 * 2
def baseEnd_5302973 : Nat := 2722974046815185827449577

theorem tailTrace_5302973 : CollatzResearch.WordTrace tailWord_5302973 prefixEnd_5302973 2722974046815185827449577 := by
  unfold tailWord_5302973
  simp only [CollatzResearch.WordTrace]
  refine ⟨193415315017241971528985573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128943543344827981019323715 193415315017241971528985573)
  ·
    refine ⟨36265371565732869661684795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 193415315017241971528985573 36265371565732869661684795)
    ·
      refine ⟨54398057348599304492527193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36265371565732869661684795 54398057348599304492527193)
      ·
        refine ⟨40798543011449478369395395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54398057348599304492527193 40798543011449478369395395)
        ·
          refine ⟨61197814517174217554093093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40798543011449478369395395 61197814517174217554093093)
          ·
            refine ⟨11474590221970165791392455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61197814517174217554093093 11474590221970165791392455)
            ·
              refine ⟨17211885332955248687088683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11474590221970165791392455 17211885332955248687088683)
              ·
                refine ⟨25817827999432873030633025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17211885332955248687088683 25817827999432873030633025)
                ·
                  refine ⟨19363370999574654772974769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25817827999432873030633025 19363370999574654772974769)
                  ·
                    refine ⟨14522528249680991079731077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19363370999574654772974769 14522528249680991079731077)
                    ·
                      refine ⟨2722974046815185827449577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14522528249680991079731077 2722974046815185827449577)
                      ·
                        rfl

theorem cell23_5302973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 1, 2, 2, 4].length) (baseStart_5302973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5302973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5302973 prefixEnd_5302973 := by exact prefixLift 5302973
  have htrace : WordTrace (prefixWord ++ tailWord_5302973) baseStart_5302973 baseEnd_5302973 := by
    simpa [prefixWord, tailWord_5302973, baseEnd_5302973] using wordTrace_append hprefix tailTrace_5302973
  have hstable : (prefixWord ++ tailWord_5302973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5302973).length < 2 ^ (prefixWord ++ tailWord_5302973).sum := by decide
  have hdescent : baseEnd_5302973 < baseStart_5302973 := by decide
  rcases family_descends (prefixWord ++ tailWord_5302973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5303000 : List Nat := [2, 1, 2, 2, 3, 3, 2, 3, 5]
def baseStart_5303000 : Nat := 118140960795 + 5303000 * 2 ^ 59
def prefixEnd_5303000 : Nat := 4983230072969 + 3 ^ 40 * 5303000 * 2
def baseEnd_5303000 : Nat := 302554212310317469090217

theorem tailTrace_5303000 : CollatzResearch.WordTrace tailWord_5303000 prefixEnd_5303000 302554212310317469090217 := by
  unfold tailWord_5303000
  simp only [CollatzResearch.WordTrace]
  refine ⟨96708149894072077570109227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128944199858762770093478969 96708149894072077570109227)
  ·
    refine ⟨145062224841108116355163841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96708149894072077570109227 145062224841108116355163841)
    ·
      refine ⟨108796668630831087266372881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145062224841108116355163841 108796668630831087266372881)
      ·
        refine ⟨81597501473123315449779661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108796668630831087266372881 81597501473123315449779661)
        ·
          refine ⟨30599063052421243293667373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81597501473123315449779661 30599063052421243293667373)
          ·
            refine ⟨11474648644657966235125265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30599063052421243293667373 11474648644657966235125265)
            ·
              refine ⟨8605986483493474676343949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11474648644657966235125265 8605986483493474676343949)
              ·
                refine ⟨3227244931310053003628981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8605986483493474676343949 3227244931310053003628981)
                ·
                  refine ⟨302554212310317469090217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3227244931310053003628981 302554212310317469090217)
                  ·
                    rfl

theorem cell23_5303000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 3, 5].length) (baseStart_5303000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5303000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5303000 prefixEnd_5303000 := by exact prefixLift 5303000
  have htrace : WordTrace (prefixWord ++ tailWord_5303000) baseStart_5303000 baseEnd_5303000 := by
    simpa [prefixWord, tailWord_5303000, baseEnd_5303000] using wordTrace_append hprefix tailTrace_5303000
  have hstable : (prefixWord ++ tailWord_5303000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5303000).length < 2 ^ (prefixWord ++ tailWord_5303000).sum := by decide
  have hdescent : baseEnd_5303000 < baseStart_5303000 := by decide
  rcases family_descends (prefixWord ++ tailWord_5303000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5303028 : List Nat := [2, 6, 1, 1, 3, 1, 1, 1, 1, 4, 2]
def baseStart_5303028 : Nat := 118140960795 + 5303028 * 2 ^ 59
def prefixEnd_5303028 : Nat := 4983230072969 + 3 ^ 40 * 5303028 * 2
def baseEnd_5303028 : Nat := 2723002288251183112261825

theorem tailTrace_5303028 : CollatzResearch.WordTrace tailWord_5303028 prefixEnd_5303028 2723002288251183112261825 := by
  unfold tailWord_5303028
  simp only [CollatzResearch.WordTrace]
  refine ⟨96708660516021357961118869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128944880688028477281491825 96708660516021357961118869)
  ·
    refine ⟨4533218461688501154427447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 96708660516021357961118869 4533218461688501154427447)
    ·
      refine ⟨6799827692532751731641171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4533218461688501154427447 6799827692532751731641171)
      ·
        refine ⟨10199741538799127597461757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6799827692532751731641171 10199741538799127597461757)
        ·
          refine ⟨3824903077049672849048159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10199741538799127597461757 3824903077049672849048159)
          ·
            refine ⟨5737354615574509273572239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3824903077049672849048159 5737354615574509273572239)
            ·
              refine ⟨8606031923361763910358359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5737354615574509273572239 8606031923361763910358359)
              ·
                refine ⟨12909047885042645865537539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8606031923361763910358359 12909047885042645865537539)
                ·
                  refine ⟨19363571827563968798306309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12909047885042645865537539 19363571827563968798306309)
                  ·
                    refine ⟨3630669717668244149682433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19363571827563968798306309 3630669717668244149682433)
                    ·
                      refine ⟨2723002288251183112261825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3630669717668244149682433 2723002288251183112261825)
                      ·
                        rfl

theorem cell23_5303028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_5303028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5303028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5303028 prefixEnd_5303028 := by exact prefixLift 5303028
  have htrace : WordTrace (prefixWord ++ tailWord_5303028) baseStart_5303028 baseEnd_5303028 := by
    simpa [prefixWord, tailWord_5303028, baseEnd_5303028] using wordTrace_append hprefix tailTrace_5303028
  have hstable : (prefixWord ++ tailWord_5303028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5303028).length < 2 ^ (prefixWord ++ tailWord_5303028).sum := by decide
  have hdescent : baseEnd_5303028 < baseStart_5303028 := by decide
  rcases family_descends (prefixWord ++ tailWord_5303028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5303073 : List Nat := [1, 2, 3, 2, 1, 2, 2, 4, 6]
def baseStart_5303073 : Nat := 118140960795 + 5303073 * 2 ^ 59
def prefixEnd_5303073 : Nat := 4983230072969 + 3 ^ 40 * 5303073 * 2
def baseEnd_5303073 : Nat := 302558377208959492911013

theorem tailTrace_5303073 : CollatzResearch.WordTrace tailWord_5303073 prefixEnd_5303073 302558377208959492911013 := by
  unfold tailWord_5303073
  simp only [CollatzResearch.WordTrace]
  refine ⟨193418962316879688607625873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128945974877919792405083915 193418962316879688607625873)
  ·
    refine ⟨145064221737659766455719405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193418962316879688607625873 145064221737659766455719405)
    ·
      refine ⟨54399083151622412420894777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145064221737659766455719405 54399083151622412420894777)
      ·
        refine ⟨40799312363716809315671083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54399083151622412420894777 40799312363716809315671083)
        ·
          refine ⟨61198968545575213973506625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40799312363716809315671083 61198968545575213973506625)
          ·
            refine ⟨45899226409181410480129969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61198968545575213973506625 45899226409181410480129969)
            ·
              refine ⟨34424419806886057860097477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45899226409181410480129969 34424419806886057860097477)
              ·
                refine ⟨6454578713791135848768277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34424419806886057860097477 6454578713791135848768277)
                ·
                  refine ⟨302558377208959492911013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6454578713791135848768277 302558377208959492911013)
                  ·
                    rfl

theorem cell23_5303073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 4, 6].length) (baseStart_5303073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5303073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5303073 prefixEnd_5303073 := by exact prefixLift 5303073
  have htrace : WordTrace (prefixWord ++ tailWord_5303073) baseStart_5303073 baseEnd_5303073 := by
    simpa [prefixWord, tailWord_5303073, baseEnd_5303073] using wordTrace_append hprefix tailTrace_5303073
  have hstable : (prefixWord ++ tailWord_5303073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5303073).length < 2 ^ (prefixWord ++ tailWord_5303073).sum := by decide
  have hdescent : baseEnd_5303073 < baseStart_5303073 := by decide
  rcases family_descends (prefixWord ++ tailWord_5303073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5303100 : List Nat := [2, 2, 2, 2, 1, 1, 1, 3, 5, 1, 3]
def baseStart_5303100 : Nat := 118140960795 + 5303100 * 2 ^ 59
def prefixEnd_5303100 : Nat := 4983230072969 + 3 ^ 40 * 5303100 * 2
def baseEnd_5303100 : Nat := 2723039258858306830561493

theorem tailTrace_5303100 : CollatzResearch.WordTrace tailWord_5303100 prefixEnd_5303100 2723039258858306830561493 := by
  unfold tailWord_5303100
  simp only [CollatzResearch.WordTrace]
  refine ⟨96709973543890936109429377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128946631391854581479239169 96709973543890936109429377)
  ·
    refine ⟨72532480157918202082072033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96709973543890936109429377 72532480157918202082072033)
    ·
      refine ⟨54399360118438651561554025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72532480157918202082072033 54399360118438651561554025)
      ·
        refine ⟨40799520088828988671165519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54399360118438651561554025 40799520088828988671165519)
        ·
          refine ⟨61199280133243483006748279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40799520088828988671165519 61199280133243483006748279)
          ·
            refine ⟨91798920199865224510122419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61199280133243483006748279 91798920199865224510122419)
            ·
              refine ⟨137698380299797836765183629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91798920199865224510122419 137698380299797836765183629)
              ·
                refine ⟨51636892612424188786943861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 137698380299797836765183629 51636892612424188786943861)
                ·
                  refine ⟨4840958682414767698775987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51636892612424188786943861 4840958682414767698775987)
                  ·
                    refine ⟨7261438023622151548163981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4840958682414767698775987 7261438023622151548163981)
                    ·
                      refine ⟨2723039258858306830561493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7261438023622151548163981 2723039258858306830561493)
                      ·
                        rfl

theorem cell23_5303100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 5, 1, 3].length) (baseStart_5303100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5303100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5303100 prefixEnd_5303100 := by exact prefixLift 5303100
  have htrace : WordTrace (prefixWord ++ tailWord_5303100) baseStart_5303100 baseEnd_5303100 := by
    simpa [prefixWord, tailWord_5303100, baseEnd_5303100] using wordTrace_append hprefix tailTrace_5303100
  have hstable : (prefixWord ++ tailWord_5303100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5303100).length < 2 ^ (prefixWord ++ tailWord_5303100).sum := by decide
  have hdescent : baseEnd_5303100 < baseStart_5303100 := by decide
  rcases family_descends (prefixWord ++ tailWord_5303100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5303127 : List Nat := [1, 1, 3, 2, 4, 1, 2, 2, 2, 3, 2]
def baseStart_5303127 : Nat := 118140960795 + 5303127 * 2 ^ 59
def prefixEnd_5303127 : Nat := 4983230072969 + 3 ^ 40 * 5303127 * 2
def baseEnd_5303127 : Nat := 2723053122835978224923869

theorem tailTrace_5303127 : CollatzResearch.WordTrace tailWord_5303127 prefixEnd_5303127 2723053122835978224923869 := by
  unfold tailWord_5303127
  simp only [CollatzResearch.WordTrace]
  refine ⟨193420931858684055830091635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128947287905789370553394423 193420931858684055830091635)
  ·
    refine ⟨290131397788026083745137453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193420931858684055830091635 290131397788026083745137453)
    ·
      refine ⟨108799274170509781404426545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 290131397788026083745137453 108799274170509781404426545)
      ·
        refine ⟨81599455627882336053319909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108799274170509781404426545 81599455627882336053319909)
        ·
          refine ⟨15299897930227938009997483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81599455627882336053319909 15299897930227938009997483)
          ·
            refine ⟨22949846895341907014996225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15299897930227938009997483 22949846895341907014996225)
            ·
              refine ⟨17212385171506430261247169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22949846895341907014996225 17212385171506430261247169)
              ·
                refine ⟨12909288878629822695935377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17212385171506430261247169 12909288878629822695935377)
                ·
                  refine ⟨9681966658972367021951533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12909288878629822695935377 9681966658972367021951533)
                  ·
                    refine ⟨3630737497114637633231825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9681966658972367021951533 3630737497114637633231825)
                    ·
                      refine ⟨2723053122835978224923869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3630737497114637633231825 2723053122835978224923869)
                      ·
                        rfl

theorem cell23_5303127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 2, 2, 3, 2].length) (baseStart_5303127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5303127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5303127 prefixEnd_5303127 := by exact prefixLift 5303127
  have htrace : WordTrace (prefixWord ++ tailWord_5303127) baseStart_5303127 baseEnd_5303127 := by
    simpa [prefixWord, tailWord_5303127, baseEnd_5303127] using wordTrace_append hprefix tailTrace_5303127
  have hstable : (prefixWord ++ tailWord_5303127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5303127).length < 2 ^ (prefixWord ++ tailWord_5303127).sum := by decide
  have hdescent : baseEnd_5303127 < baseStart_5303127 := by decide
  rcases family_descends (prefixWord ++ tailWord_5303127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5303140 : List Nat := [2, 3, 1, 1, 4, 1, 1, 2, 3, 1, 4]
def baseStart_5303140 : Nat := 118140960795 + 5303140 * 2 ^ 59
def prefixEnd_5303140 : Nat := 4983230072969 + 3 ^ 40 * 5303140 * 2
def baseEnd_5303140 : Nat := 2723059798084486674061309

theorem tailTrace_5303140 : CollatzResearch.WordTrace tailWord_5303140 prefixEnd_5303140 2723059798084486674061309 := by
  unfold tailWord_5303140
  simp only [CollatzResearch.WordTrace]
  refine ⟨96710703003818479525157437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128947604005091306033543249 96710703003818479525157437)
  ·
    refine ⟨36266513626431929821934039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96710703003818479525157437 36266513626431929821934039)
    ·
      refine ⟨54399770439647894732901059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36266513626431929821934039 54399770439647894732901059)
      ·
        refine ⟨81599655659471842099351589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54399770439647894732901059 81599655659471842099351589)
        ·
          refine ⟨15299935436150970393628423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81599655659471842099351589 15299935436150970393628423)
          ·
            refine ⟨22949903154226455590442635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15299935436150970393628423 22949903154226455590442635)
            ·
              refine ⟨34424854731339683385663953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22949903154226455590442635 34424854731339683385663953)
              ·
                refine ⟨25818641048504762539247965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34424854731339683385663953 25818641048504762539247965)
                ·
                  refine ⟨9681990393189285952217987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25818641048504762539247965 9681990393189285952217987)
                  ·
                    refine ⟨14522985589783928928326981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9681990393189285952217987 14522985589783928928326981)
                    ·
                      refine ⟨2723059798084486674061309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14522985589783928928326981 2723059798084486674061309)
                      ·
                        rfl

theorem cell23_5303140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 2, 3, 1, 4].length) (baseStart_5303140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5303140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5303140 prefixEnd_5303140 := by exact prefixLift 5303140
  have htrace : WordTrace (prefixWord ++ tailWord_5303140) baseStart_5303140 baseEnd_5303140 := by
    simpa [prefixWord, tailWord_5303140, baseEnd_5303140] using wordTrace_append hprefix tailTrace_5303140
  have hstable : (prefixWord ++ tailWord_5303140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5303140).length < 2 ^ (prefixWord ++ tailWord_5303140).sum := by decide
  have hdescent : baseEnd_5303140 < baseStart_5303140 := by decide
  rcases family_descends (prefixWord ++ tailWord_5303140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5303177 : List Nat := [1, 2, 1, 1, 5, 3, 1, 3, 1, 2, 3]
def baseStart_5303177 : Nat := 118140960795 + 5303177 * 2 ^ 59
def prefixEnd_5303177 : Nat := 4983230072969 + 3 ^ 40 * 5303177 * 2
def baseEnd_5303177 : Nat := 2723078796868703029298639

theorem tailTrace_5303177 : CollatzResearch.WordTrace tailWord_5303177 prefixEnd_5303177 2723078796868703029298639 := by
  unfold tailWord_5303177
  simp only [CollatzResearch.WordTrace]
  refine ⟨193422755508502914369411785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128948503672335276246274523 193422755508502914369411785)
  ·
    refine ⟨145067066631377185777058839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193422755508502914369411785 145067066631377185777058839)
    ·
      refine ⟨217600599947065778665588259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145067066631377185777058839 217600599947065778665588259)
      ·
        refine ⟨326400899920598667998382389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217600599947065778665588259 326400899920598667998382389)
        ·
          refine ⟨30600084367556125124848349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 326400899920598667998382389 30600084367556125124848349)
          ·
            refine ⟨11475031637833546921818131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30600084367556125124848349 11475031637833546921818131)
            ·
              refine ⟨17212547456750320382727197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11475031637833546921818131 17212547456750320382727197)
              ·
                refine ⟨6454705296281370143522699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17212547456750320382727197 6454705296281370143522699)
                ·
                  refine ⟨9682057944422055215284049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6454705296281370143522699 9682057944422055215284049)
                  ·
                    refine ⟨7261543458316541411463037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9682057944422055215284049 7261543458316541411463037)
                    ·
                      refine ⟨2723078796868703029298639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7261543458316541411463037 2723078796868703029298639)
                      ·
                        rfl

theorem cell23_5303177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 3, 1, 2, 3].length) (baseStart_5303177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5303177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5303177 prefixEnd_5303177 := by exact prefixLift 5303177
  have htrace : WordTrace (prefixWord ++ tailWord_5303177) baseStart_5303177 baseEnd_5303177 := by
    simpa [prefixWord, tailWord_5303177, baseEnd_5303177] using wordTrace_append hprefix tailTrace_5303177
  have hstable : (prefixWord ++ tailWord_5303177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5303177).length < 2 ^ (prefixWord ++ tailWord_5303177).sum := by decide
  have hdescent : baseEnd_5303177 < baseStart_5303177 := by decide
  rcases family_descends (prefixWord ++ tailWord_5303177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5303223 : List Nat := [1, 1, 3, 1, 3, 1, 2, 2, 1, 8]
def baseStart_5303223 : Nat := 118140960795 + 5303223 * 2 ^ 59
def prefixEnd_5303223 : Nat := 4983230072969 + 3 ^ 40 * 5303223 * 2
def baseEnd_5303223 : Nat := 907700805659603283107809

theorem tailTrace_5303223 : CollatzResearch.WordTrace tailWord_5303223 prefixEnd_5303223 907700805659603283107809 := by
  unfold tailWord_5303223
  simp only [CollatzResearch.WordTrace]
  refine ⟨193424433266336264225586323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128949622177557509483724215 193424433266336264225586323)
  ·
    refine ⟨290136649899504396338379485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193424433266336264225586323 290136649899504396338379485)
    ·
      refine ⟨108801243712314148626892307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 290136649899504396338379485 108801243712314148626892307)
      ·
        refine ⟨163201865568471222940338461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108801243712314148626892307 163201865568471222940338461)
        ·
          refine ⟨61200699588176708602626923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 163201865568471222940338461 61200699588176708602626923)
          ·
            refine ⟨91801049382265062903940385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61200699588176708602626923 91801049382265062903940385)
            ·
              refine ⟨68850787036698797177955289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91801049382265062903940385 68850787036698797177955289)
              ·
                refine ⟨51638090277524097883466467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68850787036698797177955289 51638090277524097883466467)
                ·
                  refine ⟨77457135416286146825199701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51638090277524097883466467 77457135416286146825199701)
                  ·
                    refine ⟨907700805659603283107809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 77457135416286146825199701 907700805659603283107809)
                    ·
                      rfl

theorem cell23_5303223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 8].length) (baseStart_5303223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5303223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5303223 prefixEnd_5303223 := by exact prefixLift 5303223
  have htrace : WordTrace (prefixWord ++ tailWord_5303223) baseStart_5303223 baseEnd_5303223 := by
    simpa [prefixWord, tailWord_5303223, baseEnd_5303223] using wordTrace_append hprefix tailTrace_5303223
  have hstable : (prefixWord ++ tailWord_5303223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5303223).length < 2 ^ (prefixWord ++ tailWord_5303223).sum := by decide
  have hdescent : baseEnd_5303223 < baseStart_5303223 := by decide
  rcases family_descends (prefixWord ++ tailWord_5303223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5303273 : List Nat := [1, 2, 1, 1, 1, 2, 1, 1, 4, 1, 8]
def baseStart_5303273 : Nat := 118140960795 + 5303273 * 2 ^ 59
def prefixEnd_5303273 : Nat := 4983230072969 + 3 ^ 40 * 5303273 * 2
def baseEnd_5303273 : Nat := 2723128091011534653698197

theorem tailTrace_5303273 : CollatzResearch.WordTrace tailWord_5303273 prefixEnd_5303273 2723128091011534653698197 := by
  unfold tailWord_5303273
  simp only [CollatzResearch.WordTrace]
  refine ⟨193426256916155122764906473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128950837944103415176604315 193426256916155122764906473)
  ·
    refine ⟨145069692687116342073679855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193426256916155122764906473 145069692687116342073679855)
    ·
      refine ⟨217604539030674513110519783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145069692687116342073679855 217604539030674513110519783)
      ·
        refine ⟨326406808546011769665779675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217604539030674513110519783 326406808546011769665779675)
        ·
          refine ⟨489610212819017654498669513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 326406808546011769665779675 489610212819017654498669513)
          ·
            refine ⟨367207659614263240874002135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 489610212819017654498669513 367207659614263240874002135)
            ·
              refine ⟨550811489421394861311003203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 367207659614263240874002135 550811489421394861311003203)
              ·
                refine ⟨826217234132092291966504805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 550811489421394861311003203 826217234132092291966504805)
                ·
                  refine ⟨154915731399767304743719651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 826217234132092291966504805 154915731399767304743719651)
                  ·
                    refine ⟨232373597099650957115579477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 154915731399767304743719651 232373597099650957115579477)
                    ·
                      refine ⟨2723128091011534653698197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 232373597099650957115579477 2723128091011534653698197)
                      ·
                        rfl

theorem cell23_5303273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 1, 8].length) (baseStart_5303273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5303273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5303273 prefixEnd_5303273 := by exact prefixLift 5303273
  have htrace : WordTrace (prefixWord ++ tailWord_5303273) baseStart_5303273 baseEnd_5303273 := by
    simpa [prefixWord, tailWord_5303273, baseEnd_5303273] using wordTrace_append hprefix tailTrace_5303273
  have hstable : (prefixWord ++ tailWord_5303273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5303273).length < 2 ^ (prefixWord ++ tailWord_5303273).sum := by decide
  have hdescent : baseEnd_5303273 < baseStart_5303273 := by decide
  rcases family_descends (prefixWord ++ tailWord_5303273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5303280 : List Nat := [2, 1, 1, 1, 3, 2, 1, 2, 4, 3, 3]
def baseStart_5303280 : Nat := 118140960795 + 5303280 * 2 ^ 59
def prefixEnd_5303280 : Nat := 4983230072969 + 3 ^ 40 * 5303280 * 2
def baseEnd_5303280 : Nat := 2723131685376116126310665

theorem tailTrace_5303280 : CollatzResearch.WordTrace tailWord_5303280 prefixEnd_5303280 2723131685376116126310665 := by
  unfold tailWord_5303280
  simp only [CollatzResearch.WordTrace]
  refine ⟨96713256113564881480205647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128951008151419841973607529 96713256113564881480205647)
  ·
    refine ⟨145069884170347322220308471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96713256113564881480205647 145069884170347322220308471)
    ·
      refine ⟨217604826255520983330462707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145069884170347322220308471 217604826255520983330462707)
      ·
        refine ⟨326407239383281474995694061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217604826255520983330462707 326407239383281474995694061)
        ·
          refine ⟨122402714768730553123385273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 326407239383281474995694061 122402714768730553123385273)
          ·
            refine ⟨91802036076547914842538955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122402714768730553123385273 91802036076547914842538955)
            ·
              refine ⟨137703054114821872263808433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91802036076547914842538955 137703054114821872263808433)
              ·
                refine ⟨103277290586116404197856325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 137703054114821872263808433 103277290586116404197856325)
                ·
                  refine ⟨19364491984896825787098061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 103277290586116404197856325 19364491984896825787098061)
                  ·
                    refine ⟨7261684494336309670161773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19364491984896825787098061 7261684494336309670161773)
                    ·
                      refine ⟨2723131685376116126310665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7261684494336309670161773 2723131685376116126310665)
                      ·
                        rfl

theorem cell23_5303280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 4, 3, 3].length) (baseStart_5303280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5303280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5303280 prefixEnd_5303280 := by exact prefixLift 5303280
  have htrace : WordTrace (prefixWord ++ tailWord_5303280) baseStart_5303280 baseEnd_5303280 := by
    simpa [prefixWord, tailWord_5303280, baseEnd_5303280] using wordTrace_append hprefix tailTrace_5303280
  have hstable : (prefixWord ++ tailWord_5303280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5303280).length < 2 ^ (prefixWord ++ tailWord_5303280).sum := by decide
  have hdescent : baseEnd_5303280 < baseStart_5303280 := by decide
  rcases family_descends (prefixWord ++ tailWord_5303280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5303285 : List Nat := [1, 3, 5, 2, 1, 1, 3, 1, 1, 3, 2]
def baseStart_5303285 : Nat := 118140960795 + 5303285 * 2 ^ 59
def prefixEnd_5303285 : Nat := 4983230072969 + 3 ^ 40 * 5303285 * 2
def baseEnd_5303285 : Nat := 2723134252779388606748143

theorem tailTrace_5303285 : CollatzResearch.WordTrace tailWord_5303285 prefixEnd_5303285 2723134252779388606748143 := by
  unfold tailWord_5303285
  simp only [CollatzResearch.WordTrace]
  refine ⟨193426694592111648814343309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128951129728074432542895539 193426694592111648814343309)
  ·
    refine ⟨72535010472041868305378741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 193426694592111648814343309 72535010472041868305378741)
    ·
      refine ⟨6800157231753925153629257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 72535010472041868305378741 6800157231753925153629257)
      ·
        refine ⟨5100117923815443865221943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6800157231753925153629257 5100117923815443865221943)
        ·
          refine ⟨7650176885723165797832915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5100117923815443865221943 7650176885723165797832915)
          ·
            refine ⟨11475265328584748696749373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7650176885723165797832915 11475265328584748696749373)
            ·
              refine ⟨4303224498219280761281015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11475265328584748696749373 4303224498219280761281015)
              ·
                refine ⟨6454836747328921141921523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4303224498219280761281015 6454836747328921141921523)
                ·
                  refine ⟨9682255120993381712882285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6454836747328921141921523 9682255120993381712882285)
                  ·
                    refine ⟨3630845670372518142330857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9682255120993381712882285 3630845670372518142330857)
                    ·
                      refine ⟨2723134252779388606748143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3630845670372518142330857 2723134252779388606748143)
                      ·
                        rfl

theorem cell23_5303285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_5303285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5303285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5303285 prefixEnd_5303285 := by exact prefixLift 5303285
  have htrace : WordTrace (prefixWord ++ tailWord_5303285) baseStart_5303285 baseEnd_5303285 := by
    simpa [prefixWord, tailWord_5303285, baseEnd_5303285] using wordTrace_append hprefix tailTrace_5303285
  have hstable : (prefixWord ++ tailWord_5303285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5303285).length < 2 ^ (prefixWord ++ tailWord_5303285).sum := by decide
  have hdescent : baseEnd_5303285 < baseStart_5303285 := by decide
  rcases family_descends (prefixWord ++ tailWord_5303285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5303304 : List Nat := [2, 1, 3, 2, 1, 3, 4, 2, 5]
def baseStart_5303304 : Nat := 118140960795 + 5303304 * 2 ^ 59
def prefixEnd_5303304 : Nat := 4983230072969 + 3 ^ 40 * 5303304 * 2
def baseEnd_5303304 : Nat := 302571556545758225823395

theorem tailTrace_5303304 : CollatzResearch.WordTrace tailWord_5303304 prefixEnd_5303304 302571556545758225823395 := by
  unfold tailWord_5303304
  simp only [CollatzResearch.WordTrace]
  refine ⟨96713693789521407529642483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128951591719361876706189977 96713693789521407529642483)
  ·
    refine ⟨145070540684282111294463725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96713693789521407529642483 145070540684282111294463725)
    ·
      refine ⟨54401452756605791735423897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145070540684282111294463725 54401452756605791735423897)
      ·
        refine ⟨40801089567454343801567923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54401452756605791735423897 40801089567454343801567923)
        ·
          refine ⟨61201634351181515702351885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40801089567454343801567923 61201634351181515702351885)
          ·
            refine ⟨22950612881693068388381957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61201634351181515702351885 22950612881693068388381957)
            ·
              refine ⟨4303239915317450322821617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22950612881693068388381957 4303239915317450322821617)
              ·
                refine ⟨3227429936488087742116213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4303239915317450322821617 3227429936488087742116213)
                ·
                  refine ⟨302571556545758225823395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3227429936488087742116213 302571556545758225823395)
                  ·
                    rfl

theorem cell23_5303304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 4, 2, 5].length) (baseStart_5303304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5303304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5303304 prefixEnd_5303304 := by exact prefixLift 5303304
  have htrace : WordTrace (prefixWord ++ tailWord_5303304) baseStart_5303304 baseEnd_5303304 := by
    simpa [prefixWord, tailWord_5303304, baseEnd_5303304] using wordTrace_append hprefix tailTrace_5303304
  have hstable : (prefixWord ++ tailWord_5303304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5303304).length < 2 ^ (prefixWord ++ tailWord_5303304).sum := by decide
  have hdescent : baseEnd_5303304 < baseStart_5303304 := by decide
  rcases family_descends (prefixWord ++ tailWord_5303304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5303307 : List Nat := [1, 1, 1, 1, 6, 2, 1, 1, 2, 5, 2]
def baseStart_5303307 : Nat := 118140960795 + 5303307 * 2 ^ 59
def prefixEnd_5303307 : Nat := 4983230072969 + 3 ^ 40 * 5303307 * 2
def baseEnd_5303307 : Nat := 2723145549353787520673041

theorem tailTrace_5303307 : CollatzResearch.WordTrace tailWord_5303307 prefixEnd_5303307 2723145549353787520673041 := by
  unfold tailWord_5303307
  simp only [CollatzResearch.WordTrace]
  refine ⟨193427496998031946571644175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128951664665354631047762783 193427496998031946571644175)
  ·
    refine ⟨290141245497047919857466263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193427496998031946571644175 290141245497047919857466263)
    ·
      refine ⟨435211868245571879786199395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290141245497047919857466263 435211868245571879786199395)
      ·
        refine ⟨652817802368357819679299093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 435211868245571879786199395 652817802368357819679299093)
        ·
          refine ⟨30600834486016772797467145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 652817802368357819679299093 30600834486016772797467145)
          ·
            refine ⟨22950625864512579598100359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30600834486016772797467145 22950625864512579598100359)
            ·
              refine ⟨34425938796768869397150539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22950625864512579598100359 34425938796768869397150539)
              ·
                refine ⟨51638908195153304095725809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34425938796768869397150539 51638908195153304095725809)
                ·
                  refine ⟨38729181146364978071794357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51638908195153304095725809 38729181146364978071794357)
                  ·
                    refine ⟨3630860732471716694230721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38729181146364978071794357 3630860732471716694230721)
                    ·
                      refine ⟨2723145549353787520673041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3630860732471716694230721 2723145549353787520673041)
                      ·
                        rfl

theorem cell23_5303307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 2, 5, 2].length) (baseStart_5303307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5303307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5303307 prefixEnd_5303307 := by exact prefixLift 5303307
  have htrace : WordTrace (prefixWord ++ tailWord_5303307) baseStart_5303307 baseEnd_5303307 := by
    simpa [prefixWord, tailWord_5303307, baseEnd_5303307] using wordTrace_append hprefix tailTrace_5303307
  have hstable : (prefixWord ++ tailWord_5303307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5303307).length < 2 ^ (prefixWord ++ tailWord_5303307).sum := by decide
  have hdescent : baseEnd_5303307 < baseStart_5303307 := by decide
  rcases family_descends (prefixWord ++ tailWord_5303307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5303360 : List Nat := [2, 1, 1, 2, 2, 3, 3, 1, 8]
def baseStart_5303360 : Nat := 118140960795 + 5303360 * 2 ^ 59
def prefixEnd_5303360 : Nat := 4983230072969 + 3 ^ 40 * 5303360 * 2
def baseEnd_5303360 : Nat := 302574751536497312590033

theorem tailTrace_5303360 : CollatzResearch.WordTrace tailWord_5303360 prefixEnd_5303360 302574751536497312590033 := by
  unfold tailWord_5303360
  simp only [CollatzResearch.WordTrace]
  refine ⟨96714715033419968311661767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128952953377893291082215689 96714715033419968311661767)
  ·
    refine ⟨145072072550129952467492651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96714715033419968311661767 145072072550129952467492651)
    ·
      refine ⟨217608108825194928701238977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145072072550129952467492651 217608108825194928701238977)
      ·
        refine ⟨163206081618896196525929233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 217608108825194928701238977 163206081618896196525929233)
        ·
          refine ⟨122404561214172147394446925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163206081618896196525929233 122404561214172147394446925)
          ·
            refine ⟨45901710455314555272917597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 122404561214172147394446925 45901710455314555272917597)
            ·
              refine ⟨17213141420742958227344099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45901710455314555272917597 17213141420742958227344099)
              ·
                refine ⟨25819712131114437341016149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17213141420742958227344099 25819712131114437341016149)
                ·
                  refine ⟨302574751536497312590033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25819712131114437341016149 302574751536497312590033)
                  ·
                    rfl

theorem cell23_5303360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 1, 8].length) (baseStart_5303360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5303360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5303360 prefixEnd_5303360 := by exact prefixLift 5303360
  have htrace : WordTrace (prefixWord ++ tailWord_5303360) baseStart_5303360 baseEnd_5303360 := by
    simpa [prefixWord, tailWord_5303360, baseEnd_5303360] using wordTrace_append hprefix tailTrace_5303360
  have hstable : (prefixWord ++ tailWord_5303360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5303360).length < 2 ^ (prefixWord ++ tailWord_5303360).sum := by decide
  have hdescent : baseEnd_5303360 < baseStart_5303360 := by decide
  rcases family_descends (prefixWord ++ tailWord_5303360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5303407 : List Nat := [1, 1, 2, 1, 3, 3, 1, 5, 1, 5]
def baseStart_5303407 : Nat := 118140960795 + 5303407 * 2 ^ 59
def prefixEnd_5303407 : Nat := 4983230072969 + 3 ^ 40 * 5303407 * 2
def baseEnd_5303407 : Nat := 907732299139745709807527

theorem tailTrace_5303407 : CollatzResearch.WordTrace tailWord_5303407 prefixEnd_5303407 907732299139745709807527 := by
  unfold tailWord_5303407
  simp only [CollatzResearch.WordTrace]
  refine ⟨193431144297669663650284475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128954096198446442433522983 193431144297669663650284475)
  ·
    refine ⟨290146716446504495475426713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193431144297669663650284475 290146716446504495475426713)
    ·
      refine ⟨217610037334878371606570035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 290146716446504495475426713 217610037334878371606570035)
      ·
        refine ⟨326415056002317557409855053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217610037334878371606570035 326415056002317557409855053)
        ·
          refine ⟨122405646000869084028695645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 326415056002317557409855053 122405646000869084028695645)
          ·
            refine ⟨45902117250325906510760867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 122405646000869084028695645 45902117250325906510760867)
            ·
              refine ⟨68853175875488859766141301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45902117250325906510760867 68853175875488859766141301)
              ·
                refine ⟨6454985238327080603075747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 68853175875488859766141301 6454985238327080603075747)
                ·
                  refine ⟨9682477857490620904613621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6454985238327080603075747 9682477857490620904613621)
                  ·
                    refine ⟨907732299139745709807527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9682477857490620904613621 907732299139745709807527)
                    ·
                      rfl

theorem cell23_5303407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 5, 1, 5].length) (baseStart_5303407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5303407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5303407 prefixEnd_5303407 := by exact prefixLift 5303407
  have htrace : WordTrace (prefixWord ++ tailWord_5303407) baseStart_5303407 baseEnd_5303407 := by
    simpa [prefixWord, tailWord_5303407, baseEnd_5303407] using wordTrace_append hprefix tailTrace_5303407
  have hstable : (prefixWord ++ tailWord_5303407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5303407).length < 2 ^ (prefixWord ++ tailWord_5303407).sum := by decide
  have hdescent : baseEnd_5303407 < baseStart_5303407 := by decide
  rcases family_descends (prefixWord ++ tailWord_5303407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5303427 : List Nat := [1, 1, 1, 3, 3, 2, 2, 2, 3, 1, 4]
def baseStart_5303427 : Nat := 118140960795 + 5303427 * 2 ^ 59
def prefixEnd_5303427 : Nat := 4983230072969 + 3 ^ 40 * 5303427 * 2
def baseEnd_5303427 : Nat := 2723207167032327051172489

theorem tailTrace_5303427 : CollatzResearch.WordTrace tailWord_5303427 prefixEnd_5303427 2723207167032327051172489 := by
  unfold tailWord_5303427
  simp only [CollatzResearch.WordTrace]
  refine ⟨193431873757597207066012535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128954582505064804710675023 193431873757597207066012535)
  ·
    refine ⟨290147810636395810599018803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193431873757597207066012535 290147810636395810599018803)
    ·
      refine ⟨435221715954593715898528205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290147810636395810599018803 435221715954593715898528205)
      ·
        refine ⟨163208143482972643461948077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 435221715954593715898528205 163208143482972643461948077)
        ·
          refine ⟨61203053806114741298230529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 163208143482972643461948077 61203053806114741298230529)
          ·
            refine ⟨45902290354586055973672897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61203053806114741298230529 45902290354586055973672897)
            ·
              refine ⟨34426717765939541980254673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45902290354586055973672897 34426717765939541980254673)
              ·
                refine ⟨25820038324454656485191005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34426717765939541980254673 25820038324454656485191005)
                ·
                  refine ⟨9682514371670496181946627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25820038324454656485191005 9682514371670496181946627)
                  ·
                    refine ⟨14523771557505744272919941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9682514371670496181946627 14523771557505744272919941)
                    ·
                      refine ⟨2723207167032327051172489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14523771557505744272919941 2723207167032327051172489)
                      ·
                        rfl

theorem cell23_5303427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 2, 3, 1, 4].length) (baseStart_5303427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5303427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5303427 prefixEnd_5303427 := by exact prefixLift 5303427
  have htrace : WordTrace (prefixWord ++ tailWord_5303427) baseStart_5303427 baseEnd_5303427 := by
    simpa [prefixWord, tailWord_5303427, baseEnd_5303427] using wordTrace_append hprefix tailTrace_5303427
  have hstable : (prefixWord ++ tailWord_5303427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5303427).length < 2 ^ (prefixWord ++ tailWord_5303427).sum := by decide
  have hdescent : baseEnd_5303427 < baseStart_5303427 := by decide
  rcases family_descends (prefixWord ++ tailWord_5303427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5303454 : List Nat := [4, 3, 1, 1, 2, 1, 1, 1, 3, 6]
def baseStart_5303454 : Nat := 118140960795 + 5303454 * 2 ^ 59
def prefixEnd_5303454 : Nat := 4983230072969 + 3 ^ 40 * 5303454 * 2
def baseEnd_5303454 : Nat := 907740343669999481844955

theorem tailTrace_5303454 : CollatzResearch.WordTrace tailWord_5303454 prefixEnd_5303454 907740343669999481844955 := by
  unfold tailWord_5303454
  simp only [CollatzResearch.WordTrace]
  refine ⟨24179107316062423834655677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128955239018999593784830277 24179107316062423834655677)
  ·
    refine ⟨9067165243523408937995879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24179107316062423834655677 9067165243523408937995879)
    ·
      refine ⟨13600747865285113406993819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9067165243523408937995879 13600747865285113406993819)
      ·
        refine ⟨20401121797927670110490729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13600747865285113406993819 20401121797927670110490729)
        ·
          refine ⟨15300841348445752582868047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20401121797927670110490729 15300841348445752582868047)
          ·
            refine ⟨22951262022668628874302071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15300841348445752582868047 22951262022668628874302071)
            ·
              refine ⟨34426893034002943311453107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22951262022668628874302071 34426893034002943311453107)
              ·
                refine ⟨51640339551004414967179661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34426893034002943311453107 51640339551004414967179661)
                ·
                  refine ⟨19365127331626655612692373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51640339551004414967179661 19365127331626655612692373)
                  ·
                    refine ⟨907740343669999481844955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19365127331626655612692373 907740343669999481844955)
                    ·
                      rfl

theorem cell23_5303454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_5303454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5303454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5303454 prefixEnd_5303454 := by exact prefixLift 5303454
  have htrace : WordTrace (prefixWord ++ tailWord_5303454) baseStart_5303454 baseEnd_5303454 := by
    simpa [prefixWord, tailWord_5303454, baseEnd_5303454] using wordTrace_append hprefix tailTrace_5303454
  have hstable : (prefixWord ++ tailWord_5303454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5303454).length < 2 ^ (prefixWord ++ tailWord_5303454).sum := by decide
  have hdescent : baseEnd_5303454 < baseStart_5303454 := by decide
  rcases family_descends (prefixWord ++ tailWord_5303454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5303458 : List Nat := [3, 3, 1, 3, 2, 1, 3, 1, 1, 5]
def baseStart_5303458 : Nat := 118140960795 + 5303458 * 2 ^ 59
def prefixEnd_5303458 : Nat := 4983230072969 + 3 ^ 40 * 5303458 * 2
def baseEnd_5303458 : Nat := 907741028310872143294949

theorem tailTrace_5303458 : CollatzResearch.WordTrace tailWord_5303458 prefixEnd_5303458 907741028310872143294949 := by
  unfold tailWord_5303458
  simp only [CollatzResearch.WordTrace]
  refine ⟨48358251105121224840097757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128955336280323266240260685 48358251105121224840097757)
  ·
    refine ⟨18134344164420459315036659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48358251105121224840097757 18134344164420459315036659)
    ·
      refine ⟨27201516246630688972554989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18134344164420459315036659 27201516246630688972554989)
      ·
        refine ⟨10200568592486508364708121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27201516246630688972554989 10200568592486508364708121)
        ·
          refine ⟨7650426444364881273531091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10200568592486508364708121 7650426444364881273531091)
          ·
            refine ⟨11475639666547321910296637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7650426444364881273531091 11475639666547321910296637)
            ·
              refine ⟨4303364874955245716361239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11475639666547321910296637 4303364874955245716361239)
              ·
                refine ⟨6455047312432868574541859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4303364874955245716361239 6455047312432868574541859)
                ·
                  refine ⟨9682570968649302861812789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6455047312432868574541859 9682570968649302861812789)
                  ·
                    refine ⟨907741028310872143294949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9682570968649302861812789 907741028310872143294949)
                    ·
                      rfl

theorem cell23_5303458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 3, 1, 1, 5].length) (baseStart_5303458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5303458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5303458 prefixEnd_5303458 := by exact prefixLift 5303458
  have htrace : WordTrace (prefixWord ++ tailWord_5303458) baseStart_5303458 baseEnd_5303458 := by
    simpa [prefixWord, tailWord_5303458, baseEnd_5303458] using wordTrace_append hprefix tailTrace_5303458
  have hstable : (prefixWord ++ tailWord_5303458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5303458).length < 2 ^ (prefixWord ++ tailWord_5303458).sum := by decide
  have hdescent : baseEnd_5303458 < baseStart_5303458 := by decide
  rcases family_descends (prefixWord ++ tailWord_5303458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5303461 : List Nat := [1, 3, 1, 2, 1, 5, 3, 1, 1, 1, 4]
def baseStart_5303461 : Nat := 118140960795 + 5303461 * 2 ^ 59
def prefixEnd_5303461 : Nat := 4983230072969 + 3 ^ 40 * 5303461 * 2
def baseEnd_5303461 : Nat := 2723224625374579918147333

theorem tailTrace_5303461 : CollatzResearch.WordTrace tailWord_5303461 prefixEnd_5303461 2723224625374579918147333 := by
  unfold tailWord_5303461
  simp only [CollatzResearch.WordTrace]
  refine ⟨193433113839474030872750237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128955409226316020581833491 193433113839474030872750237)
  ·
    refine ⟨72537417689802761577281339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 193433113839474030872750237 72537417689802761577281339)
    ·
      refine ⟨108806126534704142365922009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72537417689802761577281339 108806126534704142365922009)
      ·
        refine ⟨81604594901028106774441507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108806126534704142365922009 81604594901028106774441507)
        ·
          refine ⟨122406892351542160161662261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81604594901028106774441507 122406892351542160161662261)
          ·
            refine ⟨11475646157957077515155837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 122406892351542160161662261 11475646157957077515155837)
            ·
              refine ⟨4303367309233904068183439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11475646157957077515155837 4303367309233904068183439)
              ·
                refine ⟨6455050963850856102275159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4303367309233904068183439 6455050963850856102275159)
                ·
                  refine ⟨9682576445776284153412739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6455050963850856102275159 9682576445776284153412739)
                  ·
                    refine ⟨14523864668664426230119109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9682576445776284153412739 14523864668664426230119109)
                    ·
                      refine ⟨2723224625374579918147333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14523864668664426230119109 2723224625374579918147333)
                      ·
                        rfl

theorem cell23_5303461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 3, 1, 1, 1, 4].length) (baseStart_5303461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5303461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5303461 prefixEnd_5303461 := by exact prefixLift 5303461
  have htrace : WordTrace (prefixWord ++ tailWord_5303461) baseStart_5303461 baseEnd_5303461 := by
    simpa [prefixWord, tailWord_5303461, baseEnd_5303461] using wordTrace_append hprefix tailTrace_5303461
  have hstable : (prefixWord ++ tailWord_5303461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5303461).length < 2 ^ (prefixWord ++ tailWord_5303461).sum := by decide
  have hdescent : baseEnd_5303461 < baseStart_5303461 := by decide
  rcases family_descends (prefixWord ++ tailWord_5303461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5303484 : List Nat := [2, 2, 2, 3, 2, 3, 1, 8]
def baseStart_5303484 : Nat := 118140960795 + 5303484 * 2 ^ 59
def prefixEnd_5303484 : Nat := 4983230072969 + 3 ^ 40 * 5303484 * 2
def baseEnd_5303484 : Nat := 100860608719616049191101

theorem tailTrace_5303484 : CollatzResearch.WordTrace tailWord_5303484 prefixEnd_5303484 100860608719616049191101 := by
  unfold tailWord_5303484
  simp only [CollatzResearch.WordTrace]
  refine ⟨96716976359195352900418753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128955968478927137200558337 96716976359195352900418753)
  ·
    refine ⟨72537732269396514675314065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96716976359195352900418753 72537732269396514675314065)
    ·
      refine ⟨54403299202047386006485549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72537732269396514675314065 54403299202047386006485549)
      ·
        refine ⟨20401237200767769752432081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54403299202047386006485549 20401237200767769752432081)
        ·
          refine ⟨15300927900575827314324061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20401237200767769752432081 15300927900575827314324061)
          ·
            refine ⟨5737847962715935242871523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15300927900575827314324061 5737847962715935242871523)
            ·
              refine ⟨8606771944073902864307285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5737847962715935242871523 8606771944073902864307285)
              ·
                refine ⟨100860608719616049191101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8606771944073902864307285 100860608719616049191101)
                ·
                  rfl

theorem cell23_5303484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 8].length) (baseStart_5303484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5303484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5303484 prefixEnd_5303484 := by exact prefixLift 5303484
  have htrace : WordTrace (prefixWord ++ tailWord_5303484) baseStart_5303484 baseEnd_5303484 := by
    simpa [prefixWord, tailWord_5303484, baseEnd_5303484] using wordTrace_append hprefix tailTrace_5303484
  have hstable : (prefixWord ++ tailWord_5303484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5303484).length < 2 ^ (prefixWord ++ tailWord_5303484).sum := by decide
  have hdescent : baseEnd_5303484 < baseStart_5303484 := by decide
  rcases family_descends (prefixWord ++ tailWord_5303484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5303537 : List Nat := [1, 2, 2, 2, 2, 1, 1, 2, 4, 1, 5]
def baseStart_5303537 : Nat := 118140960795 + 5303537 * 2 ^ 59
def prefixEnd_5303537 : Nat := 4983230072969 + 3 ^ 40 * 5303537 * 2
def baseEnd_5303537 : Nat := 2723263649904321620796983

theorem tailTrace_5303537 : CollatzResearch.WordTrace tailWord_5303537 prefixEnd_5303537 2723263649904321620796983 := by
  unfold tailWord_5303537
  simp only [CollatzResearch.WordTrace]
  refine ⟨193435885787198695852516865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128957257191465797235011243 193435885787198695852516865)
  ·
    refine ⟨145076914340399021889387649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193435885787198695852516865 145076914340399021889387649)
    ·
      refine ⟨108807685755299266417040737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145076914340399021889387649 108807685755299266417040737)
      ·
        refine ⟨81605764316474449812780553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108807685755299266417040737 81605764316474449812780553)
        ·
          refine ⟨61204323237355837359585415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81605764316474449812780553 61204323237355837359585415)
          ·
            refine ⟨91806484856033756039378123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61204323237355837359585415 91806484856033756039378123)
            ·
              refine ⟨137709727284050634059067185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91806484856033756039378123 137709727284050634059067185)
              ·
                refine ⟨103282295463037975544300389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 137709727284050634059067185 103282295463037975544300389)
                ·
                  refine ⟨19365430399319620414556323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 103282295463037975544300389 19365430399319620414556323)
                  ·
                    refine ⟨29048145598979430621834485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19365430399319620414556323 29048145598979430621834485)
                    ·
                      refine ⟨2723263649904321620796983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29048145598979430621834485 2723263649904321620796983)
                      ·
                        rfl

theorem cell23_5303537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 4, 1, 5].length) (baseStart_5303537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5303537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5303537 prefixEnd_5303537 := by exact prefixLift 5303537
  have htrace : WordTrace (prefixWord ++ tailWord_5303537) baseStart_5303537 baseEnd_5303537 := by
    simpa [prefixWord, tailWord_5303537, baseEnd_5303537] using wordTrace_append hprefix tailTrace_5303537
  have hstable : (prefixWord ++ tailWord_5303537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5303537).length < 2 ^ (prefixWord ++ tailWord_5303537).sum := by decide
  have hdescent : baseEnd_5303537 < baseStart_5303537 := by decide
  rcases family_descends (prefixWord ++ tailWord_5303537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5303551 : List Nat := [1, 1, 2, 2, 1, 5, 3, 1, 1, 4, 2]
def baseStart_5303551 : Nat := 118140960795 + 5303551 * 2 ^ 59
def prefixEnd_5303551 : Nat := 4983230072969 + 3 ^ 40 * 5303551 * 2
def baseEnd_5303551 : Nat := 2723270838633484566021919

theorem tailTrace_5303551 : CollatzResearch.WordTrace tailWord_5303551 prefixEnd_5303551 2723270838633484566021919 := by
  unfold tailWord_5303551
  simp only [CollatzResearch.WordTrace]
  refine ⟨193436396409147976243526507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128957597606098650829017671 193436396409147976243526507)
  ·
    refine ⟨290154594613721964365289761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193436396409147976243526507 290154594613721964365289761)
    ·
      refine ⟨217615945960291473273967321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 290154594613721964365289761 217615945960291473273967321)
      ·
        refine ⟨163211959470218604955475491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 217615945960291473273967321 163211959470218604955475491)
        ·
          refine ⟨244817939205327907433213237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163211959470218604955475491 244817939205327907433213237)
          ·
            refine ⟨22951681800499491321863741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 244817939205327907433213237 22951681800499491321863741)
            ·
              refine ⟨8606880675187309245698903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22951681800499491321863741 8606880675187309245698903)
              ·
                refine ⟨12910321012780963868548355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8606880675187309245698903 12910321012780963868548355)
                ·
                  refine ⟨19365481519171445802822533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12910321012780963868548355 19365481519171445802822533)
                  ·
                    refine ⟨3631027784844646088029225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19365481519171445802822533 3631027784844646088029225)
                    ·
                      refine ⟨2723270838633484566021919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3631027784844646088029225 2723270838633484566021919)
                      ·
                        rfl

theorem cell23_5303551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 1, 1, 4, 2].length) (baseStart_5303551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5303551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5303551 prefixEnd_5303551 := by exact prefixLift 5303551
  have htrace : WordTrace (prefixWord ++ tailWord_5303551) baseStart_5303551 baseEnd_5303551 := by
    simpa [prefixWord, tailWord_5303551, baseEnd_5303551] using wordTrace_append hprefix tailTrace_5303551
  have hstable : (prefixWord ++ tailWord_5303551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5303551).length < 2 ^ (prefixWord ++ tailWord_5303551).sum := by decide
  have hdescent : baseEnd_5303551 < baseStart_5303551 := by decide
  rcases family_descends (prefixWord ++ tailWord_5303551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5303557 : List Nat := [1, 3, 1, 1, 2, 1, 3, 4, 7]
def baseStart_5303557 : Nat := 118140960795 + 5303557 * 2 ^ 59
def prefixEnd_5303557 : Nat := 4983230072969 + 3 ^ 40 * 5303557 * 2
def baseEnd_5303557 : Nat := 302585991057490171394099

theorem tailTrace_5303557 : CollatzResearch.WordTrace tailWord_5303557 prefixEnd_5303557 302585991057490171394099 := by
  unfold tailWord_5303557
  simp only [CollatzResearch.WordTrace]
  refine ⟨193436615247126239268244925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128957743498084159512163283 193436615247126239268244925)
  ·
    refine ⟨72538730717672339725591847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 193436615247126239268244925 72538730717672339725591847)
    ·
      refine ⟨108808096076508509588387771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72538730717672339725591847 108808096076508509588387771)
      ·
        refine ⟨163212144114762764382581657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108808096076508509588387771 163212144114762764382581657)
        ·
          refine ⟨122409108086072073286936243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163212144114762764382581657 122409108086072073286936243)
          ·
            refine ⟨183613662129108109930404365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122409108086072073286936243 183613662129108109930404365)
            ·
              refine ⟨68855123298415541223901637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 183613662129108109930404365 68855123298415541223901637)
              ·
                refine ⟨12910335618452913979481557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68855123298415541223901637 12910335618452913979481557)
                ·
                  refine ⟨302585991057490171394099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12910335618452913979481557 302585991057490171394099)
                  ·
                    rfl

theorem cell23_5303557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 4, 7].length) (baseStart_5303557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5303557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5303557 prefixEnd_5303557 := by exact prefixLift 5303557
  have htrace : WordTrace (prefixWord ++ tailWord_5303557) baseStart_5303557 baseEnd_5303557 := by
    simpa [prefixWord, tailWord_5303557, baseEnd_5303557] using wordTrace_append hprefix tailTrace_5303557
  have hstable : (prefixWord ++ tailWord_5303557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5303557).length < 2 ^ (prefixWord ++ tailWord_5303557).sum := by decide
  have hdescent : baseEnd_5303557 < baseStart_5303557 := by decide
  rcases family_descends (prefixWord ++ tailWord_5303557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5303602 : List Nat := [3, 2, 1, 1, 4, 3, 2, 1, 2, 2, 2]
def baseStart_5303602 : Nat := 118140960795 + 5303602 * 2 ^ 59
def prefixEnd_5303602 : Nat := 4983230072969 + 3 ^ 40 * 5303602 * 2
def baseEnd_5303602 : Nat := 2723297026146863866484185

theorem tailTrace_5303602 : CollatzResearch.WordTrace tailWord_5303602 prefixEnd_5303602 2723297026146863866484185 := by
  unfold tailWord_5303602
  simp only [CollatzResearch.WordTrace]
  refine ⟨48359564132990802988408265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128958837687975474635755373 48359564132990802988408265)
  ·
    refine ⟨36269673099743102241306199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48359564132990802988408265 36269673099743102241306199)
    ·
      refine ⟨54404509649614653361959299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36269673099743102241306199 54404509649614653361959299)
      ·
        refine ⟨81606764474421980042938949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54404509649614653361959299 81606764474421980042938949)
        ·
          refine ⟨15301268338954121258051053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81606764474421980042938949 15301268338954121258051053)
          ·
            refine ⟨5737975627107795471769145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15301268338954121258051053 5737975627107795471769145)
            ·
              refine ⟨4303481720330846603826859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5737975627107795471769145 4303481720330846603826859)
              ·
                refine ⟨6455222580496269905740289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4303481720330846603826859 6455222580496269905740289)
                ·
                  refine ⟨4841416935372202429305217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6455222580496269905740289 4841416935372202429305217)
                  ·
                    refine ⟨3631062701529151821978913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4841416935372202429305217 3631062701529151821978913)
                    ·
                      refine ⟨2723297026146863866484185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3631062701529151821978913 2723297026146863866484185)
                      ·
                        rfl

theorem cell23_5303602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 2, 1, 2, 2, 2].length) (baseStart_5303602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5303602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5303602 prefixEnd_5303602 := by exact prefixLift 5303602
  have htrace : WordTrace (prefixWord ++ tailWord_5303602) baseStart_5303602 baseEnd_5303602 := by
    simpa [prefixWord, tailWord_5303602, baseEnd_5303602] using wordTrace_append hprefix tailTrace_5303602
  have hstable : (prefixWord ++ tailWord_5303602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5303602).length < 2 ^ (prefixWord ++ tailWord_5303602).sum := by decide
  have hdescent : baseEnd_5303602 < baseStart_5303602 := by decide
  rcases family_descends (prefixWord ++ tailWord_5303602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5303614 : List Nat := [4, 2, 1, 2, 1, 1, 1, 2, 1, 1, 7]
def baseStart_5303614 : Nat := 118140960795 + 5303614 * 2 ^ 59
def prefixEnd_5303614 : Nat := 4983230072969 + 3 ^ 40 * 5303614 * 2
def baseEnd_5303614 : Nat := 2723303187914717819534129

theorem tailTrace_5303614 : CollatzResearch.WordTrace tailWord_5303614 prefixEnd_5303614 2723303187914717819534129 := by
  unfold tailWord_5303614
  simp only [CollatzResearch.WordTrace]
  refine ⟨24179836775989967250383737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128959129471946492002046597 24179836775989967250383737)
  ·
    refine ⟨18134877581992475437787803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24179836775989967250383737 18134877581992475437787803)
    ·
      refine ⟨27202316372988713156681705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18134877581992475437787803 27202316372988713156681705)
      ·
        refine ⟨20401737279741534867511279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27202316372988713156681705 20401737279741534867511279)
        ·
          refine ⟨30602605919612302301266919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20401737279741534867511279 30602605919612302301266919)
          ·
            refine ⟨45903908879418453451900379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30602605919612302301266919 45903908879418453451900379)
            ·
              refine ⟨68855863319127680177850569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45903908879418453451900379 68855863319127680177850569)
              ·
                refine ⟨51641897489345760133387927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68855863319127680177850569 51641897489345760133387927)
                ·
                  refine ⟨77462846234018640200081891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51641897489345760133387927 77462846234018640200081891)
                  ·
                    refine ⟨116194269351027960300122837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 77462846234018640200081891 116194269351027960300122837)
                    ·
                      refine ⟨2723303187914717819534129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 116194269351027960300122837 2723303187914717819534129)
                      ·
                        rfl

theorem cell23_5303614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_5303614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5303614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5303614 prefixEnd_5303614 := by exact prefixLift 5303614
  have htrace : WordTrace (prefixWord ++ tailWord_5303614) baseStart_5303614 baseEnd_5303614 := by
    simpa [prefixWord, tailWord_5303614, baseEnd_5303614] using wordTrace_append hprefix tailTrace_5303614
  have hstable : (prefixWord ++ tailWord_5303614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5303614).length < 2 ^ (prefixWord ++ tailWord_5303614).sum := by decide
  have hdescent : baseEnd_5303614 < baseStart_5303614 := by decide
  rcases family_descends (prefixWord ++ tailWord_5303614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5303664 : List Nat := [2, 1, 1, 1, 4, 2, 1, 5, 6]
def baseStart_5303664 : Nat := 118140960795 + 5303664 * 2 ^ 59
def prefixEnd_5303664 : Nat := 4983230072969 + 3 ^ 40 * 5303664 * 2
def baseEnd_5303664 : Nat := 302592095771938069323211

theorem tailTrace_5303664 : CollatzResearch.WordTrace tailWord_5303664 prefixEnd_5303664 302592095771938069323211 := by
  unfold tailWord_5303664
  simp only [CollatzResearch.WordTrace]
  refine ⟨96720258928869298271195023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128960345238492397694926697 96720258928869298271195023)
  ·
    refine ⟨145080388393303947406792535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96720258928869298271195023 145080388393303947406792535)
    ·
      refine ⟨217620582589955921110188803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145080388393303947406792535 217620582589955921110188803)
      ·
        refine ⟨326430873884933881665283205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217620582589955921110188803 326430873884933881665283205)
        ·
          refine ⟨61205788853425102812240601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 326430873884933881665283205 61205788853425102812240601)
          ·
            refine ⟨45904341640068827109180451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61205788853425102812240601 45904341640068827109180451)
            ·
              refine ⟨68856512460103240663770677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45904341640068827109180451 68856512460103240663770677)
              ·
                refine ⟨6455298043134678812228501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 68856512460103240663770677 6455298043134678812228501)
                ·
                  refine ⟨302592095771938069323211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6455298043134678812228501 302592095771938069323211)
                  ·
                    rfl

theorem cell23_5303664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 5, 6].length) (baseStart_5303664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5303664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5303664 prefixEnd_5303664 := by exact prefixLift 5303664
  have htrace : WordTrace (prefixWord ++ tailWord_5303664) baseStart_5303664 baseEnd_5303664 := by
    simpa [prefixWord, tailWord_5303664, baseEnd_5303664] using wordTrace_append hprefix tailTrace_5303664
  have hstable : (prefixWord ++ tailWord_5303664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5303664).length < 2 ^ (prefixWord ++ tailWord_5303664).sum := by decide
  have hdescent : baseEnd_5303664 < baseStart_5303664 := by decide
  rcases family_descends (prefixWord ++ tailWord_5303664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5303674 : List Nat := [3, 1, 1, 1, 1, 1, 2, 3, 2, 5, 3]
def baseStart_5303674 : Nat := 118140960795 + 5303674 * 2 ^ 59
def prefixEnd_5303674 : Nat := 4983230072969 + 3 ^ 40 * 5303674 * 2
def baseEnd_5303674 : Nat := 2723333996753987584783853

theorem tailTrace_5303674 : CollatzResearch.WordTrace tailWord_5303674 prefixEnd_5303674 2723333996753987584783853 := by
  unfold tailWord_5303674
  simp only [CollatzResearch.WordTrace]
  refine ⟨48360220646925592062563519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128960588391801578833502717 48360220646925592062563519)
  ·
    refine ⟨72540330970388388093845279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48360220646925592062563519 72540330970388388093845279)
    ·
      refine ⟨108810496455582582140767919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72540330970388388093845279 108810496455582582140767919)
      ·
        refine ⟨163215744683373873211151879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108810496455582582140767919 163215744683373873211151879)
        ·
          refine ⟨244823617025060809816727819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163215744683373873211151879 244823617025060809816727819)
          ·
            refine ⟨367235425537591214725091729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 244823617025060809816727819 367235425537591214725091729)
            ·
              refine ⟨275426569153193411043818797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 367235425537591214725091729 275426569153193411043818797)
              ·
                refine ⟨103284963432447529141432049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 275426569153193411043818797 103284963432447529141432049)
                ·
                  refine ⟨77463722574335646856074037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 103284963432447529141432049 77463722574335646856074037)
                  ·
                    refine ⟨7262223991343966892756941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 77463722574335646856074037 7262223991343966892756941)
                    ·
                      refine ⟨2723333996753987584783853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7262223991343966892756941 2723333996753987584783853)
                      ·
                        rfl

theorem cell23_5303674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 2, 5, 3].length) (baseStart_5303674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5303674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5303674 prefixEnd_5303674 := by exact prefixLift 5303674
  have htrace : WordTrace (prefixWord ++ tailWord_5303674) baseStart_5303674 baseEnd_5303674 := by
    simpa [prefixWord, tailWord_5303674, baseEnd_5303674] using wordTrace_append hprefix tailTrace_5303674
  have hstable : (prefixWord ++ tailWord_5303674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5303674).length < 2 ^ (prefixWord ++ tailWord_5303674).sum := by decide
  have hdescent : baseEnd_5303674 < baseStart_5303674 := by decide
  rcases family_descends (prefixWord ++ tailWord_5303674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5303691 : List Nat := [1, 1, 1, 1, 4, 3, 1, 2, 5, 1, 3]
def baseStart_5303691 : Nat := 118140960795 + 5303691 * 2 ^ 59
def prefixEnd_5303691 : Nat := 4983230072969 + 3 ^ 40 * 5303691 * 2
def baseEnd_5303691 : Nat := 2723342725925114018271275

theorem tailTrace_5303691 : CollatzResearch.WordTrace tailWord_5303691 prefixEnd_5303691 2723342725925114018271275 := by
  unfold tailWord_5303691
  simp only [CollatzResearch.WordTrace]
  refine ⟨193441502628640780153622927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128961001752427186769081951 193441502628640780153622927)
  ·
    refine ⟨290162253942961170230434391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193441502628640780153622927 290162253942961170230434391)
    ·
      refine ⟨435243380914441755345651587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290162253942961170230434391 435243380914441755345651587)
      ·
        refine ⟨652865071371662633018477381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 435243380914441755345651587 652865071371662633018477381)
        ·
          refine ⟨122412200882186743690964509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 652865071371662633018477381 122412200882186743690964509)
          ·
            refine ⟨45904575330820028884111691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 122412200882186743690964509 45904575330820028884111691)
            ·
              refine ⟨68856862996230043326167537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45904575330820028884111691 68856862996230043326167537)
              ·
                refine ⟨51642647247172532494625653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68856862996230043326167537 51642647247172532494625653)
                ·
                  refine ⟨4841498179422424921371155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51642647247172532494625653 4841498179422424921371155)
                  ·
                    refine ⟨7262247269133637382056733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4841498179422424921371155 7262247269133637382056733)
                    ·
                      refine ⟨2723342725925114018271275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7262247269133637382056733 2723342725925114018271275)
                      ·
                        rfl

theorem cell23_5303691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 5, 1, 3].length) (baseStart_5303691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5303691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5303691 prefixEnd_5303691 := by exact prefixLift 5303691
  have htrace : WordTrace (prefixWord ++ tailWord_5303691) baseStart_5303691 baseEnd_5303691 := by
    simpa [prefixWord, tailWord_5303691, baseEnd_5303691] using wordTrace_append hprefix tailTrace_5303691
  have hstable : (prefixWord ++ tailWord_5303691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5303691).length < 2 ^ (prefixWord ++ tailWord_5303691).sum := by decide
  have hdescent : baseEnd_5303691 < baseStart_5303691 := by decide
  rcases family_descends (prefixWord ++ tailWord_5303691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5303698 : List Nat := [3, 2, 3, 3, 1, 1, 1, 1, 8]
def baseStart_5303698 : Nat := 118140960795 + 5303698 * 2 ^ 59
def prefixEnd_5303698 : Nat := 4983230072969 + 3 ^ 40 * 5303698 * 2
def baseEnd_5303698 : Nat := 302594035587743943431527

theorem tailTrace_5303698 : CollatzResearch.WordTrace tailWord_5303698 prefixEnd_5303698 302594035587743943431527 := by
  unfold tailWord_5303698
  simp only [CollatzResearch.WordTrace]
  refine ⟨48360439484903855087281937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128961171959743613566085165 48360439484903855087281937)
  ·
    refine ⟨36270329613677891315461453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48360439484903855087281937 36270329613677891315461453)
    ·
      refine ⟨13601373605129209243298045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36270329613677891315461453 13601373605129209243298045)
      ·
        refine ⟨5100515101923453466236767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13601373605129209243298045 5100515101923453466236767)
        ·
          refine ⟨7650772652885180199355151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5100515101923453466236767 7650772652885180199355151)
          ·
            refine ⟨11476158979327770299032727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7650772652885180199355151 11476158979327770299032727)
            ·
              refine ⟨17214238468991655448549091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11476158979327770299032727 17214238468991655448549091)
              ·
                refine ⟨25821357703487483172823637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17214238468991655448549091 25821357703487483172823637)
                ·
                  refine ⟨302594035587743943431527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25821357703487483172823637 302594035587743943431527)
                  ·
                    rfl

theorem cell23_5303698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 1, 8].length) (baseStart_5303698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5303698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5303698 prefixEnd_5303698 := by exact prefixLift 5303698
  have htrace : WordTrace (prefixWord ++ tailWord_5303698) baseStart_5303698 baseEnd_5303698 := by
    simpa [prefixWord, tailWord_5303698, baseEnd_5303698] using wordTrace_append hprefix tailTrace_5303698
  have hstable : (prefixWord ++ tailWord_5303698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5303698).length < 2 ^ (prefixWord ++ tailWord_5303698).sum := by decide
  have hdescent : baseEnd_5303698 < baseStart_5303698 := by decide
  rcases family_descends (prefixWord ++ tailWord_5303698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
