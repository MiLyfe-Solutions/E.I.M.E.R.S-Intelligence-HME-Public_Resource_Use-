import V185TrunkScan20Chunk132

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_808221 : List Nat := [1, 4, 2, 3, 1, 2, 3, 2, 2]
def baseStart_808221 : Nat := 118140960795 + 808221 * 2 ^ 59
def prefixEnd_808221 : Nat := 4983230072969 + 3 ^ 40 * 808221 * 2
def baseEnd_808221 : Nat := 368894087162300058062725

theorem tailTrace_808221 : CollatzResearch.WordTrace tailWord_808221 prefixEnd_808221 368894087162300058062725 := by
  unfold tailWord_808221
  simp only [CollatzResearch.WordTrace]
  refine ⟨29478241604960825002528517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19652161069973883335019011 29478241604960825002528517)
  ·
    refine ⟨5527170300930154687974097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29478241604960825002528517 5527170300930154687974097)
    ·
      refine ⟨4145377725697616015980573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5527170300930154687974097 4145377725697616015980573)
      ·
        refine ⟨1554516647136606005992715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4145377725697616015980573 1554516647136606005992715)
        ·
          refine ⟨2331774970704909008989073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1554516647136606005992715 2331774970704909008989073)
          ·
            refine ⟨1748831228028681756741805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2331774970704909008989073 1748831228028681756741805)
            ·
              refine ⟨655811710510755658778177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1748831228028681756741805 655811710510755658778177)
              ·
                refine ⟨491858782883066744083633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 655811710510755658778177 491858782883066744083633)
                ·
                  refine ⟨368894087162300058062725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 491858782883066744083633 368894087162300058062725)
                  ·
                    rfl

theorem cell20_808221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 3, 2, 2].length) (baseStart_808221 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_808221 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_808221 prefixEnd_808221 := by exact prefixLift 808221
  have htrace : WordTrace (prefixWord ++ tailWord_808221) baseStart_808221 baseEnd_808221 := by
    simpa [prefixWord, tailWord_808221, baseEnd_808221] using wordTrace_append hprefix tailTrace_808221
  have hstable : (prefixWord ++ tailWord_808221).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808221).length < 2 ^ (prefixWord ++ tailWord_808221).sum := by decide
  have hdescent : baseEnd_808221 < baseStart_808221 := by decide
  rcases family_descends (prefixWord ++ tailWord_808221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808232 : List Nat := [2, 1, 5, 1, 2, 2, 2, 5]
def baseStart_808232 : Nat := 118140960795 + 808232 * 2 ^ 59
def prefixEnd_808232 : Nat := 4983230072969 + 3 ^ 40 * 808232 * 2
def baseEnd_808232 : Nat := 122966369287344302898671

theorem tailTrace_808232 : CollatzResearch.WordTrace tailWord_808232 prefixEnd_808232 122966369287344302898671 := by
  unfold tailWord_808232
  simp only [CollatzResearch.WordTrace]
  refine ⟨14739321403960486940589475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19652428538613982587452633 14739321403960486940589475)
  ·
    refine ⟨22108982105940730410884213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14739321403960486940589475 22108982105940730410884213)
    ·
      refine ⟨2072717072431943476020395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22108982105940730410884213 2072717072431943476020395)
      ·
        refine ⟨3109075608647915214030593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2072717072431943476020395 3109075608647915214030593)
        ·
          refine ⟨2331806706485936410522945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3109075608647915214030593 2331806706485936410522945)
          ·
            refine ⟨1748855029864452307892209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2331806706485936410522945 1748855029864452307892209)
            ·
              refine ⟨1311641272398339230919157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1748855029864452307892209 1311641272398339230919157)
              ·
                refine ⟨122966369287344302898671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1311641272398339230919157 122966369287344302898671)
                ·
                  rfl

theorem cell20_808232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 5].length) (baseStart_808232 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_808232 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_808232 prefixEnd_808232 := by exact prefixLift 808232
  have htrace : WordTrace (prefixWord ++ tailWord_808232) baseStart_808232 baseEnd_808232 := by
    simpa [prefixWord, tailWord_808232, baseEnd_808232] using wordTrace_append hprefix tailTrace_808232
  have hstable : (prefixWord ++ tailWord_808232).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808232).length < 2 ^ (prefixWord ++ tailWord_808232).sum := by decide
  have hdescent : baseEnd_808232 < baseStart_808232 := by decide
  rcases family_descends (prefixWord ++ tailWord_808232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808277 : List Nat := [1, 3, 2, 2, 3, 1, 1, 4, 3]
def baseStart_808277 : Nat := 118140960795 + 808277 * 2 ^ 59
def prefixEnd_808277 : Nat := 4983230072969 + 3 ^ 40 * 808277 * 2
def baseEnd_808277 : Nat := 368919647088212752195829

theorem tailTrace_808277 : CollatzResearch.WordTrace tailWord_808277 prefixEnd_808277 368919647088212752195829 := by
  unfold tailWord_808277
  simp only [CollatzResearch.WordTrace]
  refine ⟨29480284092757946566567085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19653522728505297711044723 29480284092757946566567085)
  ·
    refine ⟨11055106534784229962462657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29480284092757946566567085 11055106534784229962462657)
    ·
      refine ⟨8291329901088172471846993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11055106534784229962462657 8291329901088172471846993)
      ·
        refine ⟨6218497425816129353885245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8291329901088172471846993 6218497425816129353885245)
        ·
          refine ⟨2331936534681048507706967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6218497425816129353885245 2331936534681048507706967)
          ·
            refine ⟨3497904802021572761560451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2331936534681048507706967 3497904802021572761560451)
            ·
              refine ⟨5246857203032359142340677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3497904802021572761560451 5246857203032359142340677)
              ·
                refine ⟨983785725568567339188877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5246857203032359142340677 983785725568567339188877)
                ·
                  refine ⟨368919647088212752195829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 983785725568567339188877 368919647088212752195829)
                  ·
                    rfl

theorem cell20_808277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 4, 3].length) (baseStart_808277 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_808277 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_808277 prefixEnd_808277 := by exact prefixLift 808277
  have htrace : WordTrace (prefixWord ++ tailWord_808277) baseStart_808277 baseEnd_808277 := by
    simpa [prefixWord, tailWord_808277, baseEnd_808277] using wordTrace_append hprefix tailTrace_808277
  have hstable : (prefixWord ++ tailWord_808277).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808277).length < 2 ^ (prefixWord ++ tailWord_808277).sum := by decide
  have hdescent : baseEnd_808277 < baseStart_808277 := by decide
  rcases family_descends (prefixWord ++ tailWord_808277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808291 : List Nat := [1, 1, 1, 5, 2, 2, 3, 5]
def baseStart_808291 : Nat := 118140960795 + 808291 * 2 ^ 59
def prefixEnd_808291 : Nat := 4983230072969 + 3 ^ 40 * 808291 * 2
def baseEnd_808291 : Nat := 122975345689896975243035

theorem tailTrace_808291 : CollatzResearch.WordTrace tailWord_808291 prefixEnd_808291 122975345689896975243035 := by
  unfold tailWord_808291
  simp only [CollatzResearch.WordTrace]
  refine ⟨29480794714707226957576727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19653863143138151305051151 29480794714707226957576727)
  ·
    refine ⟨44221192072060840436365091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29480794714707226957576727 44221192072060840436365091)
    ·
      refine ⟨66331788108091260654547637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44221192072060840436365091 66331788108091260654547637)
      ·
        refine ⟨6218605135133555686363841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 66331788108091260654547637 6218605135133555686363841)
        ·
          refine ⟨4663953851350166764772881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6218605135133555686363841 4663953851350166764772881)
          ·
            refine ⟨3497965388512625073579661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4663953851350166764772881 3497965388512625073579661)
            ·
              refine ⟨1311737020692234402592373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3497965388512625073579661 1311737020692234402592373)
              ·
                refine ⟨122975345689896975243035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1311737020692234402592373 122975345689896975243035)
                ·
                  rfl

theorem cell20_808291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 5].length) (baseStart_808291 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_808291 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_808291 prefixEnd_808291 := by exact prefixLift 808291
  have htrace : WordTrace (prefixWord ++ tailWord_808291) baseStart_808291 baseEnd_808291 := by
    simpa [prefixWord, tailWord_808291, baseEnd_808291] using wordTrace_append hprefix tailTrace_808291
  have hstable : (prefixWord ++ tailWord_808291).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808291).length < 2 ^ (prefixWord ++ tailWord_808291).sum := by decide
  have hdescent : baseEnd_808291 < baseStart_808291 := by decide
  rcases family_descends (prefixWord ++ tailWord_808291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808305 : List Nat := [1, 2, 2, 2, 1, 2, 3, 1, 6]
def baseStart_808305 : Nat := 118140960795 + 808305 * 2 ^ 59
def prefixEnd_808305 : Nat := 4983230072969 + 3 ^ 40 * 808305 * 2
def baseEnd_808305 : Nat := 368932427051169099262381

theorem tailTrace_808305 : CollatzResearch.WordTrace tailWord_808305 prefixEnd_808305 368932427051169099262381 := by
  unfold tailWord_808305
  simp only [CollatzResearch.WordTrace]
  refine ⟨29481305336656507348586369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19654203557771004899057579 29481305336656507348586369)
  ·
    refine ⟨22110979002492380511439777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29481305336656507348586369 22110979002492380511439777)
    ·
      refine ⟨16583234251869285383579833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22110979002492380511439777 16583234251869285383579833)
      ·
        refine ⟨12437425688901964037684875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16583234251869285383579833 12437425688901964037684875)
        ·
          refine ⟨18656138533352946056527313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12437425688901964037684875 18656138533352946056527313)
          ·
            refine ⟨13992103900014709542395485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18656138533352946056527313 13992103900014709542395485)
            ·
              refine ⟨5247038962505516078398307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13992103900014709542395485 5247038962505516078398307)
              ·
                refine ⟨7870558443758274117597461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5247038962505516078398307 7870558443758274117597461)
                ·
                  refine ⟨368932427051169099262381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7870558443758274117597461 368932427051169099262381)
                  ·
                    rfl

theorem cell20_808305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 6].length) (baseStart_808305 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_808305 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_808305 prefixEnd_808305 := by exact prefixLift 808305
  have htrace : WordTrace (prefixWord ++ tailWord_808305) baseStart_808305 baseEnd_808305 := by
    simpa [prefixWord, tailWord_808305, baseEnd_808305] using wordTrace_append hprefix tailTrace_808305
  have hstable : (prefixWord ++ tailWord_808305).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808305).length < 2 ^ (prefixWord ++ tailWord_808305).sum := by decide
  have hdescent : baseEnd_808305 < baseStart_808305 := by decide
  rcases family_descends (prefixWord ++ tailWord_808305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808329 : List Nat := [1, 2, 1, 1, 7, 1, 7]
def baseStart_808329 : Nat := 118140960795 + 808329 * 2 ^ 59
def prefixEnd_808329 : Nat := 4983230072969 + 3 ^ 40 * 808329 * 2
def baseEnd_808329 : Nat := 40993709033903520273587

theorem tailTrace_808329 : CollatzResearch.WordTrace tailWord_808329 prefixEnd_808329 40993709033903520273587 := by
  unfold tailWord_808329
  simp only [CollatzResearch.WordTrace]
  refine ⟨29482180688569559447460041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19654787125713039631640027 29482180688569559447460041)
  ·
    refine ⟨22111635516427169585595031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29482180688569559447460041 22111635516427169585595031)
    ·
      refine ⟨33167453274640754378392547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22111635516427169585595031 33167453274640754378392547)
      ·
        refine ⟨49751179911961131567588821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33167453274640754378392547 49751179911961131567588821)
        ·
          refine ⟨1166043279186589021115363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 49751179911961131567588821 1166043279186589021115363)
          ·
            refine ⟨1749064918779883531673045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1166043279186589021115363 1749064918779883531673045)
            ·
              refine ⟨40993709033903520273587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1749064918779883531673045 40993709033903520273587)
              ·
                rfl

theorem cell20_808329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 7].length) (baseStart_808329 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_808329 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_808329 prefixEnd_808329 := by exact prefixLift 808329
  have htrace : WordTrace (prefixWord ++ tailWord_808329) baseStart_808329 baseEnd_808329 := by
    simpa [prefixWord, tailWord_808329, baseEnd_808329] using wordTrace_append hprefix tailTrace_808329
  have hstable : (prefixWord ++ tailWord_808329).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808329).length < 2 ^ (prefixWord ++ tailWord_808329).sum := by decide
  have hdescent : baseEnd_808329 < baseStart_808329 := by decide
  rcases family_descends (prefixWord ++ tailWord_808329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808386 : List Nat := [3, 5, 2, 1, 1, 1, 3, 2, 2]
def baseStart_808386 : Nat := 118140960795 + 808386 * 2 ^ 59
def prefixEnd_808386 : Nat := 4983230072969 + 3 ^ 40 * 808386 * 2
def baseEnd_808386 : Nat := 368969397658292817562051

theorem tailTrace_808386 : CollatzResearch.WordTrace tailWord_808386 prefixEnd_808386 368969397658292817562051 := by
  unfold tailWord_808386
  simp only [CollatzResearch.WordTrace]
  refine ⟨7371064912340764545571253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19656173099575372121523341 7371064912340764545571253)
  ·
    refine ⟨691037335531946676147305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7371064912340764545571253 691037335531946676147305)
    ·
      refine ⟨518278001648960007110479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 691037335531946676147305 518278001648960007110479)
      ·
        refine ⟨777417002473440010665719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 518278001648960007110479 777417002473440010665719)
        ·
          refine ⟨1166125503710160015998579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 777417002473440010665719 1166125503710160015998579)
          ·
            refine ⟨1749188255565240023997869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1166125503710160015998579 1749188255565240023997869)
            ·
              refine ⟨655945595836965008999201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1749188255565240023997869 655945595836965008999201)
              ·
                refine ⟨491959196877723756749401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 655945595836965008999201 491959196877723756749401)
                ·
                  refine ⟨368969397658292817562051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 491959196877723756749401 368969397658292817562051)
                  ·
                    rfl

theorem cell20_808386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_808386 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_808386 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_808386 prefixEnd_808386 := by exact prefixLift 808386
  have htrace : WordTrace (prefixWord ++ tailWord_808386) baseStart_808386 baseEnd_808386 := by
    simpa [prefixWord, tailWord_808386, baseEnd_808386] using wordTrace_append hprefix tailTrace_808386
  have hstable : (prefixWord ++ tailWord_808386).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808386).length < 2 ^ (prefixWord ++ tailWord_808386).sum := by decide
  have hdescent : baseEnd_808386 < baseStart_808386 := by decide
  rcases family_descends (prefixWord ++ tailWord_808386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808394 : List Nat := [3, 1, 2, 1, 2, 4, 3, 2, 2]
def baseStart_808394 : Nat := 118140960795 + 808394 * 2 ^ 59
def prefixEnd_808394 : Nat := 4983230072969 + 3 ^ 40 * 808394 * 2
def baseEnd_808394 : Nat := 368973049076280345295351

theorem tailTrace_808394 : CollatzResearch.WordTrace tailWord_808394 prefixEnd_808394 368973049076280345295351 := by
  unfold tailWord_808394
  simp only [CollatzResearch.WordTrace]
  refine ⟨7371137858333518887144059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19656367622222717032384157 7371137858333518887144059)
  ·
    refine ⟨11056706787500278330716089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7371137858333518887144059 11056706787500278330716089)
    ·
      refine ⟨8292530090625208748037067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11056706787500278330716089 8292530090625208748037067)
      ·
        refine ⟨12438795135937813122055601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8292530090625208748037067 12438795135937813122055601)
        ·
          refine ⟨9329096351953359841541701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12438795135937813122055601 9329096351953359841541701)
          ·
            refine ⟨1749205565991254970289069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9329096351953359841541701 1749205565991254970289069)
            ·
              refine ⟨655952087246720613858401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1749205565991254970289069 655952087246720613858401)
              ·
                refine ⟨491964065435040460393801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 655952087246720613858401 491964065435040460393801)
                ·
                  refine ⟨368973049076280345295351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 491964065435040460393801 368973049076280345295351)
                  ·
                    rfl

theorem cell20_808394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 3, 2, 2].length) (baseStart_808394 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_808394 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_808394 prefixEnd_808394 := by exact prefixLift 808394
  have htrace : WordTrace (prefixWord ++ tailWord_808394) baseStart_808394 baseEnd_808394 := by
    simpa [prefixWord, tailWord_808394, baseEnd_808394] using wordTrace_append hprefix tailTrace_808394
  have hstable : (prefixWord ++ tailWord_808394).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808394).length < 2 ^ (prefixWord ++ tailWord_808394).sum := by decide
  have hdescent : baseEnd_808394 < baseStart_808394 := by decide
  rcases family_descends (prefixWord ++ tailWord_808394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808398 : List Nat := [4, 1, 1, 1, 2, 1, 5, 1, 4]
def baseStart_808398 : Nat := 118140960795 + 808398 * 2 ^ 59
def prefixEnd_808398 : Nat := 4983230072969 + 3 ^ 40 * 808398 * 2
def baseEnd_808398 : Nat := 368974874785274109162001

theorem tailTrace_808398 : CollatzResearch.WordTrace tailWord_808398 prefixEnd_808398 368974874785274109162001 := by
  unfold tailWord_808398
  simp only [CollatzResearch.WordTrace]
  refine ⟨3685587165664948028965231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19656464883546389487814565 3685587165664948028965231)
  ·
    refine ⟨5528380748497422043447847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3685587165664948028965231 5528380748497422043447847)
    ·
      refine ⟨8292571122746133065171771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5528380748497422043447847 8292571122746133065171771)
      ·
        refine ⟨12438856684119199597757657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8292571122746133065171771 12438856684119199597757657)
        ·
          refine ⟨9329142513089399698318243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12438856684119199597757657 9329142513089399698318243)
          ·
            refine ⟨13993713769634099547477365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9329142513089399698318243 13993713769634099547477365)
            ·
              refine ⟨1311910665903196832576003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13993713769634099547477365 1311910665903196832576003)
              ·
                refine ⟨1967865998854795248864005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1311910665903196832576003 1967865998854795248864005)
                ·
                  refine ⟨368974874785274109162001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1967865998854795248864005 368974874785274109162001)
                  ·
                    rfl

theorem cell20_808398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 1, 4].length) (baseStart_808398 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_808398 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_808398 prefixEnd_808398 := by exact prefixLift 808398
  have htrace : WordTrace (prefixWord ++ tailWord_808398) baseStart_808398 baseEnd_808398 := by
    simpa [prefixWord, tailWord_808398, baseEnd_808398] using wordTrace_append hprefix tailTrace_808398
  have hstable : (prefixWord ++ tailWord_808398).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808398).length < 2 ^ (prefixWord ++ tailWord_808398).sum := by decide
  have hdescent : baseEnd_808398 < baseStart_808398 := by decide
  rcases family_descends (prefixWord ++ tailWord_808398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808404 : List Nat := [2, 4, 1, 2, 4, 1, 2, 1, 3]
def baseStart_808404 : Nat := 118140960795 + 808404 * 2 ^ 59
def prefixEnd_808404 : Nat := 4983230072969 + 3 ^ 40 * 808404 * 2
def baseEnd_808404 : Nat := 368977613348764754961977

theorem tailTrace_808404 : CollatzResearch.WordTrace tailWord_808404 prefixEnd_808404 368977613348764754961977 := by
  unfold tailWord_808404
  simp only [CollatzResearch.WordTrace]
  refine ⟨14742458081648923628220133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19656610775531898170960177 14742458081648923628220133)
  ·
    refine ⟨2764210890309173180291275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14742458081648923628220133 2764210890309173180291275)
    ·
      refine ⟨4146316335463759770436913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2764210890309173180291275 4146316335463759770436913)
      ·
        refine ⟨3109737251597819827827685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4146316335463759770436913 3109737251597819827827685)
        ·
          refine ⟨583075734674591217717691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3109737251597819827827685 583075734674591217717691)
          ·
            refine ⟨874613602011886826576537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 583075734674591217717691 874613602011886826576537)
            ·
              refine ⟨655960201508915119932403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 874613602011886826576537 655960201508915119932403)
              ·
                refine ⟨983940302263372679898605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 655960201508915119932403 983940302263372679898605)
                ·
                  refine ⟨368977613348764754961977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 983940302263372679898605 368977613348764754961977)
                  ·
                    rfl

theorem cell20_808404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 2, 1, 3].length) (baseStart_808404 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_808404 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_808404 prefixEnd_808404 := by exact prefixLift 808404
  have htrace : WordTrace (prefixWord ++ tailWord_808404) baseStart_808404 baseEnd_808404 := by
    simpa [prefixWord, tailWord_808404, baseEnd_808404] using wordTrace_append hprefix tailTrace_808404
  have hstable : (prefixWord ++ tailWord_808404).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808404).length < 2 ^ (prefixWord ++ tailWord_808404).sum := by decide
  have hdescent : baseEnd_808404 < baseStart_808404 := by decide
  rcases family_descends (prefixWord ++ tailWord_808404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808405 : List Nat := [1, 3, 2, 3, 1, 1, 4, 5]
def baseStart_808405 : Nat := 118140960795 + 808405 * 2 ^ 59
def prefixEnd_808405 : Nat := 4983230072969 + 3 ^ 40 * 808405 * 2
def baseEnd_808405 : Nat := 122992689925337731976213

theorem tailTrace_808405 : CollatzResearch.WordTrace tailWord_808405 prefixEnd_808405 122992689925337731976213 := by
  unfold tailWord_808405
  simp only [CollatzResearch.WordTrace]
  refine ⟨29484952636294224427226669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19656635090862816284817779 29484952636294224427226669)
  ·
    refine ⟨11056857238610334160210001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29484952636294224427226669 11056857238610334160210001)
    ·
      refine ⟨8292642928957750620157501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11056857238610334160210001 8292642928957750620157501)
      ·
        refine ⟨3109741098359156482559063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8292642928957750620157501 3109741098359156482559063)
        ·
          refine ⟨4664611647538734723838595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3109741098359156482559063 4664611647538734723838595)
          ·
            refine ⟨6996917471308102085757893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4664611647538734723838595 6996917471308102085757893)
            ·
              refine ⟨1311922025870269141079605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6996917471308102085757893 1311922025870269141079605)
              ·
                refine ⟨122992689925337731976213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1311922025870269141079605 122992689925337731976213)
                ·
                  rfl

theorem cell20_808405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 5].length) (baseStart_808405 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_808405 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_808405 prefixEnd_808405 := by exact prefixLift 808405
  have htrace : WordTrace (prefixWord ++ tailWord_808405) baseStart_808405 baseEnd_808405 := by
    simpa [prefixWord, tailWord_808405, baseEnd_808405] using wordTrace_append hprefix tailTrace_808405
  have hstable : (prefixWord ++ tailWord_808405).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808405).length < 2 ^ (prefixWord ++ tailWord_808405).sum := by decide
  have hdescent : baseEnd_808405 < baseStart_808405 := by decide
  rcases family_descends (prefixWord ++ tailWord_808405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808449 : List Nat := [1, 2, 4, 1, 4, 2, 2, 2, 2]
def baseStart_808449 : Nat := 118140960795 + 808449 * 2 ^ 59
def prefixEnd_808449 : Nat := 4983230072969 + 3 ^ 40 * 808449 * 2
def baseEnd_808449 : Nat := 368998152574944598461793

theorem tailTrace_808449 : CollatzResearch.WordTrace tailWord_808449 prefixEnd_808449 368998152574944598461793 := by
  unfold tailWord_808449
  simp only [CollatzResearch.WordTrace]
  refine ⟨29486557448134819941828401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19657704965423213294552267 29486557448134819941828401)
  ·
    refine ⟨22114918086101114956371301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29486557448134819941828401 22114918086101114956371301)
    ·
      refine ⟨4146547141143959054319619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22114918086101114956371301 4146547141143959054319619)
      ·
        refine ⟨6219820711715938581479429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4146547141143959054319619 6219820711715938581479429)
        ·
          refine ⟨1166216383446738484027393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6219820711715938581479429 1166216383446738484027393)
          ·
            refine ⟨874662287585053863020545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1166216383446738484027393 874662287585053863020545)
            ·
              refine ⟨655996715688790397265409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 874662287585053863020545 655996715688790397265409)
              ·
                refine ⟨491997536766592797949057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 655996715688790397265409 491997536766592797949057)
                ·
                  refine ⟨368998152574944598461793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 491997536766592797949057 368998152574944598461793)
                  ·
                    rfl

theorem cell20_808449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 2, 2, 2].length) (baseStart_808449 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_808449 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_808449 prefixEnd_808449 := by exact prefixLift 808449
  have htrace : WordTrace (prefixWord ++ tailWord_808449) baseStart_808449 baseEnd_808449 := by
    simpa [prefixWord, tailWord_808449, baseEnd_808449] using wordTrace_append hprefix tailTrace_808449
  have hstable : (prefixWord ++ tailWord_808449).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808449).length < 2 ^ (prefixWord ++ tailWord_808449).sum := by decide
  have hdescent : baseEnd_808449 < baseStart_808449 := by decide
  rcases family_descends (prefixWord ++ tailWord_808449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808457 : List Nat := [1, 2, 1, 1, 3, 1, 4, 3, 4]
def baseStart_808457 : Nat := 118140960795 + 808457 * 2 ^ 59
def prefixEnd_808457 : Nat := 4983230072969 + 3 ^ 40 * 808457 * 2
def baseEnd_808457 : Nat := 369001803992932126195093

theorem tailTrace_808457 : CollatzResearch.WordTrace tailWord_808457 prefixEnd_808457 369001803992932126195093 := by
  unfold tailWord_808457
  simp only [CollatzResearch.WordTrace]
  refine ⟨29486849232105837308119625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19657899488070558205413083 29486849232105837308119625)
  ·
    refine ⟨22115136924079377981089719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29486849232105837308119625 22115136924079377981089719)
    ·
      refine ⟨33172705386119066971634579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22115136924079377981089719 33172705386119066971634579)
      ·
        refine ⟨49759058079178600457451869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33172705386119066971634579 49759058079178600457451869)
        ·
          refine ⟨18659646779691975171544451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49759058079178600457451869 18659646779691975171544451)
          ·
            refine ⟨27989470169537962757316677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18659646779691975171544451 27989470169537962757316677)
            ·
              refine ⟨5248025656788368016996877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27989470169537962757316677 5248025656788368016996877)
              ·
                refine ⟨1968009621295638006373829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5248025656788368016996877 1968009621295638006373829)
                ·
                  refine ⟨369001803992932126195093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1968009621295638006373829 369001803992932126195093)
                  ·
                    rfl

theorem cell20_808457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 3, 4].length) (baseStart_808457 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_808457 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_808457 prefixEnd_808457 := by exact prefixLift 808457
  have htrace : WordTrace (prefixWord ++ tailWord_808457) baseStart_808457 baseEnd_808457 := by
    simpa [prefixWord, tailWord_808457, baseEnd_808457] using wordTrace_append hprefix tailTrace_808457
  have hstable : (prefixWord ++ tailWord_808457).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808457).length < 2 ^ (prefixWord ++ tailWord_808457).sum := by decide
  have hdescent : baseEnd_808457 < baseStart_808457 := by decide
  rcases family_descends (prefixWord ++ tailWord_808457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808460 : List Nat := [2, 2, 1, 2, 5, 2, 1, 5]
def baseStart_808460 : Nat := 118140960795 + 808460 * 2 ^ 59
def prefixEnd_808460 : Nat := 4983230072969 + 3 ^ 40 * 808460 * 2
def baseEnd_808460 : Nat := 123001057758225816365027

theorem tailTrace_808460 : CollatzResearch.WordTrace tailWord_808460 prefixEnd_808460 123001057758225816365027 := by
  unfold tailWord_808460
  simp only [CollatzResearch.WordTrace]
  refine ⟨14743479325547484410239417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19657972434063312546985889 14743479325547484410239417)
  ·
    refine ⟨11057609494160613307679563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14743479325547484410239417 11057609494160613307679563)
    ·
      refine ⟨16586414241240919961519345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11057609494160613307679563 16586414241240919961519345)
      ·
        refine ⟨12439810680930689971139509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16586414241240919961519345 12439810680930689971139509)
        ·
          refine ⟨1166232251337252184794329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12439810680930689971139509 1166232251337252184794329)
          ·
            refine ⟨874674188502939138595747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1166232251337252184794329 874674188502939138595747)
            ·
              refine ⟨1312011282754408707893621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 874674188502939138595747 1312011282754408707893621)
              ·
                refine ⟨123001057758225816365027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1312011282754408707893621 123001057758225816365027)
                ·
                  rfl

theorem cell20_808460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 5].length) (baseStart_808460 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_808460 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_808460 prefixEnd_808460 := by exact prefixLift 808460
  have htrace : WordTrace (prefixWord ++ tailWord_808460) baseStart_808460 baseEnd_808460 := by
    simpa [prefixWord, tailWord_808460, baseEnd_808460] using wordTrace_append hprefix tailTrace_808460
  have hstable : (prefixWord ++ tailWord_808460).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808460).length < 2 ^ (prefixWord ++ tailWord_808460).sum := by decide
  have hdescent : baseEnd_808460 < baseStart_808460 := by decide
  rcases family_descends (prefixWord ++ tailWord_808460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808505 : List Nat := [1, 2, 1, 5, 1, 2, 3, 2, 3]
def baseStart_808505 : Nat := 118140960795 + 808505 * 2 ^ 59
def prefixEnd_808505 : Nat := 4983230072969 + 3 ^ 40 * 808505 * 2
def baseEnd_808505 : Nat := 369023712500857292594897

theorem tailTrace_808505 : CollatzResearch.WordTrace tailWord_808505 prefixEnd_808505 369023712500857292594897 := by
  unfold tailWord_808505
  simp only [CollatzResearch.WordTrace]
  refine ⟨29488599935931941505866969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19659066623954627670577979 29488599935931941505866969)
  ·
    refine ⟨22116449951948956129400227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29488599935931941505866969 22116449951948956129400227)
    ·
      refine ⟨33174674927923434194100341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22116449951948956129400227 33174674927923434194100341)
      ·
        refine ⟨3110125774492821955696907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33174674927923434194100341 3110125774492821955696907)
        ·
          refine ⟨4665188661739232933545361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3110125774492821955696907 4665188661739232933545361)
          ·
            refine ⟨3498891496304424700159021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4665188661739232933545361 3498891496304424700159021)
            ·
              refine ⟨1312084311114159262559633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3498891496304424700159021 1312084311114159262559633)
              ·
                refine ⟨984063233335619446919725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1312084311114159262559633 984063233335619446919725)
                ·
                  refine ⟨369023712500857292594897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 984063233335619446919725 369023712500857292594897)
                  ·
                    rfl

theorem cell20_808505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 2, 3].length) (baseStart_808505 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_808505 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_808505 prefixEnd_808505 := by exact prefixLift 808505
  have htrace : WordTrace (prefixWord ++ tailWord_808505) baseStart_808505 baseEnd_808505 := by
    simpa [prefixWord, tailWord_808505, baseEnd_808505] using wordTrace_append hprefix tailTrace_808505
  have hstable : (prefixWord ++ tailWord_808505).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808505).length < 2 ^ (prefixWord ++ tailWord_808505).sum := by decide
  have hdescent : baseEnd_808505 < baseStart_808505 := by decide
  rcases family_descends (prefixWord ++ tailWord_808505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808518 : List Nat := [6, 1, 1, 1, 3, 1, 3, 1, 3]
def baseStart_808518 : Nat := 118140960795 + 808518 * 2 ^ 59
def prefixEnd_808518 : Nat := 4983230072969 + 3 ^ 40 * 808518 * 2
def baseEnd_808518 : Nat := 369029646055087025161511

theorem tailTrace_808518 : CollatzResearch.WordTrace tailWord_808518 prefixEnd_808518 369029646055087025161511 := by
  unfold tailWord_808518
  simp only [CollatzResearch.WordTrace]
  refine ⟨921533565152651397690319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 19659382723256563150726805 921533565152651397690319)
  ·
    refine ⟨1382300347728977096535479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 921533565152651397690319 1382300347728977096535479)
    ·
      refine ⟨2073450521593465644803219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1382300347728977096535479 2073450521593465644803219)
      ·
        refine ⟨3110175782390198467204829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2073450521593465644803219 3110175782390198467204829)
        ·
          refine ⟨1166315918396324425201811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3110175782390198467204829 1166315918396324425201811)
          ·
            refine ⟨1749473877594486637802717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1166315918396324425201811 1749473877594486637802717)
            ·
              refine ⟨656052704097932489176019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1749473877594486637802717 656052704097932489176019)
              ·
                refine ⟨984079056146898733764029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 656052704097932489176019 984079056146898733764029)
                ·
                  refine ⟨369029646055087025161511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 984079056146898733764029 369029646055087025161511)
                  ·
                    rfl

theorem cell20_808518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_808518 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_808518 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_808518 prefixEnd_808518 := by exact prefixLift 808518
  have htrace : WordTrace (prefixWord ++ tailWord_808518) baseStart_808518 baseEnd_808518 := by
    simpa [prefixWord, tailWord_808518, baseEnd_808518] using wordTrace_append hprefix tailTrace_808518
  have hstable : (prefixWord ++ tailWord_808518).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808518).length < 2 ^ (prefixWord ++ tailWord_808518).sum := by decide
  have hdescent : baseEnd_808518 < baseStart_808518 := by decide
  rcases family_descends (prefixWord ++ tailWord_808518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808629 : List Nat := [1, 3, 3, 3, 3, 1, 1, 5]
def baseStart_808629 : Nat := 118140960795 + 808629 * 2 ^ 59
def prefixEnd_808629 : Nat := 4983230072969 + 3 ^ 40 * 808629 * 2
def baseEnd_808629 : Nat := 123026769826554657487019

theorem tailTrace_808629 : CollatzResearch.WordTrace tailWord_808629 prefixEnd_808629 123026769826554657487019 := by
  unfold tailWord_808629
  simp only [CollatzResearch.WordTrace]
  refine ⟨29493122587482710683380941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19662081724988473788920627 29493122587482710683380941)
  ·
    refine ⟨11059920970306016506267853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29493122587482710683380941 11059920970306016506267853)
    ·
      refine ⟨4147470363864756189850445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11059920970306016506267853 4147470363864756189850445)
      ·
        refine ⟨1555301386449283571193917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4147470363864756189850445 1555301386449283571193917)
        ·
          refine ⟨583238019918481339197719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1555301386449283571193917 583238019918481339197719)
          ·
            refine ⟨874857029877722008796579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 583238019918481339197719 874857029877722008796579)
            ·
              refine ⟨1312285544816583013194869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 874857029877722008796579 1312285544816583013194869)
              ·
                refine ⟨123026769826554657487019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1312285544816583013194869 123026769826554657487019)
                ·
                  rfl

theorem cell20_808629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 5].length) (baseStart_808629 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_808629 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_808629 prefixEnd_808629 := by exact prefixLift 808629
  have htrace : WordTrace (prefixWord ++ tailWord_808629) baseStart_808629 baseEnd_808629 := by
    simpa [prefixWord, tailWord_808629, baseEnd_808629] using wordTrace_append hprefix tailTrace_808629
  have hstable : (prefixWord ++ tailWord_808629).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808629).length < 2 ^ (prefixWord ++ tailWord_808629).sum := by decide
  have hdescent : baseEnd_808629 < baseStart_808629 := by decide
  rcases family_descends (prefixWord ++ tailWord_808629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808640 : List Nat := [2, 1, 1, 2, 4, 1, 1, 5, 3]
def baseStart_808640 : Nat := 118140960795 + 808640 * 2 ^ 59
def prefixEnd_808640 : Nat := 4983230072969 + 3 ^ 40 * 808640 * 2
def baseEnd_808640 : Nat := 369085330179396823094345

theorem tailTrace_808640 : CollatzResearch.WordTrace tailWord_808640 prefixEnd_808640 369085330179396823094345 := by
  unfold tailWord_808640
  simp only [CollatzResearch.WordTrace]
  refine ⟨14746761895221429781015687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19662349193628573041354249 14746761895221429781015687)
  ·
    refine ⟨22120142842832144671523531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14746761895221429781015687 22120142842832144671523531)
    ·
      refine ⟨33180214264248217007285297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22120142842832144671523531 33180214264248217007285297)
      ·
        refine ⟨24885160698186162755463973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33180214264248217007285297 24885160698186162755463973)
        ·
          refine ⟨4665967630909905516649495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24885160698186162755463973 4665967630909905516649495)
          ·
            refine ⟨6998951446364858274974243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4665967630909905516649495 6998951446364858274974243)
            ·
              refine ⟨10498427169547287412461365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6998951446364858274974243 10498427169547287412461365)
              ·
                refine ⟨984227547145058194918253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10498427169547287412461365 984227547145058194918253)
                ·
                  refine ⟨369085330179396823094345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 984227547145058194918253 369085330179396823094345)
                  ·
                    rfl

theorem cell20_808640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 5, 3].length) (baseStart_808640 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_808640 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_808640 prefixEnd_808640 := by exact prefixLift 808640
  have htrace : WordTrace (prefixWord ++ tailWord_808640) baseStart_808640 baseEnd_808640 := by
    simpa [prefixWord, tailWord_808640, baseEnd_808640] using wordTrace_append hprefix tailTrace_808640
  have hstable : (prefixWord ++ tailWord_808640).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808640).length < 2 ^ (prefixWord ++ tailWord_808640).sum := by decide
  have hdescent : baseEnd_808640 < baseStart_808640 := by decide
  rcases family_descends (prefixWord ++ tailWord_808640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808646 : List Nat := [6, 1, 2, 1, 1, 2, 3, 4]
def baseStart_808646 : Nat := 118140960795 + 808646 * 2 ^ 59
def prefixEnd_808646 : Nat := 4983230072969 + 3 ^ 40 * 808646 * 2
def baseEnd_808646 : Nat := 123029356247629156298107

theorem tailTrace_808646 : CollatzResearch.WordTrace tailWord_808646 prefixEnd_808646 123029356247629156298107 := by
  unfold tailWord_808646
  simp only [CollatzResearch.WordTrace]
  refine ⟨921679457138160080835931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 19662495085614081724499861 921679457138160080835931)
  ·
    refine ⟨1382519185707240121253897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 921679457138160080835931 1382519185707240121253897)
    ·
      refine ⟨1036889389280430090940423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1382519185707240121253897 1036889389280430090940423)
      ·
        refine ⟨1555334083920645136410635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1036889389280430090940423 1555334083920645136410635)
        ·
          refine ⟨2333001125880967704615953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1555334083920645136410635 2333001125880967704615953)
          ·
            refine ⟨1749750844410725778461965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2333001125880967704615953 1749750844410725778461965)
            ·
              refine ⟨656156566654022166923237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1749750844410725778461965 656156566654022166923237)
              ·
                refine ⟨123029356247629156298107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 656156566654022166923237 123029356247629156298107)
                ·
                  rfl

theorem cell20_808646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_808646 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_808646 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_808646 prefixEnd_808646 := by exact prefixLift 808646
  have htrace : WordTrace (prefixWord ++ tailWord_808646) baseStart_808646 baseEnd_808646 := by
    simpa [prefixWord, tailWord_808646, baseEnd_808646] using wordTrace_append hprefix tailTrace_808646
  have hstable : (prefixWord ++ tailWord_808646).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808646).length < 2 ^ (prefixWord ++ tailWord_808646).sum := by decide
  have hdescent : baseEnd_808646 < baseStart_808646 := by decide
  rcases family_descends (prefixWord ++ tailWord_808646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808647 : List Nat := [1, 1, 4, 1, 1, 1, 5, 2, 4]
def baseStart_808647 : Nat := 118140960795 + 808647 * 2 ^ 59
def prefixEnd_808647 : Nat := 4983230072969 + 3 ^ 40 * 808647 * 2
def baseEnd_808647 : Nat := 369088525170135909860983

theorem tailTrace_808647 : CollatzResearch.WordTrace tailWord_808647 prefixEnd_808647 369088525170135909860983 := by
  unfold tailWord_808647
  simp only [CollatzResearch.WordTrace]
  refine ⟨29493779101417499757536195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19662519400944999838357463 29493779101417499757536195)
  ·
    refine ⟨44240668652126249636304293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29493779101417499757536195 44240668652126249636304293)
    ·
      refine ⟨8295125372273671806807055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44240668652126249636304293 8295125372273671806807055)
      ·
        refine ⟨12442688058410507710210583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8295125372273671806807055 12442688058410507710210583)
        ·
          refine ⟨18664032087615761565315875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12442688058410507710210583 18664032087615761565315875)
          ·
            refine ⟨27996048131423642347973813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18664032087615761565315875 27996048131423642347973813)
            ·
              refine ⟨2624629512320966470122545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27996048131423642347973813 2624629512320966470122545)
              ·
                refine ⟨1968472134240724852591909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2624629512320966470122545 1968472134240724852591909)
                ·
                  refine ⟨369088525170135909860983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1968472134240724852591909 369088525170135909860983)
                  ·
                    rfl

theorem cell20_808647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 2, 4].length) (baseStart_808647 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_808647 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_808647 prefixEnd_808647 := by exact prefixLift 808647
  have htrace : WordTrace (prefixWord ++ tailWord_808647) baseStart_808647 baseEnd_808647 := by
    simpa [prefixWord, tailWord_808647, baseEnd_808647] using wordTrace_append hprefix tailTrace_808647
  have hstable : (prefixWord ++ tailWord_808647).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808647).length < 2 ^ (prefixWord ++ tailWord_808647).sum := by decide
  have hdescent : baseEnd_808647 < baseStart_808647 := by decide
  rcases family_descends (prefixWord ++ tailWord_808647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808650 : List Nat := [3, 1, 2, 1, 5, 1, 3, 4]
def baseStart_808650 : Nat := 118140960795 + 808650 * 2 ^ 59
def prefixEnd_808650 : Nat := 4983230072969 + 3 ^ 40 * 808650 * 2
def baseEnd_808650 : Nat := 123029964817293744253657

theorem tailTrace_808650 : CollatzResearch.WordTrace tailWord_808650 prefixEnd_808650 123029964817293744253657 := by
  unfold tailWord_808650
  simp only [CollatzResearch.WordTrace]
  refine ⟨7373472130101657817473851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19662592346937754179930269 7373472130101657817473851)
  ·
    refine ⟨11060208195152486726210777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7373472130101657817473851 11060208195152486726210777)
    ·
      refine ⟨8295156146364365044658083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11060208195152486726210777 8295156146364365044658083)
      ·
        refine ⟨12442734219546547566987125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8295156146364365044658083 12442734219546547566987125)
        ·
          refine ⟨1166506333082488834405043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12442734219546547566987125 1166506333082488834405043)
          ·
            refine ⟨1749759499623733251607565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1166506333082488834405043 1749759499623733251607565)
            ·
              refine ⟨656159812358899969352837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1749759499623733251607565 656159812358899969352837)
              ·
                refine ⟨123029964817293744253657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 656159812358899969352837 123029964817293744253657)
                ·
                  rfl

theorem cell20_808650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 3, 4].length) (baseStart_808650 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_808650 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_808650 prefixEnd_808650 := by exact prefixLift 808650
  have htrace : WordTrace (prefixWord ++ tailWord_808650) baseStart_808650 baseEnd_808650 := by
    simpa [prefixWord, tailWord_808650, baseEnd_808650] using wordTrace_append hprefix tailTrace_808650
  have hstable : (prefixWord ++ tailWord_808650).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808650).length < 2 ^ (prefixWord ++ tailWord_808650).sum := by decide
  have hdescent : baseEnd_808650 < baseStart_808650 := by decide
  rcases family_descends (prefixWord ++ tailWord_808650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808660 : List Nat := [2, 4, 1, 3, 1, 2, 2, 3, 2]
def baseStart_808660 : Nat := 118140960795 + 808660 * 2 ^ 59
def prefixEnd_808660 : Nat := 4983230072969 + 3 ^ 40 * 808660 * 2
def baseEnd_808660 : Nat := 369094458724365642427597

theorem tailTrace_808660 : CollatzResearch.WordTrace tailWord_808660 prefixEnd_808660 369094458724365642427597 := by
  unfold tailWord_808660
  simp only [CollatzResearch.WordTrace]
  refine ⟨14747126625185201488879717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19662835500246935318506289 14747126625185201488879717)
  ·
    refine ⟨2765086242222225279164947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14747126625185201488879717 2765086242222225279164947)
    ·
      refine ⟨4147629363333337918747421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2765086242222225279164947 4147629363333337918747421)
      ·
        refine ⟨1555361011250001719530283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4147629363333337918747421 1555361011250001719530283)
        ·
          refine ⟨2333041516875002579295425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1555361011250001719530283 2333041516875002579295425)
          ·
            refine ⟨1749781137656251934471569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2333041516875002579295425 1749781137656251934471569)
            ·
              refine ⟨1312335853242188950853677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1749781137656251934471569 1312335853242188950853677)
              ·
                refine ⟨492125944965820856570129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1312335853242188950853677 492125944965820856570129)
                ·
                  refine ⟨369094458724365642427597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 492125944965820856570129 369094458724365642427597)
                  ·
                    rfl

theorem cell20_808660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 3, 2].length) (baseStart_808660 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_808660 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_808660 prefixEnd_808660 := by exact prefixLift 808660
  have htrace : WordTrace (prefixWord ++ tailWord_808660) baseStart_808660 baseEnd_808660 := by
    simpa [prefixWord, tailWord_808660, baseEnd_808660] using wordTrace_append hprefix tailTrace_808660
  have hstable : (prefixWord ++ tailWord_808660).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808660).length < 2 ^ (prefixWord ++ tailWord_808660).sum := by decide
  have hdescent : baseEnd_808660 < baseStart_808660 := by decide
  rcases family_descends (prefixWord ++ tailWord_808660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808730 : List Nat := [3, 1, 1, 3, 2, 2, 8]
def baseStart_808730 : Nat := 118140960795 + 808730 * 2 ^ 59
def prefixEnd_808730 : Nat := 4983230072969 + 3 ^ 40 * 808730 * 2
def baseEnd_808730 : Nat := 41014045403528501121553

theorem tailTrace_808730 : CollatzResearch.WordTrace tailWord_808730 prefixEnd_808730 41014045403528501121553 := by
  unfold tailWord_808730
  simp only [CollatzResearch.WordTrace]
  refine ⟨7374201590029201233201911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19664537573411203288538429 7374201590029201233201911)
  ·
    refine ⟨11061302385043801849802867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7374201590029201233201911 11061302385043801849802867)
    ·
      refine ⟨16591953577565702774704301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11061302385043801849802867 16591953577565702774704301)
      ·
        refine ⟨6221982591587138540514113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16591953577565702774704301 6221982591587138540514113)
        ·
          refine ⟨4666486943690353905385585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6221982591587138540514113 4666486943690353905385585)
          ·
            refine ⟨3499865207767765429039189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4666486943690353905385585 3499865207767765429039189)
            ·
              refine ⟨41014045403528501121553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3499865207767765429039189 41014045403528501121553)
              ·
                rfl

theorem cell20_808730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 8].length) (baseStart_808730 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_808730 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_808730 prefixEnd_808730 := by exact prefixLift 808730
  have htrace : WordTrace (prefixWord ++ tailWord_808730) baseStart_808730 baseEnd_808730 := by
    simpa [prefixWord, tailWord_808730, baseEnd_808730] using wordTrace_append hprefix tailTrace_808730
  have hstable : (prefixWord ++ tailWord_808730).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808730).length < 2 ^ (prefixWord ++ tailWord_808730).sum := by decide
  have hdescent : baseEnd_808730 < baseStart_808730 := by decide
  rcases family_descends (prefixWord ++ tailWord_808730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808740 : List Nat := [2, 3, 1, 3, 2, 1, 3, 1, 4]
def baseStart_808740 : Nat := 118140960795 + 808740 * 2 ^ 59
def prefixEnd_808740 : Nat := 4983230072969 + 3 ^ 40 * 808740 * 2
def baseEnd_808740 : Nat := 369130972904240919760603

theorem tailTrace_808740 : CollatzResearch.WordTrace tailWord_808740 prefixEnd_808740 369130972904240919760603 := by
  unfold tailWord_808740
  simp only [CollatzResearch.WordTrace]
  refine ⟨14748585545040288320335837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19664780726720384427114449 14748585545040288320335837)
  ·
    refine ⟨5530719579390108120125939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14748585545040288320335837 5530719579390108120125939)
    ·
      refine ⟨8296079369085162180188909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5530719579390108120125939 8296079369085162180188909)
      ·
        refine ⟨3111029763406935817570841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8296079369085162180188909 3111029763406935817570841)
        ·
          refine ⟨2333272322555201863178131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3111029763406935817570841 2333272322555201863178131)
          ·
            refine ⟨3499908483832802794767197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2333272322555201863178131 3499908483832802794767197)
            ·
              refine ⟨1312465681437301048037699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3499908483832802794767197 1312465681437301048037699)
              ·
                refine ⟨1968698522155951572056549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1312465681437301048037699 1968698522155951572056549)
                ·
                  refine ⟨369130972904240919760603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1968698522155951572056549 369130972904240919760603)
                  ·
                    rfl

theorem cell20_808740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 1, 4].length) (baseStart_808740 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_808740 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_808740 prefixEnd_808740 := by exact prefixLift 808740
  have htrace : WordTrace (prefixWord ++ tailWord_808740) baseStart_808740 baseEnd_808740 := by
    simpa [prefixWord, tailWord_808740, baseEnd_808740] using wordTrace_append hprefix tailTrace_808740
  have hstable : (prefixWord ++ tailWord_808740).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808740).length < 2 ^ (prefixWord ++ tailWord_808740).sum := by decide
  have hdescent : baseEnd_808740 < baseStart_808740 := by decide
  rcases family_descends (prefixWord ++ tailWord_808740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808750 : List Nat := [4, 1, 3, 2, 2, 1, 1, 3, 3]
def baseStart_808750 : Nat := 118140960795 + 808750 * 2 ^ 59
def prefixEnd_808750 : Nat := 4983230072969 + 3 ^ 40 * 808750 * 2
def baseEnd_808750 : Nat := 369135537176725329427229

theorem tailTrace_808750 : CollatzResearch.WordTrace tailWord_808750 prefixEnd_808750 369135537176725329427229 := by
  unfold tailWord_808750
  simp only [CollatzResearch.WordTrace]
  refine ⟨3687191977505543543566963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19665023880029565565690469 3687191977505543543566963)
  ·
    refine ⟨5530787966258315315350445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3687191977505543543566963 5530787966258315315350445)
    ·
      refine ⟨2074045487346868243256417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5530787966258315315350445 2074045487346868243256417)
      ·
        refine ⟨1555534115510151182442313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2074045487346868243256417 1555534115510151182442313)
        ·
          refine ⟨1166650586632613386831735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1555534115510151182442313 1166650586632613386831735)
          ·
            refine ⟨1749975879948920080247603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1166650586632613386831735 1749975879948920080247603)
            ·
              refine ⟨2624963819923380120371405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1749975879948920080247603 2624963819923380120371405)
              ·
                refine ⟨984361432471267545139277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2624963819923380120371405 984361432471267545139277)
                ·
                  refine ⟨369135537176725329427229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 984361432471267545139277 369135537176725329427229)
                  ·
                    rfl

theorem cell20_808750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 3, 3].length) (baseStart_808750 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_808750 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_808750 prefixEnd_808750 := by exact prefixLift 808750
  have htrace : WordTrace (prefixWord ++ tailWord_808750) baseStart_808750 baseEnd_808750 := by
    simpa [prefixWord, tailWord_808750, baseEnd_808750] using wordTrace_append hprefix tailTrace_808750
  have hstable : (prefixWord ++ tailWord_808750).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808750).length < 2 ^ (prefixWord ++ tailWord_808750).sum := by decide
  have hdescent : baseEnd_808750 < baseStart_808750 := by decide
  rcases family_descends (prefixWord ++ tailWord_808750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808775 : List Nat := [1, 1, 4, 1, 2, 1, 2, 1, 7]
def baseStart_808775 : Nat := 118140960795 + 808775 * 2 ^ 59
def prefixEnd_808775 : Nat := 4983230072969 + 3 ^ 40 * 808775 * 2
def baseEnd_808775 : Nat := 369146947857936353593793

theorem tailTrace_808775 : CollatzResearch.WordTrace tailWord_808775 prefixEnd_808775 369146947857936353593793 := by
  unfold tailWord_808775
  simp only [CollatzResearch.WordTrace]
  refine ⟨29498447644953777618195779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19665631763302518412130519 29498447644953777618195779)
  ·
    refine ⟨44247671467430666427293669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29498447644953777618195779 44247671467430666427293669)
    ·
      refine ⟨8296438400143249955117563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44247671467430666427293669 8296438400143249955117563)
      ·
        refine ⟨12444657600214874932676345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8296438400143249955117563 12444657600214874932676345)
        ·
          refine ⟨9333493200161156199507259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12444657600214874932676345 9333493200161156199507259)
          ·
            refine ⟨14000239800241734299260889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9333493200161156199507259 14000239800241734299260889)
            ·
              refine ⟨10500179850181300724445667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14000239800241734299260889 10500179850181300724445667)
              ·
                refine ⟨15750269775271951086668501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10500179850181300724445667 15750269775271951086668501)
                ·
                  refine ⟨369146947857936353593793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15750269775271951086668501 369146947857936353593793)
                  ·
                    rfl

theorem cell20_808775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 7].length) (baseStart_808775 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_808775 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_808775 prefixEnd_808775 := by exact prefixLift 808775
  have htrace : WordTrace (prefixWord ++ tailWord_808775) baseStart_808775 baseEnd_808775 := by
    simpa [prefixWord, tailWord_808775, baseEnd_808775] using wordTrace_append hprefix tailTrace_808775
  have hstable : (prefixWord ++ tailWord_808775).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808775).length < 2 ^ (prefixWord ++ tailWord_808775).sum := by decide
  have hdescent : baseEnd_808775 < baseStart_808775 := by decide
  rcases family_descends (prefixWord ++ tailWord_808775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808778 : List Nat := [3, 1, 2, 1, 1, 1, 4, 5, 2]
def baseStart_808778 : Nat := 118140960795 + 808778 * 2 ^ 59
def prefixEnd_808778 : Nat := 4983230072969 + 3 ^ 40 * 808778 * 2
def baseEnd_808778 : Nat := 369148317139681676493781

theorem tailTrace_808778 : CollatzResearch.WordTrace tailWord_808778 prefixEnd_808778 369148317139681676493781 := by
  unfold tailWord_808778
  simp only [CollatzResearch.WordTrace]
  refine ⟨7374639265985727282638747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19665704709295272753703325 7374639265985727282638747)
  ·
    refine ⟨11061958898978590923958121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7374639265985727282638747 11061958898978590923958121)
    ·
      refine ⟨8296469174233943192968591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11061958898978590923958121 8296469174233943192968591)
      ·
        refine ⟨12444703761350914789452887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8296469174233943192968591 12444703761350914789452887)
        ·
          refine ⟨18667055642026372184179331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12444703761350914789452887 18667055642026372184179331)
          ·
            refine ⟨28000583463039558276268997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18667055642026372184179331 28000583463039558276268997)
            ·
              refine ⟨5250109399319917176800437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28000583463039558276268997 5250109399319917176800437)
              ·
                refine ⟨492197756186242235325041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5250109399319917176800437 492197756186242235325041)
                ·
                  refine ⟨369148317139681676493781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 492197756186242235325041 369148317139681676493781)
                  ·
                    rfl

theorem cell20_808778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 5, 2].length) (baseStart_808778 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_808778 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_808778 prefixEnd_808778 := by exact prefixLift 808778
  have htrace : WordTrace (prefixWord ++ tailWord_808778) baseStart_808778 baseEnd_808778 := by
    simpa [prefixWord, tailWord_808778, baseEnd_808778] using wordTrace_append hprefix tailTrace_808778
  have hstable : (prefixWord ++ tailWord_808778).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808778).length < 2 ^ (prefixWord ++ tailWord_808778).sum := by decide
  have hdescent : baseEnd_808778 < baseStart_808778 := by decide
  rcases family_descends (prefixWord ++ tailWord_808778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808791 : List Nat := [1, 1, 3, 2, 6, 1, 2, 2, 2]
def baseStart_808791 : Nat := 118140960795 + 808791 * 2 ^ 59
def prefixEnd_808791 : Nat := 4983230072969 + 3 ^ 40 * 808791 * 2
def baseEnd_808791 : Nat := 369154250693911409060395

theorem tailTrace_808791 : CollatzResearch.WordTrace tailWord_808791 prefixEnd_808791 369154250693911409060395 := by
  unfold tailWord_808791
  simp only [CollatzResearch.WordTrace]
  refine ⟨29499031212895812350778227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19666020808597208233852151 29499031212895812350778227)
  ·
    refine ⟨44248546819343718526167341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29499031212895812350778227 44248546819343718526167341)
    ·
      refine ⟨16593205057253894447312753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44248546819343718526167341 16593205057253894447312753)
      ·
        refine ⟨12444903792940420835484565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16593205057253894447312753 12444903792940420835484565)
        ·
          refine ⟨583354865294082226663339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 12444903792940420835484565 583354865294082226663339)
          ·
            refine ⟨875032297941123339995009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 583354865294082226663339 875032297941123339995009)
            ·
              refine ⟨656274223455842504996257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 875032297941123339995009 656274223455842504996257)
              ·
                refine ⟨492205667591881878747193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 656274223455842504996257 492205667591881878747193)
                ·
                  refine ⟨369154250693911409060395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 492205667591881878747193 369154250693911409060395)
                  ·
                    rfl

theorem cell20_808791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 2, 2, 2].length) (baseStart_808791 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_808791 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_808791 prefixEnd_808791 := by exact prefixLift 808791
  have htrace : WordTrace (prefixWord ++ tailWord_808791) baseStart_808791 baseEnd_808791 := by
    simpa [prefixWord, tailWord_808791, baseEnd_808791] using wordTrace_append hprefix tailTrace_808791
  have hstable : (prefixWord ++ tailWord_808791).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808791).length < 2 ^ (prefixWord ++ tailWord_808791).sum := by decide
  have hdescent : baseEnd_808791 < baseStart_808791 := by decide
  rcases family_descends (prefixWord ++ tailWord_808791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808802 : List Nat := [3, 3, 2, 1, 2, 3, 1, 5]
def baseStart_808802 : Nat := 118140960795 + 808802 * 2 ^ 59
def prefixEnd_808802 : Nat := 4983230072969 + 3 ^ 40 * 808802 * 2
def baseEnd_808802 : Nat := 123053090464548086564561

theorem tailTrace_808802 : CollatzResearch.WordTrace tailWord_808802 prefixEnd_808802 123053090464548086564561 := by
  unfold tailWord_808802
  simp only [CollatzResearch.WordTrace]
  refine ⟨7374858103963990307357165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19666288277237307486285773 7374858103963990307357165)
  ·
    refine ⟨2765571788986496365258937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7374858103963990307357165 2765571788986496365258937)
    ·
      refine ⟨2074178841739872273944203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2765571788986496365258937 2074178841739872273944203)
      ·
        refine ⟨3111268262609808410916305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2074178841739872273944203 3111268262609808410916305)
        ·
          refine ⟨2333451196957356308187229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3111268262609808410916305 2333451196957356308187229)
          ·
            refine ⟨875044198859008615570211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2333451196957356308187229 875044198859008615570211)
            ·
              refine ⟨1312566298288512923355317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 875044198859008615570211 1312566298288512923355317)
              ·
                refine ⟨123053090464548086564561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1312566298288512923355317 123053090464548086564561)
                ·
                  rfl

theorem cell20_808802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 5].length) (baseStart_808802 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_808802 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_808802 prefixEnd_808802 := by exact prefixLift 808802
  have htrace : WordTrace (prefixWord ++ tailWord_808802) baseStart_808802 baseEnd_808802 := by
    simpa [prefixWord, tailWord_808802, baseEnd_808802] using wordTrace_append hprefix tailTrace_808802
  have hstable : (prefixWord ++ tailWord_808802).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808802).length < 2 ^ (prefixWord ++ tailWord_808802).sum := by decide
  have hdescent : baseEnd_808802 < baseStart_808802 := by decide
  rcases family_descends (prefixWord ++ tailWord_808802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808884 : List Nat := [2, 5, 2, 1, 3, 1, 1, 3, 2]
def baseStart_808884 : Nat := 118140960795 + 808884 * 2 ^ 59
def prefixEnd_808884 : Nat := 4983230072969 + 3 ^ 40 * 808884 * 2
def baseEnd_808884 : Nat := 369196698428016418960015

theorem tailTrace_808884 : CollatzResearch.WordTrace tailWord_808884 prefixEnd_808884 369196698428016418960015 := by
  unfold tailWord_808884
  simp only [CollatzResearch.WordTrace]
  refine ⟨14751211600779444616956853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19668282134372592822609137 14751211600779444616956853)
  ·
    refine ⟨1382926087573072932839705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14751211600779444616956853 1382926087573072932839705)
    ·
      refine ⟨1037194565679804699629779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1382926087573072932839705 1037194565679804699629779)
      ·
        refine ⟨1555791848519707049444669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1037194565679804699629779 1555791848519707049444669)
        ·
          refine ⟨583421943194890143541751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1555791848519707049444669 583421943194890143541751)
          ·
            refine ⟨875132914792335215312627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 583421943194890143541751 875132914792335215312627)
            ·
              refine ⟨1312699372188502822968941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 875132914792335215312627 1312699372188502822968941)
              ·
                refine ⟨492262264570688558613353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1312699372188502822968941 492262264570688558613353)
                ·
                  refine ⟨369196698428016418960015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 492262264570688558613353 369196698428016418960015)
                  ·
                    rfl

theorem cell20_808884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_808884 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_808884 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_808884 prefixEnd_808884 := by exact prefixLift 808884
  have htrace : WordTrace (prefixWord ++ tailWord_808884) baseStart_808884 baseEnd_808884 := by
    simpa [prefixWord, tailWord_808884, baseEnd_808884] using wordTrace_append hprefix tailTrace_808884
  have hstable : (prefixWord ++ tailWord_808884).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808884).length < 2 ^ (prefixWord ++ tailWord_808884).sum := by decide
  have hdescent : baseEnd_808884 < baseStart_808884 := by decide
  rcases family_descends (prefixWord ++ tailWord_808884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808889 : List Nat := [1, 2, 1, 4, 2, 1, 1, 1, 7]
def baseStart_808889 : Nat := 118140960795 + 808889 * 2 ^ 59
def prefixEnd_808889 : Nat := 4983230072969 + 3 ^ 40 * 808889 * 2
def baseEnd_808889 : Nat := 369198980564258623793327

theorem tailTrace_808889 : CollatzResearch.WordTrace tailWord_808889 prefixEnd_808889 369198980564258623793327 := by
  unfold tailWord_808889
  simp only [CollatzResearch.WordTrace]
  refine ⟨29502605566540775087845721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19668403711027183391897147 29502605566540775087845721)
  ·
    refine ⟨22126954174905581315884291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29502605566540775087845721 22126954174905581315884291)
    ·
      refine ⟨33190431262358371973826437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22126954174905581315884291 33190431262358371973826437)
      ·
        refine ⟨6223205861692194745092457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33190431262358371973826437 6223205861692194745092457)
        ·
          refine ⟨4667404396269146058819343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6223205861692194745092457 4667404396269146058819343)
          ·
            refine ⟨7001106594403719088229015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4667404396269146058819343 7001106594403719088229015)
            ·
              refine ⟨10501659891605578632343523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7001106594403719088229015 10501659891605578632343523)
              ·
                refine ⟨15752489837408367948515285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10501659891605578632343523 15752489837408367948515285)
                ·
                  refine ⟨369198980564258623793327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15752489837408367948515285 369198980564258623793327)
                  ·
                    rfl

theorem cell20_808889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 7].length) (baseStart_808889 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_808889 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_808889 prefixEnd_808889 := by exact prefixLift 808889
  have htrace : WordTrace (prefixWord ++ tailWord_808889) baseStart_808889 baseEnd_808889 := by
    simpa [prefixWord, tailWord_808889, baseEnd_808889] using wordTrace_append hprefix tailTrace_808889
  have hstable : (prefixWord ++ tailWord_808889).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808889).length < 2 ^ (prefixWord ++ tailWord_808889).sum := by decide
  have hdescent : baseEnd_808889 < baseStart_808889 := by decide
  rcases family_descends (prefixWord ++ tailWord_808889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808920 : List Nat := [2, 1, 2, 2, 2, 2, 4, 5]
def baseStart_808920 : Nat := 118140960795 + 808920 * 2 ^ 59
def prefixEnd_808920 : Nat := 4983230072969 + 3 ^ 40 * 808920 * 2
def baseEnd_808920 : Nat := 123071043269653431253289

theorem tailTrace_808920 : CollatzResearch.WordTrace tailWord_808920 prefixEnd_808920 123071043269653431253289 := by
  unfold tailWord_808920
  simp only [CollatzResearch.WordTrace]
  refine ⟨14751868114714233691112107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19669157486285644921482809 14751868114714233691112107)
  ·
    refine ⟨22127802172071350536668161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14751868114714233691112107 22127802172071350536668161)
    ·
      refine ⟨16595851629053512902501121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22127802172071350536668161 16595851629053512902501121)
      ·
        refine ⟨12446888721790134676875841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16595851629053512902501121 12446888721790134676875841)
        ·
          refine ⟨9335166541342601007656881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12446888721790134676875841 9335166541342601007656881)
          ·
            refine ⟨7001374906006950755742661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9335166541342601007656881 7001374906006950755742661)
            ·
              refine ⟨1312757794876303266701749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7001374906006950755742661 1312757794876303266701749)
              ·
                refine ⟨123071043269653431253289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1312757794876303266701749 123071043269653431253289)
                ·
                  rfl

theorem cell20_808920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 5].length) (baseStart_808920 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_808920 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_808920 prefixEnd_808920 := by exact prefixLift 808920
  have htrace : WordTrace (prefixWord ++ tailWord_808920) baseStart_808920 baseEnd_808920 := by
    simpa [prefixWord, tailWord_808920, baseEnd_808920] using wordTrace_append hprefix tailTrace_808920
  have hstable : (prefixWord ++ tailWord_808920).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808920).length < 2 ^ (prefixWord ++ tailWord_808920).sum := by decide
  have hdescent : baseEnd_808920 < baseStart_808920 := by decide
  rcases family_descends (prefixWord ++ tailWord_808920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808964 : List Nat := [2, 3, 2, 4, 1, 1, 1, 4, 2]
def baseStart_808964 : Nat := 118140960795 + 808964 * 2 ^ 59
def prefixEnd_808964 : Nat := 4983230072969 + 3 ^ 40 * 808964 * 2
def baseEnd_808964 : Nat := 369233212607891696293021

theorem tailTrace_808964 : CollatzResearch.WordTrace tailWord_808964 prefixEnd_808964 369233212607891696293021 := by
  unfold tailWord_808964
  simp only [CollatzResearch.WordTrace]
  refine ⟨14752670520634531448412973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19670227360846041931217297 14752670520634531448412973)
  ·
    refine ⟨5532251445237949293154865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14752670520634531448412973 5532251445237949293154865)
    ·
      refine ⟨4149188583928461969866149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5532251445237949293154865 4149188583928461969866149)
      ·
        refine ⟨777972859486586619349903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4149188583928461969866149 777972859486586619349903)
        ·
          refine ⟨1166959289229879929024855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 777972859486586619349903 1166959289229879929024855)
          ·
            refine ⟨1750438933844819893537283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1166959289229879929024855 1750438933844819893537283)
            ·
              refine ⟨2625658400767229840305925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1750438933844819893537283 2625658400767229840305925)
              ·
                refine ⟨492310950143855595057361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2625658400767229840305925 492310950143855595057361)
                ·
                  refine ⟨369233212607891696293021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 492310950143855595057361 369233212607891696293021)
                  ·
                    rfl

theorem cell20_808964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 4, 2].length) (baseStart_808964 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_808964 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_808964 prefixEnd_808964 := by exact prefixLift 808964
  have htrace : WordTrace (prefixWord ++ tailWord_808964) baseStart_808964 baseEnd_808964 := by
    simpa [prefixWord, tailWord_808964, baseEnd_808964] using wordTrace_append hprefix tailTrace_808964
  have hstable : (prefixWord ++ tailWord_808964).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808964).length < 2 ^ (prefixWord ++ tailWord_808964).sum := by decide
  have hdescent : baseEnd_808964 < baseStart_808964 := by decide
  rcases family_descends (prefixWord ++ tailWord_808964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808968 : List Nat := [2, 1, 3, 2, 1, 2, 3, 4, 2]
def baseStart_808968 : Nat := 118140960795 + 808968 * 2 ^ 59
def prefixEnd_808968 : Nat := 4983230072969 + 3 ^ 40 * 808968 * 2
def baseEnd_808968 : Nat := 369235038316885460159671

theorem tailTrace_808968 : CollatzResearch.WordTrace tailWord_808968 prefixEnd_808968 369235038316885460159671 := by
  unfold tailWord_808968
  simp only [CollatzResearch.WordTrace]
  refine ⟨14752743466627285789985779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19670324622169714386647705 14752743466627285789985779)
  ·
    refine ⟨22129115199940928684978669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14752743466627285789985779 22129115199940928684978669)
    ·
      refine ⟨8298418199977848256867001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22129115199940928684978669 8298418199977848256867001)
      ·
        refine ⟨6223813649983386192650251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8298418199977848256867001 6223813649983386192650251)
        ·
          refine ⟨9335720474975079288975377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6223813649983386192650251 9335720474975079288975377)
          ·
            refine ⟨7001790356231309466731533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9335720474975079288975377 7001790356231309466731533)
            ·
              refine ⟨2625671383586741050024325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7001790356231309466731533 2625671383586741050024325)
              ·
                refine ⟨492313384422513946879561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2625671383586741050024325 492313384422513946879561)
                ·
                  refine ⟨369235038316885460159671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 492313384422513946879561 369235038316885460159671)
                  ·
                    rfl

theorem cell20_808968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 4, 2].length) (baseStart_808968 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_808968 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_808968 prefixEnd_808968 := by exact prefixLift 808968
  have htrace : WordTrace (prefixWord ++ tailWord_808968) baseStart_808968 baseEnd_808968 := by
    simpa [prefixWord, tailWord_808968, baseEnd_808968] using wordTrace_append hprefix tailTrace_808968
  have hstable : (prefixWord ++ tailWord_808968).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808968).length < 2 ^ (prefixWord ++ tailWord_808968).sum := by decide
  have hdescent : baseEnd_808968 < baseStart_808968 := by decide
  rcases family_descends (prefixWord ++ tailWord_808968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808989 : List Nat := [1, 4, 2, 2, 2, 1, 1, 1, 6]
def baseStart_808989 : Nat := 118140960795 + 808989 * 2 ^ 59
def prefixEnd_808989 : Nat := 4983230072969 + 3 ^ 40 * 808989 * 2
def baseEnd_808989 : Nat := 369244623289102720459585

theorem tailTrace_808989 : CollatzResearch.WordTrace tailWord_808989 prefixEnd_808989 369244623289102720459585 := by
  unfold tailWord_808989
  simp only [CollatzResearch.WordTrace]
  refine ⟨29506252866178492166486021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19670835244118994777657347 29506252866178492166486021)
  ·
    refine ⟨5532422412408467281216129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29506252866178492166486021 5532422412408467281216129)
    ·
      refine ⟨4149316809306350460912097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5532422412408467281216129 4149316809306350460912097)
      ·
        refine ⟨3111987606979762845684073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4149316809306350460912097 3111987606979762845684073)
        ·
          refine ⟨2333990705234822134263055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3111987606979762845684073 2333990705234822134263055)
          ·
            refine ⟨3500986057852233201394583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2333990705234822134263055 3500986057852233201394583)
            ·
              refine ⟨5251479086778349802091875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3500986057852233201394583 5251479086778349802091875)
              ·
                refine ⟨7877218630167524703137813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5251479086778349802091875 7877218630167524703137813)
                ·
                  refine ⟨369244623289102720459585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7877218630167524703137813 369244623289102720459585)
                  ·
                    rfl

theorem cell20_808989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_808989 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_808989 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_808989 prefixEnd_808989 := by exact prefixLift 808989
  have htrace : WordTrace (prefixWord ++ tailWord_808989) baseStart_808989 baseEnd_808989 := by
    simpa [prefixWord, tailWord_808989, baseEnd_808989] using wordTrace_append hprefix tailTrace_808989
  have hstable : (prefixWord ++ tailWord_808989).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808989).length < 2 ^ (prefixWord ++ tailWord_808989).sum := by decide
  have hdescent : baseEnd_808989 < baseStart_808989 := by decide
  rcases family_descends (prefixWord ++ tailWord_808989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809016 : List Nat := [2, 1, 2, 1, 7, 1, 1, 2, 3]
def baseStart_809016 : Nat := 118140960795 + 809016 * 2 ^ 59
def prefixEnd_809016 : Nat := 4983230072969 + 3 ^ 40 * 809016 * 2
def baseEnd_809016 : Nat := 369256946824810626559475

theorem tailTrace_809016 : CollatzResearch.WordTrace tailWord_809016 prefixEnd_809016 369256946824810626559475 := by
  unfold tailWord_809016
  simp only [CollatzResearch.WordTrace]
  refine ⟨14753618818540337888859451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19671491758053783851812601 14753618818540337888859451)
  ·
    refine ⟨22130428227810506833289177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14753618818540337888859451 22130428227810506833289177)
    ·
      refine ⟨16597821170857880124966883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22130428227810506833289177 16597821170857880124966883)
      ·
        refine ⟨24896731756286820187450325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16597821170857880124966883 24896731756286820187450325)
        ·
          refine ⟨583517150537972348143367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 24896731756286820187450325 583517150537972348143367)
          ·
            refine ⟨875275725806958522215051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 583517150537972348143367 875275725806958522215051)
            ·
              refine ⟨1312913588710437783322577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 875275725806958522215051 1312913588710437783322577)
              ·
                refine ⟨984685191532828337491933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1312913588710437783322577 984685191532828337491933)
                ·
                  refine ⟨369256946824810626559475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 984685191532828337491933 369256946824810626559475)
                  ·
                    rfl

theorem cell20_809016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 2, 3].length) (baseStart_809016 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_809016 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_809016 prefixEnd_809016 := by exact prefixLift 809016
  have htrace : WordTrace (prefixWord ++ tailWord_809016) baseStart_809016 baseEnd_809016 := by
    simpa [prefixWord, tailWord_809016, baseEnd_809016] using wordTrace_append hprefix tailTrace_809016
  have hstable : (prefixWord ++ tailWord_809016).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809016).length < 2 ^ (prefixWord ++ tailWord_809016).sum := by decide
  have hdescent : baseEnd_809016 < baseStart_809016 := by decide
  rcases family_descends (prefixWord ++ tailWord_809016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809061 : List Nat := [1, 3, 1, 3, 2, 4, 1, 3, 2]
def baseStart_809061 : Nat := 118140960795 + 809061 * 2 ^ 59
def prefixEnd_809061 : Nat := 4983230072969 + 3 ^ 40 * 809061 * 2
def baseEnd_809061 : Nat := 369277486050990470059291

theorem tailTrace_809061 : CollatzResearch.WordTrace tailWord_809061 prefixEnd_809061 369277486050990470059291 := by
  unfold tailWord_809061
  simp only [CollatzResearch.WordTrace]
  refine ⟨29508878921917648463107037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19672585947945098975404691 29508878921917648463107037)
  ·
    refine ⟨11065829595719118173665139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29508878921917648463107037 11065829595719118173665139)
    ·
      refine ⟨16598744393578677260497709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11065829595719118173665139 16598744393578677260497709)
      ·
        refine ⟨6224529147592003972686641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16598744393578677260497709 6224529147592003972686641)
        ·
          refine ⟨4668396860694002979514981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6224529147592003972686641 4668396860694002979514981)
          ·
            refine ⟨875324411380125558659059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4668396860694002979514981 875324411380125558659059)
            ·
              refine ⟨1312986617070188337988589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 875324411380125558659059 1312986617070188337988589)
              ·
                refine ⟨492369981401320626745721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1312986617070188337988589 492369981401320626745721)
                ·
                  refine ⟨369277486050990470059291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 492369981401320626745721 369277486050990470059291)
                  ·
                    rfl

theorem cell20_809061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 3, 2].length) (baseStart_809061 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_809061 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_809061 prefixEnd_809061 := by exact prefixLift 809061
  have htrace : WordTrace (prefixWord ++ tailWord_809061) baseStart_809061 baseEnd_809061 := by
    simpa [prefixWord, tailWord_809061, baseEnd_809061] using wordTrace_append hprefix tailTrace_809061
  have hstable : (prefixWord ++ tailWord_809061).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809061).length < 2 ^ (prefixWord ++ tailWord_809061).sum := by decide
  have hdescent : baseEnd_809061 < baseStart_809061 := by decide
  rcases family_descends (prefixWord ++ tailWord_809061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809072 : List Nat := [2, 1, 1, 1, 5, 4, 6]
def baseStart_809072 : Nat := 118140960795 + 809072 * 2 ^ 59
def prefixEnd_809072 : Nat := 4983230072969 + 3 ^ 40 * 809072 * 2
def baseEnd_809072 : Nat := 41031389638969257854731

theorem tailTrace_809072 : CollatzResearch.WordTrace tailWord_809072 prefixEnd_809072 41031389638969257854731 := by
  unfold tailWord_809072
  simp only [CollatzResearch.WordTrace]
  refine ⟨14754640062438898670878735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19672853416585198227838313 14754640062438898670878735)
  ·
    refine ⟨22131960093658348006318103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14754640062438898670878735 22131960093658348006318103)
    ·
      refine ⟨33197940140487522009477155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22131960093658348006318103 33197940140487522009477155)
      ·
        refine ⟨49796910210731283014215733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33197940140487522009477155 49796910210731283014215733)
        ·
          refine ⟨4668460332256057782582725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49796910210731283014215733 4668460332256057782582725)
          ·
            refine ⟨875336312298010834234261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4668460332256057782582725 875336312298010834234261)
            ·
              refine ⟨41031389638969257854731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 875336312298010834234261 41031389638969257854731)
              ·
                rfl

theorem cell20_809072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 6].length) (baseStart_809072 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_809072 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_809072 prefixEnd_809072 := by exact prefixLift 809072
  have htrace : WordTrace (prefixWord ++ tailWord_809072) baseStart_809072 baseEnd_809072 := by
    simpa [prefixWord, tailWord_809072, baseEnd_809072] using wordTrace_append hprefix tailTrace_809072
  have hstable : (prefixWord ++ tailWord_809072).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809072).length < 2 ^ (prefixWord ++ tailWord_809072).sum := by decide
  have hdescent : baseEnd_809072 < baseStart_809072 := by decide
  rcases family_descends (prefixWord ++ tailWord_809072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809078 : List Nat := [5, 1, 1, 2, 1, 3, 3, 2, 2]
def baseStart_809078 : Nat := 118140960795 + 809078 * 2 ^ 59
def prefixEnd_809078 : Nat := 4983230072969 + 3 ^ 40 * 809078 * 2
def baseEnd_809078 : Nat := 369285245314213966492555

theorem tailTrace_809078 : CollatzResearch.WordTrace tailWord_809078 prefixEnd_809078 369285245314213966492555 := by
  unfold tailWord_809078
  simp only [CollatzResearch.WordTrace]
  refine ⟨1844343685178503772904743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19672999308570706910983925 1844343685178503772904743)
  ·
    refine ⟨2766515527767755659357115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1844343685178503772904743 2766515527767755659357115)
    ·
      refine ⟨4149773291651633489035673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2766515527767755659357115 4149773291651633489035673)
      ·
        refine ⟨3112329968738725116776755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4149773291651633489035673 3112329968738725116776755)
        ·
          refine ⟨4668494953108087675165133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3112329968738725116776755 4668494953108087675165133)
          ·
            refine ⟨1750685607415532878186925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4668494953108087675165133 1750685607415532878186925)
            ·
              refine ⟨656507102780824829320097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1750685607415532878186925 656507102780824829320097)
              ·
                refine ⟨492380327085618621990073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 656507102780824829320097 492380327085618621990073)
                ·
                  refine ⟨369285245314213966492555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 492380327085618621990073 369285245314213966492555)
                  ·
                    rfl

theorem cell20_809078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 3, 2, 2].length) (baseStart_809078 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_809078 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_809078 prefixEnd_809078 := by exact prefixLift 809078
  have htrace : WordTrace (prefixWord ++ tailWord_809078) baseStart_809078 baseEnd_809078 := by
    simpa [prefixWord, tailWord_809078, baseEnd_809078] using wordTrace_append hprefix tailTrace_809078
  have hstable : (prefixWord ++ tailWord_809078).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809078).length < 2 ^ (prefixWord ++ tailWord_809078).sum := by decide
  have hdescent : baseEnd_809078 < baseStart_809078 := by decide
  rcases family_descends (prefixWord ++ tailWord_809078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809079 : List Nat := [1, 1, 3, 1, 1, 5, 2, 1, 5]
def baseStart_809079 : Nat := 118140960795 + 809079 * 2 ^ 59
def prefixEnd_809079 : Nat := 4983230072969 + 3 ^ 40 * 809079 * 2
def baseEnd_809079 : Nat := 369285701741462407459217

theorem tailTrace_809079 : CollatzResearch.WordTrace tailWord_809079 prefixEnd_809079 369285701741462407459217 := by
  unfold tailWord_809079
  simp only [CollatzResearch.WordTrace]
  refine ⟨29509535435852437537262291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19673023623901625024841527 29509535435852437537262291)
  ·
    refine ⟨44264303153778656305893437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29509535435852437537262291 44264303153778656305893437)
    ·
      refine ⟨16599113682666996114710039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44264303153778656305893437 16599113682666996114710039)
      ·
        refine ⟨24898670524000494172065059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16599113682666996114710039 24898670524000494172065059)
        ·
          refine ⟨37348005786000741258097589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24898670524000494172065059 37348005786000741258097589)
          ·
            refine ⟨3501375542437569492946649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37348005786000741258097589 3501375542437569492946649)
            ·
              refine ⟨2626031656828177119709987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3501375542437569492946649 2626031656828177119709987)
              ·
                refine ⟨3939047485242265679564981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2626031656828177119709987 3939047485242265679564981)
                ·
                  refine ⟨369285701741462407459217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3939047485242265679564981 369285701741462407459217)
                  ·
                    rfl

theorem cell20_809079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 1, 5].length) (baseStart_809079 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_809079 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_809079 prefixEnd_809079 := by exact prefixLift 809079
  have htrace : WordTrace (prefixWord ++ tailWord_809079) baseStart_809079 baseEnd_809079 := by
    simpa [prefixWord, tailWord_809079, baseEnd_809079] using wordTrace_append hprefix tailTrace_809079
  have hstable : (prefixWord ++ tailWord_809079).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809079).length < 2 ^ (prefixWord ++ tailWord_809079).sum := by decide
  have hdescent : baseEnd_809079 < baseStart_809079 := by decide
  rcases family_descends (prefixWord ++ tailWord_809079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809089 : List Nat := [1, 2, 4, 2, 3, 1, 2, 5]
def baseStart_809089 : Nat := 118140960795 + 809089 * 2 ^ 59
def prefixEnd_809089 : Nat := 4983230072969 + 3 ^ 40 * 809089 * 2
def baseEnd_809089 : Nat := 123096755337982272375281

theorem tailTrace_809089 : CollatzResearch.WordTrace tailWord_809089 prefixEnd_809089 123096755337982272375281 := by
  unfold tailWord_809089
  simp only [CollatzResearch.WordTrace]
  refine ⟨29509900165816209245126321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19673266777210806163417547 29509900165816209245126321)
  ·
    refine ⟨22132425124362156933844741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29509900165816209245126321 22132425124362156933844741)
    ·
      refine ⟨4149829710817904425095889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22132425124362156933844741 4149829710817904425095889)
      ·
        refine ⟨3112372283113428318821917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4149829710817904425095889 3112372283113428318821917)
        ·
          refine ⟨1167139606167535619558219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3112372283113428318821917 1167139606167535619558219)
          ·
            refine ⟨1750709409251303429337329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1167139606167535619558219 1750709409251303429337329)
            ·
              refine ⟨1313032056938477572002997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1750709409251303429337329 1313032056938477572002997)
              ·
                refine ⟨123096755337982272375281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1313032056938477572002997 123096755337982272375281)
                ·
                  rfl

theorem cell20_809089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 5].length) (baseStart_809089 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_809089 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_809089 prefixEnd_809089 := by exact prefixLift 809089
  have htrace : WordTrace (prefixWord ++ tailWord_809089) baseStart_809089 baseEnd_809089 := by
    simpa [prefixWord, tailWord_809089, baseEnd_809089] using wordTrace_append hprefix tailTrace_809089
  have hstable : (prefixWord ++ tailWord_809089).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809089).length < 2 ^ (prefixWord ++ tailWord_809089).sum := by decide
  have hdescent : baseEnd_809089 < baseStart_809089 := by decide
  rcases family_descends (prefixWord ++ tailWord_809089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809127 : List Nat := [1, 1, 6, 2, 3, 7]
def baseStart_809127 : Nat := 118140960795 + 809127 * 2 ^ 59
def prefixEnd_809127 : Nat := 4983230072969 + 3 ^ 40 * 809127 * 2
def baseEnd_809127 : Nat := 13678059638866206439223

theorem tailTrace_809127 : CollatzResearch.WordTrace tailWord_809127 prefixEnd_809127 13678059638866206439223 := by
  unfold tailWord_809127
  simp only [CollatzResearch.WordTrace]
  refine ⟨29511286139678541735009635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19674190759785694490006423 29511286139678541735009635)
  ·
    refine ⟨44266929209517812602514453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29511286139678541735009635 44266929209517812602514453)
    ·
      refine ⟨2075012306696147465742865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 44266929209517812602514453 2075012306696147465742865)
      ·
        refine ⟨1556259230022110599307149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2075012306696147465742865 1556259230022110599307149)
        ·
          refine ⟨583597211258291474740181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1556259230022110599307149 583597211258291474740181)
          ·
            refine ⟨13678059638866206439223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 583597211258291474740181 13678059638866206439223)
            ·
              rfl

theorem cell20_809127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 7].length) (baseStart_809127 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_809127 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_809127 prefixEnd_809127 := by exact prefixLift 809127
  have htrace : WordTrace (prefixWord ++ tailWord_809127) baseStart_809127 baseEnd_809127 := by
    simpa [prefixWord, tailWord_809127, baseEnd_809127] using wordTrace_append hprefix tailTrace_809127
  have hstable : (prefixWord ++ tailWord_809127).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809127).length < 2 ^ (prefixWord ++ tailWord_809127).sum := by decide
  have hdescent : baseEnd_809127 < baseStart_809127 := by decide
  rcases family_descends (prefixWord ++ tailWord_809127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809130 : List Nat := [3, 1, 5, 1, 2, 1, 2, 2, 3]
def baseStart_809130 : Nat := 118140960795 + 809130 * 2 ^ 59
def prefixEnd_809130 : Nat := 4983230072969 + 3 ^ 40 * 809130 * 2
def baseEnd_809130 : Nat := 369308979531132896759009

theorem tailTrace_809130 : CollatzResearch.WordTrace tailWord_809130 prefixEnd_809130 369308979531132896759009 := by
  unfold tailWord_809130
  simp only [CollatzResearch.WordTrace]
  refine ⟨7377848889666918311842211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19674263705778448831579229 7377848889666918311842211)
  ·
    refine ⟨11066773334500377467763317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7377848889666918311842211 11066773334500377467763317)
    ·
      refine ⟨1037510000109410387602811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11066773334500377467763317 1037510000109410387602811)
      ·
        refine ⟨1556265000164115581404217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1037510000109410387602811 1556265000164115581404217)
        ·
          refine ⟨1167198750123086686053163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1556265000164115581404217 1167198750123086686053163)
          ·
            refine ⟨1750798125184630029079745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1167198750123086686053163 1750798125184630029079745)
            ·
              refine ⟨1313098593888472521809809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1750798125184630029079745 1313098593888472521809809)
              ·
                refine ⟨984823945416354391357357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1313098593888472521809809 984823945416354391357357)
                ·
                  refine ⟨369308979531132896759009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 984823945416354391357357 369308979531132896759009)
                  ·
                    rfl

theorem cell20_809130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 2, 3].length) (baseStart_809130 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_809130 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_809130 prefixEnd_809130 := by exact prefixLift 809130
  have htrace : WordTrace (prefixWord ++ tailWord_809130) baseStart_809130 baseEnd_809130 := by
    simpa [prefixWord, tailWord_809130, baseEnd_809130] using wordTrace_append hprefix tailTrace_809130
  have hstable : (prefixWord ++ tailWord_809130).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809130).length < 2 ^ (prefixWord ++ tailWord_809130).sum := by decide
  have hdescent : baseEnd_809130 < baseStart_809130 := by decide
  rcases family_descends (prefixWord ++ tailWord_809130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809137 : List Nat := [1, 2, 2, 5, 2, 1, 1, 4, 2]
def baseStart_809137 : Nat := 118140960795 + 809137 * 2 ^ 59
def prefixEnd_809137 : Nat := 4983230072969 + 3 ^ 40 * 809137 * 2
def baseEnd_809137 : Nat := 369312174521871983525647

theorem tailTrace_809137 : CollatzResearch.WordTrace tailWord_809137 prefixEnd_809137 369312174521871983525647 := by
  unfold tailWord_809137
  simp only [CollatzResearch.WordTrace]
  refine ⟨29511650869642313442873665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19674433913094875628582443 29511650869642313442873665)
  ·
    refine ⟨22133738152231735082155249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29511650869642313442873665 22133738152231735082155249)
    ·
      refine ⟨16600303614173801311616437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22133738152231735082155249 16600303614173801311616437)
      ·
        refine ⟨1556278463828793872964041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16600303614173801311616437 1556278463828793872964041)
        ·
          refine ⟨1167208847871595404723031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1556278463828793872964041 1167208847871595404723031)
          ·
            refine ⟨1750813271807393107084547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1167208847871595404723031 1750813271807393107084547)
            ·
              refine ⟨2626219907711089660626821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1750813271807393107084547 2626219907711089660626821)
              ·
                refine ⟨492416232695829311367529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2626219907711089660626821 492416232695829311367529)
                ·
                  refine ⟨369312174521871983525647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 492416232695829311367529 369312174521871983525647)
                  ·
                    rfl

theorem cell20_809137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 4, 2].length) (baseStart_809137 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_809137 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_809137 prefixEnd_809137 := by exact prefixLift 809137
  have htrace : WordTrace (prefixWord ++ tailWord_809137) baseStart_809137 baseEnd_809137 := by
    simpa [prefixWord, tailWord_809137, baseEnd_809137] using wordTrace_append hprefix tailTrace_809137
  have hstable : (prefixWord ++ tailWord_809137).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809137).length < 2 ^ (prefixWord ++ tailWord_809137).sum := by decide
  have hdescent : baseEnd_809137 < baseStart_809137 := by decide
  rcases family_descends (prefixWord ++ tailWord_809137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809140 : List Nat := [2, 5, 3, 1, 1, 2, 1, 5]
def baseStart_809140 : Nat := 118140960795 + 809140 * 2 ^ 59
def prefixEnd_809140 : Nat := 4983230072969 + 3 ^ 40 * 809140 * 2
def baseEnd_809140 : Nat := 123104514601205768808545

theorem tailTrace_809140 : CollatzResearch.WordTrace tailWord_809140 prefixEnd_809140 123104514601205768808545 := by
  unfold tailWord_809140
  simp only [CollatzResearch.WordTrace]
  refine ⟨14755880144315722477616437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19674506859087629970155249 14755880144315722477616437)
  ·
    refine ⟨1383363763529598982276541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14755880144315722477616437 1383363763529598982276541)
    ·
      refine ⟨518761411323599618353703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1383363763529598982276541 518761411323599618353703)
      ·
        refine ⟨778142116985399427530555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 518761411323599618353703 778142116985399427530555)
        ·
          refine ⟨1167213175478099141295833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 778142116985399427530555 1167213175478099141295833)
          ·
            refine ⟨875409881608574355971875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1167213175478099141295833 875409881608574355971875)
            ·
              refine ⟨1313114822412861533957813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 875409881608574355971875 1313114822412861533957813)
              ·
                refine ⟨123104514601205768808545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1313114822412861533957813 123104514601205768808545)
                ·
                  rfl

theorem cell20_809140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 5].length) (baseStart_809140 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_809140 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_809140 prefixEnd_809140 := by exact prefixLift 809140
  have htrace : WordTrace (prefixWord ++ tailWord_809140) baseStart_809140 baseEnd_809140 := by
    simpa [prefixWord, tailWord_809140, baseEnd_809140] using wordTrace_append hprefix tailTrace_809140
  have hstable : (prefixWord ++ tailWord_809140).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809140).length < 2 ^ (prefixWord ++ tailWord_809140).sum := by decide
  have hdescent : baseEnd_809140 < baseStart_809140 := by decide
  rcases family_descends (prefixWord ++ tailWord_809140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809169 : List Nat := [1, 2, 2, 1, 2, 2, 2, 8]
def baseStart_809169 : Nat := 118140960795 + 809169 * 2 ^ 59
def prefixEnd_809169 : Nat := 4983230072969 + 3 ^ 40 * 809169 * 2
def baseEnd_809169 : Nat := 123108926731274031486283

theorem tailTrace_809169 : CollatzResearch.WordTrace tailWord_809169 prefixEnd_809169 123108926731274031486283 := by
  unfold tailWord_809169
  simp only [CollatzResearch.WordTrace]
  refine ⟨29512818005526382908038561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19675212003684255272025707 29512818005526382908038561)
  ·
    refine ⟨22134613504144787181028921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29512818005526382908038561 22134613504144787181028921)
    ·
      refine ⟨16600960128108590385771691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22134613504144787181028921 16600960128108590385771691)
      ·
        refine ⟨24901440192162885578657537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16600960128108590385771691 24901440192162885578657537)
        ·
          refine ⟨18676080144122164183993153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24901440192162885578657537 18676080144122164183993153)
          ·
            refine ⟨14007060108091623137994865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18676080144122164183993153 14007060108091623137994865)
            ·
              refine ⟨10505295081068717353496149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14007060108091623137994865 10505295081068717353496149)
              ·
                refine ⟨123108926731274031486283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10505295081068717353496149 123108926731274031486283)
                ·
                  rfl

theorem cell20_809169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 8].length) (baseStart_809169 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_809169 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_809169 prefixEnd_809169 := by exact prefixLift 809169
  have htrace : WordTrace (prefixWord ++ tailWord_809169) baseStart_809169 baseEnd_809169 := by
    simpa [prefixWord, tailWord_809169, baseEnd_809169] using wordTrace_append hprefix tailTrace_809169
  have hstable : (prefixWord ++ tailWord_809169).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809169).length < 2 ^ (prefixWord ++ tailWord_809169).sum := by decide
  have hdescent : baseEnd_809169 < baseStart_809169 := by decide
  rcases family_descends (prefixWord ++ tailWord_809169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809179 : List Nat := [1, 1, 1, 1, 1, 1, 1, 11, 2]
def baseStart_809179 : Nat := 118140960795 + 809179 * 2 ^ 59
def prefixEnd_809179 : Nat := 4983230072969 + 3 ^ 40 * 809179 * 2
def baseEnd_809179 : Nat := 369331344466306504125475

theorem tailTrace_809179 : CollatzResearch.WordTrace tailWord_809179 prefixEnd_809179 369331344466306504125475 := by
  unfold tailWord_809179
  simp only [CollatzResearch.WordTrace]
  refine ⟨29513182735490154615902591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19675455156993436410601727 29513182735490154615902591)
  ·
    refine ⟨44269774103235231923853887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29513182735490154615902591 44269774103235231923853887)
    ·
      refine ⟨66404661154852847885780831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44269774103235231923853887 66404661154852847885780831)
      ·
        refine ⟨99606991732279271828671247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66404661154852847885780831 99606991732279271828671247)
        ·
          refine ⟨149410487598418907743006871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99606991732279271828671247 149410487598418907743006871)
          ·
            refine ⟨224115731397628361614510307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149410487598418907743006871 224115731397628361614510307)
            ·
              refine ⟨336173597096442542421765461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 224115731397628361614510307 336173597096442542421765461)
              ·
                refine ⟨492441792621742005500633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 336173597096442542421765461 492441792621742005500633)
                ·
                  refine ⟨369331344466306504125475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 492441792621742005500633 369331344466306504125475)
                  ·
                    rfl

theorem cell20_809179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 11, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 11, 2].length) (baseStart_809179 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_809179 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_809179 prefixEnd_809179 := by exact prefixLift 809179
  have htrace : WordTrace (prefixWord ++ tailWord_809179) baseStart_809179 baseEnd_809179 := by
    simpa [prefixWord, tailWord_809179, baseEnd_809179] using wordTrace_append hprefix tailTrace_809179
  have hstable : (prefixWord ++ tailWord_809179).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809179).length < 2 ^ (prefixWord ++ tailWord_809179).sum := by decide
  have hdescent : baseEnd_809179 < baseStart_809179 := by decide
  rcases family_descends (prefixWord ++ tailWord_809179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809189 : List Nat := [1, 3, 1, 4, 2, 3, 1, 2, 3]
def baseStart_809189 : Nat := 118140960795 + 809189 * 2 ^ 59
def prefixEnd_809189 : Nat := 4983230072969 + 3 ^ 40 * 809189 * 2
def baseEnd_809189 : Nat := 369335908738790913792101

theorem tailTrace_809189 : CollatzResearch.WordTrace tailWord_809189 prefixEnd_809189 369335908738790913792101 := by
  unfold tailWord_809189
  simp only [CollatzResearch.WordTrace]
  refine ⟨29513547465453926323766621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19675698310302617549177747 29513547465453926323766621)
  ·
    refine ⟨11067580299545222371412483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29513547465453926323766621 11067580299545222371412483)
    ·
      refine ⟨16601370449317833557118725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11067580299545222371412483 16601370449317833557118725)
      ·
        refine ⟨3112756959247093791959761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16601370449317833557118725 3112756959247093791959761)
        ·
          refine ⟨2334567719435320343969821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3112756959247093791959761 2334567719435320343969821)
          ·
            refine ⟨875462894788245128988683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2334567719435320343969821 875462894788245128988683)
            ·
              refine ⟨1313194342182367693483025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 875462894788245128988683 1313194342182367693483025)
              ·
                refine ⟨984895756636775770112269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1313194342182367693483025 984895756636775770112269)
                ·
                  refine ⟨369335908738790913792101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 984895756636775770112269 369335908738790913792101)
                  ·
                    rfl

theorem cell20_809189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 2, 3].length) (baseStart_809189 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_809189 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_809189 prefixEnd_809189 := by exact prefixLift 809189
  have htrace : WordTrace (prefixWord ++ tailWord_809189) baseStart_809189 baseEnd_809189 := by
    simpa [prefixWord, tailWord_809189, baseEnd_809189] using wordTrace_append hprefix tailTrace_809189
  have hstable : (prefixWord ++ tailWord_809189).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809189).length < 2 ^ (prefixWord ++ tailWord_809189).sum := by decide
  have hdescent : baseEnd_809189 < baseStart_809189 := by decide
  rcases family_descends (prefixWord ++ tailWord_809189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809220 : List Nat := [2, 3, 2, 2, 3, 2, 2, 4]
def baseStart_809220 : Nat := 118140960795 + 809220 * 2 ^ 59
def prefixEnd_809220 : Nat := 4983230072969 + 3 ^ 40 * 809220 * 2
def baseEnd_809220 : Nat := 123116685994497527919547

theorem tailTrace_809220 : CollatzResearch.WordTrace tailWord_809220 prefixEnd_809220 123116685994497527919547 := by
  unfold tailWord_809220
  simp only [CollatzResearch.WordTrace]
  refine ⟨14757339064170809309072557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19676452085561079078763409 14757339064170809309072557)
  ·
    refine ⟨5534002149064053490902209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14757339064170809309072557 5534002149064053490902209)
    ·
      refine ⟨4150501611798040118176657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5534002149064053490902209 4150501611798040118176657)
      ·
        refine ⟨3112876208848530088632493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4150501611798040118176657 3112876208848530088632493)
        ·
          refine ⟨1167328578318198783237185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3112876208848530088632493 1167328578318198783237185)
          ·
            refine ⟨875496433738649087427889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1167328578318198783237185 875496433738649087427889)
            ·
              refine ⟨656622325303986815570917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 875496433738649087427889 656622325303986815570917)
              ·
                refine ⟨123116685994497527919547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 656622325303986815570917 123116685994497527919547)
                ·
                  rfl

theorem cell20_809220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 2, 4].length) (baseStart_809220 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_809220 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_809220 prefixEnd_809220 := by exact prefixLift 809220
  have htrace : WordTrace (prefixWord ++ tailWord_809220) baseStart_809220 baseEnd_809220 := by
    simpa [prefixWord, tailWord_809220, baseEnd_809220] using wordTrace_append hprefix tailTrace_809220
  have hstable : (prefixWord ++ tailWord_809220).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809220).length < 2 ^ (prefixWord ++ tailWord_809220).sum := by decide
  have hdescent : baseEnd_809220 < baseStart_809220 := by decide
  rcases family_descends (prefixWord ++ tailWord_809220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809224 : List Nat := [2, 1, 3, 2, 3, 2, 1, 6]
def baseStart_809224 : Nat := 118140960795 + 809224 * 2 ^ 59
def prefixEnd_809224 : Nat := 4983230072969 + 3 ^ 40 * 809224 * 2
def baseEnd_809224 : Nat := 123117294564162115875097

theorem tailTrace_809224 : CollatzResearch.WordTrace tailWord_809224 prefixEnd_809224 123117294564162115875097 := by
  unfold tailWord_809224
  simp only [CollatzResearch.WordTrace]
  refine ⟨14757412010163563650645363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19676549346884751534193817 14757412010163563650645363)
  ·
    refine ⟨22136118015245345475968045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14757412010163563650645363 22136118015245345475968045)
    ·
      refine ⟨8301044255717004553488017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22136118015245345475968045 8301044255717004553488017)
      ·
        refine ⟨6225783191787753415116013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8301044255717004553488017 6225783191787753415116013)
        ·
          refine ⟨2334668696920407530668505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6225783191787753415116013 2334668696920407530668505)
          ·
            refine ⟨1751001522690305648001379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2334668696920407530668505 1751001522690305648001379)
            ·
              refine ⟨2626502284035458472002069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1751001522690305648001379 2626502284035458472002069)
              ·
                refine ⟨123117294564162115875097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2626502284035458472002069 123117294564162115875097)
                ·
                  rfl

theorem cell20_809224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 6].length) (baseStart_809224 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_809224 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_809224 prefixEnd_809224 := by exact prefixLift 809224
  have htrace : WordTrace (prefixWord ++ tailWord_809224) baseStart_809224 baseEnd_809224 := by
    simpa [prefixWord, tailWord_809224, baseEnd_809224] using wordTrace_append hprefix tailTrace_809224
  have hstable : (prefixWord ++ tailWord_809224).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809224).length < 2 ^ (prefixWord ++ tailWord_809224).sum := by decide
  have hdescent : baseEnd_809224 < baseStart_809224 := by decide
  rcases family_descends (prefixWord ++ tailWord_809224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809261 : List Nat := [1, 5, 3, 1, 2, 2, 2, 1, 3]
def baseStart_809261 : Nat := 118140960795 + 809261 * 2 ^ 59
def prefixEnd_809261 : Nat := 4983230072969 + 3 ^ 40 * 809261 * 2
def baseEnd_809261 : Nat := 369368771500678663391807

theorem tailTrace_809261 : CollatzResearch.WordTrace tailWord_809261 prefixEnd_809261 369368771500678663391807 := by
  unfold tailWord_809261
  simp only [CollatzResearch.WordTrace]
  refine ⟨29516173521193082620387637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19677449014128721746925091 29516173521193082620387637)
  ·
    refine ⟨2767141267611851495661341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29516173521193082620387637 2767141267611851495661341)
    ·
      refine ⟨1037677975354444310873003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2767141267611851495661341 1037677975354444310873003)
      ·
        refine ⟨1556516963031666466309505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1037677975354444310873003 1556516963031666466309505)
        ·
          refine ⟨1167387722273749849732129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1556516963031666466309505 1167387722273749849732129)
          ·
            refine ⟨875540791705312387299097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1167387722273749849732129 875540791705312387299097)
            ·
              refine ⟨656655593778984290474323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 875540791705312387299097 656655593778984290474323)
              ·
                refine ⟨984983390668476435711485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 656655593778984290474323 984983390668476435711485)
                ·
                  refine ⟨369368771500678663391807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 984983390668476435711485 369368771500678663391807)
                  ·
                    rfl

theorem cell20_809261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 2, 1, 3].length) (baseStart_809261 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_809261 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_809261 prefixEnd_809261 := by exact prefixLift 809261
  have htrace : WordTrace (prefixWord ++ tailWord_809261) baseStart_809261 baseEnd_809261 := by
    simpa [prefixWord, tailWord_809261, baseEnd_809261] using wordTrace_append hprefix tailTrace_809261
  have hstable : (prefixWord ++ tailWord_809261).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809261).length < 2 ^ (prefixWord ++ tailWord_809261).sum := by decide
  have hdescent : baseEnd_809261 < baseStart_809261 := by decide
  rcases family_descends (prefixWord ++ tailWord_809261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809276 : List Nat := [2, 2, 2, 2, 1, 2, 2, 1, 6]
def baseStart_809276 : Nat := 118140960795 + 809276 * 2 ^ 59
def prefixEnd_809276 : Nat := 4983230072969 + 3 ^ 40 * 809276 * 2
def baseEnd_809276 : Nat := 369375617909405277891745

theorem tailTrace_809276 : CollatzResearch.WordTrace tailWord_809276 prefixEnd_809276 369375617909405277891745 := by
  unfold tailWord_809276
  simp only [CollatzResearch.WordTrace]
  refine ⟨14758360308069370091091841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19677813744092493454789121 14758360308069370091091841)
  ·
    refine ⟨11068770231052027568318881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14758360308069370091091841 11068770231052027568318881)
    ·
      refine ⟨8301577673289020676239161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11068770231052027568318881 8301577673289020676239161)
      ·
        refine ⟨6226183254966765507179371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8301577673289020676239161 6226183254966765507179371)
        ·
          refine ⟨9339274882450148260769057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6226183254966765507179371 9339274882450148260769057)
          ·
            refine ⟨7004456161837611195576793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9339274882450148260769057 7004456161837611195576793)
            ·
              refine ⟨5253342121378208396682595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7004456161837611195576793 5253342121378208396682595)
              ·
                refine ⟨7880013182067312595023893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5253342121378208396682595 7880013182067312595023893)
                ·
                  refine ⟨369375617909405277891745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7880013182067312595023893 369375617909405277891745)
                  ·
                    rfl

theorem cell20_809276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 6].length) (baseStart_809276 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_809276 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_809276 prefixEnd_809276 := by exact prefixLift 809276
  have htrace : WordTrace (prefixWord ++ tailWord_809276) baseStart_809276 baseEnd_809276 := by
    simpa [prefixWord, tailWord_809276, baseEnd_809276] using wordTrace_append hprefix tailTrace_809276
  have hstable : (prefixWord ++ tailWord_809276).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809276).length < 2 ^ (prefixWord ++ tailWord_809276).sum := by decide
  have hdescent : baseEnd_809276 < baseStart_809276 := by decide
  rcases family_descends (prefixWord ++ tailWord_809276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809283 : List Nat := [1, 1, 1, 3, 1, 3, 4, 6]
def baseStart_809283 : Nat := 118140960795 + 809283 * 2 ^ 59
def prefixEnd_809283 : Nat := 4983230072969 + 3 ^ 40 * 809283 * 2
def baseEnd_809283 : Nat := 123126270966714788219461

theorem tailTrace_809283 : CollatzResearch.WordTrace tailWord_809283 prefixEnd_809283 123126270966714788219461 := by
  unfold tailWord_809283
  simp only [CollatzResearch.WordTrace]
  refine ⟨29516975927113380377688503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19677983951408920251792335 29516975927113380377688503)
  ·
    refine ⟨44275463890670070566532755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29516975927113380377688503 44275463890670070566532755)
    ·
      refine ⟨66413195836005105849799133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44275463890670070566532755 66413195836005105849799133)
      ·
        refine ⟨24904948438501914693674675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66413195836005105849799133 24904948438501914693674675)
        ·
          refine ⟨37357422657752872040512013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24904948438501914693674675 37357422657752872040512013)
          ·
            refine ⟨14009033496657327015192005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37357422657752872040512013 14009033496657327015192005)
            ·
              refine ⟨2626693780623248815348501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14009033496657327015192005 2626693780623248815348501)
              ·
                refine ⟨123126270966714788219461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2626693780623248815348501 123126270966714788219461)
                ·
                  rfl

theorem cell20_809283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 6].length) (baseStart_809283 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_809283 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_809283 prefixEnd_809283 := by exact prefixLift 809283
  have htrace : WordTrace (prefixWord ++ tailWord_809283) baseStart_809283 baseEnd_809283 := by
    simpa [prefixWord, tailWord_809283, baseEnd_809283] using wordTrace_append hprefix tailTrace_809283
  have hstable : (prefixWord ++ tailWord_809283).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809283).length < 2 ^ (prefixWord ++ tailWord_809283).sum := by decide
  have hdescent : baseEnd_809283 < baseStart_809283 := by decide
  rcases family_descends (prefixWord ++ tailWord_809283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809348 : List Nat := [2, 3, 2, 1, 1, 2, 4, 3, 2]
def baseStart_809348 : Nat := 118140960795 + 809348 * 2 ^ 59
def prefixEnd_809348 : Nat := 4983230072969 + 3 ^ 40 * 809348 * 2
def baseEnd_809348 : Nat := 369408480671293027491451

theorem tailTrace_809348 : CollatzResearch.WordTrace tailWord_809348 prefixEnd_809348 369408480671293027491451 := by
  unfold tailWord_809348
  simp only [CollatzResearch.WordTrace]
  refine ⟨14759673335938948239402349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19679564447918597652536465 14759673335938948239402349)
  ·
    refine ⟨5534877500977105589775881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14759673335938948239402349 5534877500977105589775881)
    ·
      refine ⟨4151158125732829192331911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5534877500977105589775881 4151158125732829192331911)
      ·
        refine ⟨6226737188599243788497867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4151158125732829192331911 6226737188599243788497867)
        ·
          refine ⟨9340105782898865682746801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6226737188599243788497867 9340105782898865682746801)
          ·
            refine ⟨7005079337174149262060101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9340105782898865682746801 7005079337174149262060101)
            ·
              refine ⟨1313452375720152986636269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7005079337174149262060101 1313452375720152986636269)
              ·
                refine ⟨492544640895057369988601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1313452375720152986636269 492544640895057369988601)
                ·
                  refine ⟨369408480671293027491451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 492544640895057369988601 369408480671293027491451)
                  ·
                    rfl

theorem cell20_809348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 3, 2].length) (baseStart_809348 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_809348 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_809348 prefixEnd_809348 := by exact prefixLift 809348
  have htrace : WordTrace (prefixWord ++ tailWord_809348) baseStart_809348 baseEnd_809348 := by
    simpa [prefixWord, tailWord_809348, baseEnd_809348] using wordTrace_append hprefix tailTrace_809348
  have hstable : (prefixWord ++ tailWord_809348).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809348).length < 2 ^ (prefixWord ++ tailWord_809348).sum := by decide
  have hdescent : baseEnd_809348 < baseStart_809348 := by decide
  rcases family_descends (prefixWord ++ tailWord_809348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809352 : List Nat := [2, 1, 3, 3, 1, 1, 1, 2, 6]
def baseStart_809352 : Nat := 118140960795 + 809352 * 2 ^ 59
def prefixEnd_809352 : Nat := 4983230072969 + 3 ^ 40 * 809352 * 2
def baseEnd_809352 : Nat := 369410306380286791358101

theorem tailTrace_809352 : CollatzResearch.WordTrace tailWord_809352 prefixEnd_809352 369410306380286791358101 := by
  unfold tailWord_809352
  simp only [CollatzResearch.WordTrace]
  refine ⟨14759746281931702580975155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19679661709242270107966873 14759746281931702580975155)
  ·
    refine ⟨22139619422897553871462733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14759746281931702580975155 22139619422897553871462733)
    ·
      refine ⟨8302357283586582701798525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22139619422897553871462733 8302357283586582701798525)
      ·
        refine ⟨3113383981344968513174447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8302357283586582701798525 3113383981344968513174447)
        ·
          refine ⟨4670075972017452769761671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3113383981344968513174447 4670075972017452769761671)
          ·
            refine ⟨7005113958026179154642507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4670075972017452769761671 7005113958026179154642507)
            ·
              refine ⟨10507670937039268731963761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7005113958026179154642507 10507670937039268731963761)
              ·
                refine ⟨7880753202779451548972821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10507670937039268731963761 7880753202779451548972821)
                ·
                  refine ⟨369410306380286791358101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7880753202779451548972821 369410306380286791358101)
                  ·
                    rfl

theorem cell20_809352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 6].length) (baseStart_809352 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_809352 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_809352 prefixEnd_809352 := by exact prefixLift 809352
  have htrace : WordTrace (prefixWord ++ tailWord_809352) baseStart_809352 baseEnd_809352 := by
    simpa [prefixWord, tailWord_809352, baseEnd_809352] using wordTrace_append hprefix tailTrace_809352
  have hstable : (prefixWord ++ tailWord_809352).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809352).length < 2 ^ (prefixWord ++ tailWord_809352).sum := by decide
  have hdescent : baseEnd_809352 < baseStart_809352 := by decide
  rcases family_descends (prefixWord ++ tailWord_809352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809369 : List Nat := [1, 2, 1, 2, 1, 4, 1, 6, 2]
def baseStart_809369 : Nat := 118140960795 + 809369 * 2 ^ 59
def prefixEnd_809369 : Nat := 4983230072969 + 3 ^ 40 * 809369 * 2
def baseEnd_809369 : Nat := 369418065643510287791365

theorem tailTrace_809369 : CollatzResearch.WordTrace tailWord_809369 prefixEnd_809369 369418065643510287791365 := by
  unfold tailWord_809369
  simp only [CollatzResearch.WordTrace]
  refine ⟨29520112604801817065319161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19680075069867878043546107 29520112604801817065319161)
  ·
    refine ⟨22140084453601362798989371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29520112604801817065319161 22140084453601362798989371)
    ·
      refine ⟨33210126680402044198484057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22140084453601362798989371 33210126680402044198484057)
      ·
        refine ⟨24907595010301533148863043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33210126680402044198484057 24907595010301533148863043)
        ·
          refine ⟨37361392515452299723294565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24907595010301533148863043 37361392515452299723294565)
          ·
            refine ⟨7005261096647306198117731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37361392515452299723294565 7005261096647306198117731)
            ·
              refine ⟨10507891644970959297176597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7005261096647306198117731 10507891644970959297176597)
              ·
                refine ⟨492557420858013717055153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10507891644970959297176597 492557420858013717055153)
                ·
                  refine ⟨369418065643510287791365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 492557420858013717055153 369418065643510287791365)
                  ·
                    rfl

theorem cell20_809369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 6, 2].length) (baseStart_809369 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_809369 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_809369 prefixEnd_809369 := by exact prefixLift 809369
  have htrace : WordTrace (prefixWord ++ tailWord_809369) baseStart_809369 baseEnd_809369 := by
    simpa [prefixWord, tailWord_809369, baseEnd_809369] using wordTrace_append hprefix tailTrace_809369
  have hstable : (prefixWord ++ tailWord_809369).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809369).length < 2 ^ (prefixWord ++ tailWord_809369).sum := by decide
  have hdescent : baseEnd_809369 < baseStart_809369 := by decide
  rcases family_descends (prefixWord ++ tailWord_809369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809389 : List Nat := [1, 5, 2, 2, 3, 1, 2, 4]
def baseStart_809389 : Nat := 118140960795 + 809389 * 2 ^ 59
def prefixEnd_809389 : Nat := 4983230072969 + 3 ^ 40 * 809389 * 2
def baseEnd_809389 : Nat := 123142398062826369041539

theorem tailTrace_809389 : CollatzResearch.WordTrace tailWord_809389 prefixEnd_809389 123142398062826369041539 := by
  unfold tailWord_809389
  simp only [CollatzResearch.WordTrace]
  refine ⟨29520842064729360481047221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19680561376486240320698147 29520842064729360481047221)
  ·
    refine ⟨2767578943568377545098177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29520842064729360481047221 2767578943568377545098177)
    ·
      refine ⟨2075684207676283158823633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2767578943568377545098177 2075684207676283158823633)
      ·
        refine ⟨1556763155757212369117725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2075684207676283158823633 1556763155757212369117725)
        ·
          refine ⟨583786183408954638419147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1556763155757212369117725 583786183408954638419147)
          ·
            refine ⟨875679275113431957628721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 583786183408954638419147 875679275113431957628721)
            ·
              refine ⟨656759456335073968221541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 875679275113431957628721 656759456335073968221541)
              ·
                refine ⟨123142398062826369041539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 656759456335073968221541 123142398062826369041539)
                ·
                  rfl

theorem cell20_809389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 2, 4].length) (baseStart_809389 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_809389 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_809389 prefixEnd_809389 := by exact prefixLift 809389
  have htrace : WordTrace (prefixWord ++ tailWord_809389) baseStart_809389 baseEnd_809389 := by
    simpa [prefixWord, tailWord_809389, baseEnd_809389] using wordTrace_append hprefix tailTrace_809389
  have hstable : (prefixWord ++ tailWord_809389).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809389).length < 2 ^ (prefixWord ++ tailWord_809389).sum := by decide
  have hdescent : baseEnd_809389 < baseStart_809389 := by decide
  rcases family_descends (prefixWord ++ tailWord_809389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809393 : List Nat := [1, 2, 2, 4, 1, 4, 2, 4]
def baseStart_809393 : Nat := 118140960795 + 809393 * 2 ^ 59
def prefixEnd_809393 : Nat := 4983230072969 + 3 ^ 40 * 809393 * 2
def baseEnd_809393 : Nat := 123143006632490956997089

theorem tailTrace_809393 : CollatzResearch.WordTrace tailWord_809393 prefixEnd_809393 123143006632490956997089 := by
  unfold tailWord_809393
  simp only [CollatzResearch.WordTrace]
  refine ⟨29520987956714869164192833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19680658637809912776128555 29520987956714869164192833)
  ·
    refine ⟨22140740967536151873144625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29520987956714869164192833 22140740967536151873144625)
    ·
      refine ⟨16605555725652113904858469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22140740967536151873144625 16605555725652113904858469)
      ·
        refine ⟨3113541698559771357160963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16605555725652113904858469 3113541698559771357160963)
        ·
          refine ⟨4670312547839657035741445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3113541698559771357160963 4670312547839657035741445)
          ·
            refine ⟨875683602719935694201521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4670312547839657035741445 875683602719935694201521)
            ·
              refine ⟨656762702039951770651141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 875683602719935694201521 656762702039951770651141)
              ·
                refine ⟨123143006632490956997089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 656762702039951770651141 123143006632490956997089)
                ·
                  rfl

theorem cell20_809393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 2, 4].length) (baseStart_809393 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_809393 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_809393 prefixEnd_809393 := by exact prefixLift 809393
  have htrace : WordTrace (prefixWord ++ tailWord_809393) baseStart_809393 baseEnd_809393 := by
    simpa [prefixWord, tailWord_809393, baseEnd_809393] using wordTrace_append hprefix tailTrace_809393
  have hstable : (prefixWord ++ tailWord_809393).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809393).length < 2 ^ (prefixWord ++ tailWord_809393).sum := by decide
  have hdescent : baseEnd_809393 < baseStart_809393 := by decide
  rcases family_descends (prefixWord ++ tailWord_809393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809462 : List Nat := [5, 1, 1, 1, 2, 1, 2, 5, 2]
def baseStart_809462 : Nat := 118140960795 + 809462 * 2 ^ 59
def prefixEnd_809462 : Nat := 4983230072969 + 3 ^ 40 * 809462 * 2
def baseEnd_809462 : Nat := 369460513377615297690985

theorem tailTrace_809462 : CollatzResearch.WordTrace tailWord_809462 prefixEnd_809462 369460513377615297690985 := by
  unfold tailWord_809462
  simp only [CollatzResearch.WordTrace]
  refine ⟨1845219037091555871778415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19682336395643262632303093 1845219037091555871778415)
  ·
    refine ⟨2767828555637333807667623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1845219037091555871778415 2767828555637333807667623)
    ·
      refine ⟨4151742833456000711501435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2767828555637333807667623 4151742833456000711501435)
      ·
        refine ⟨6227614250184001067252153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4151742833456000711501435 6227614250184001067252153)
        ·
          refine ⟨4670710687638000800439115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6227614250184001067252153 4670710687638000800439115)
          ·
            refine ⟨7006066031457001200658673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4670710687638000800439115 7006066031457001200658673)
            ·
              refine ⟨5254549523592750900494005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7006066031457001200658673 5254549523592750900494005)
              ·
                refine ⟨492614017836820396921313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5254549523592750900494005 492614017836820396921313)
                ·
                  refine ⟨369460513377615297690985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 492614017836820396921313 369460513377615297690985)
                  ·
                    rfl

theorem cell20_809462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 5, 2].length) (baseStart_809462 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_809462 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_809462 prefixEnd_809462 := by exact prefixLift 809462
  have htrace : WordTrace (prefixWord ++ tailWord_809462) baseStart_809462 baseEnd_809462 := by
    simpa [prefixWord, tailWord_809462, baseEnd_809462] using wordTrace_append hprefix tailTrace_809462
  have hstable : (prefixWord ++ tailWord_809462).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809462).length < 2 ^ (prefixWord ++ tailWord_809462).sum := by decide
  have hdescent : baseEnd_809462 < baseStart_809462 := by decide
  rcases family_descends (prefixWord ++ tailWord_809462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809473 : List Nat := [1, 2, 4, 1, 3, 9]
def baseStart_809473 : Nat := 118140960795 + 809473 * 2 ^ 59
def prefixEnd_809473 : Nat := 4983230072969 + 3 ^ 40 * 809473 * 2
def baseEnd_809473 : Nat := 13683908669531412900899

theorem tailTrace_809473 : CollatzResearch.WordTrace tailWord_809473 prefixEnd_809473 13683908669531412900899 := by
  unfold tailWord_809473
  simp only [CollatzResearch.WordTrace]
  refine ⟨29523905796425042827105073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19682603864283361884736715 29523905796425042827105073)
  ·
    refine ⟨22142929347318782120328805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29523905796425042827105073 22142929347318782120328805)
    ·
      refine ⟨4151799252622271647561651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22142929347318782120328805 4151799252622271647561651)
      ·
        refine ⟨6227698878933407471342477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4151799252622271647561651 6227698878933407471342477)
        ·
          refine ⟨2335387079600027801753429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6227698878933407471342477 2335387079600027801753429)
          ·
            refine ⟨13683908669531412900899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2335387079600027801753429 13683908669531412900899)
            ·
              rfl

theorem cell20_809473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 9].length) (baseStart_809473 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_809473 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_809473 prefixEnd_809473 := by exact prefixLift 809473
  have htrace : WordTrace (prefixWord ++ tailWord_809473) baseStart_809473 baseEnd_809473 := by
    simpa [prefixWord, tailWord_809473, baseEnd_809473] using wordTrace_append hprefix tailTrace_809473
  have hstable : (prefixWord ++ tailWord_809473).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809473).length < 2 ^ (prefixWord ++ tailWord_809473).sum := by decide
  have hdescent : baseEnd_809473 < baseStart_809473 := by decide
  rcases family_descends (prefixWord ++ tailWord_809473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809476 : List Nat := [2, 3, 2, 3, 1, 1, 1, 4, 3]
def baseStart_809476 : Nat := 118140960795 + 809476 * 2 ^ 59
def prefixEnd_809476 : Nat := 4983230072969 + 3 ^ 40 * 809476 * 2
def baseEnd_809476 : Nat := 369466903359093471224261

theorem tailTrace_809476 : CollatzResearch.WordTrace tailWord_809476 prefixEnd_809476 369466903359093471224261 := by
  unfold tailWord_809476
  simp only [CollatzResearch.WordTrace]
  refine ⟨14762007607707087169732141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19682676810276116226309521 14762007607707087169732141)
  ·
    refine ⟨5535752852890157688649553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14762007607707087169732141 5535752852890157688649553)
    ·
      refine ⟨4151814639667618266487165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5535752852890157688649553 4151814639667618266487165)
      ·
        refine ⟨1556930489875356849932687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4151814639667618266487165 1556930489875356849932687)
        ·
          refine ⟨2335395734813035274899031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1556930489875356849932687 2335395734813035274899031)
          ·
            refine ⟨3503093602219552912348547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2335395734813035274899031 3503093602219552912348547)
            ·
              refine ⟨5254640403329329368522821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3503093602219552912348547 5254640403329329368522821)
              ·
                refine ⟨985245075624249256598029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5254640403329329368522821 985245075624249256598029)
                ·
                  refine ⟨369466903359093471224261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 985245075624249256598029 369466903359093471224261)
                  ·
                    rfl

theorem cell20_809476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 4, 3].length) (baseStart_809476 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_809476 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_809476 prefixEnd_809476 := by exact prefixLift 809476
  have htrace : WordTrace (prefixWord ++ tailWord_809476) baseStart_809476 baseEnd_809476 := by
    simpa [prefixWord, tailWord_809476, baseEnd_809476] using wordTrace_append hprefix tailTrace_809476
  have hstable : (prefixWord ++ tailWord_809476).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809476).length < 2 ^ (prefixWord ++ tailWord_809476).sum := by decide
  have hdescent : baseEnd_809476 < baseStart_809476 := by decide
  rcases family_descends (prefixWord ++ tailWord_809476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809521 : List Nat := [1, 2, 2, 3, 1, 1, 3, 5, 2]
def baseStart_809521 : Nat := 118140960795 + 809521 * 2 ^ 59
def prefixEnd_809521 : Nat := 4983230072969 + 3 ^ 40 * 809521 * 2
def baseEnd_809521 : Nat := 369487442585273314724077

theorem tailTrace_809521 : CollatzResearch.WordTrace tailWord_809521 prefixEnd_809521 369487442585273314724077 := by
  unfold tailWord_809521
  simp only [CollatzResearch.WordTrace]
  refine ⟨29525656500251147024852417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19683771000167431349901611 29525656500251147024852417)
  ·
    refine ⟨22144242375188360268639313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29525656500251147024852417 22144242375188360268639313)
    ·
      refine ⟨16608181781391270201479485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22144242375188360268639313 16608181781391270201479485)
      ·
        refine ⟨6228068168021726325554807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16608181781391270201479485 6228068168021726325554807)
        ·
          refine ⟨9342102252032589488332211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6228068168021726325554807 9342102252032589488332211)
          ·
            refine ⟨14013153378048884232498317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9342102252032589488332211 14013153378048884232498317)
            ·
              refine ⟨5254932516768331587186869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14013153378048884232498317 5254932516768331587186869)
              ·
                refine ⟨492649923447031086298769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5254932516768331587186869 492649923447031086298769)
                ·
                  refine ⟨369487442585273314724077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 492649923447031086298769 369487442585273314724077)
                  ·
                    rfl

theorem cell20_809521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 5, 2].length) (baseStart_809521 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_809521 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_809521 prefixEnd_809521 := by exact prefixLift 809521
  have htrace : WordTrace (prefixWord ++ tailWord_809521) baseStart_809521 baseEnd_809521 := by
    simpa [prefixWord, tailWord_809521, baseEnd_809521] using wordTrace_append hprefix tailTrace_809521
  have hstable : (prefixWord ++ tailWord_809521).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809521).length < 2 ^ (prefixWord ++ tailWord_809521).sum := by decide
  have hdescent : baseEnd_809521 < baseStart_809521 := by decide
  rcases family_descends (prefixWord ++ tailWord_809521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809604 : List Nat := [2, 3, 2, 1, 3, 2, 2, 5]
def baseStart_809604 : Nat := 118140960795 + 809604 * 2 ^ 59
def prefixEnd_809604 : Nat := 4983230072969 + 3 ^ 40 * 809604 * 2
def baseEnd_809604 : Nat := 123175108682297971652357

theorem tailTrace_809604 : CollatzResearch.WordTrace tailWord_809604 prefixEnd_809604 123175108682297971652357 := by
  unfold tailWord_809604
  simp only [CollatzResearch.WordTrace]
  refine ⟨14764341879475226100061933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19685789172633634800082577 14764341879475226100061933)
  ·
    refine ⟨5536628204803209787523225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14764341879475226100061933 5536628204803209787523225)
    ·
      refine ⟨4152471153602407340642419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5536628204803209787523225 4152471153602407340642419)
      ·
        refine ⟨6228706730403611010963629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4152471153602407340642419 6228706730403611010963629)
        ·
          refine ⟨2335765023901354129111361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6228706730403611010963629 2335765023901354129111361)
          ·
            refine ⟨1751823767926015596833521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2335765023901354129111361 1751823767926015596833521)
            ·
              refine ⟨1313867825944511697625141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1751823767926015596833521 1313867825944511697625141)
              ·
                refine ⟨123175108682297971652357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1313867825944511697625141 123175108682297971652357)
                ·
                  rfl

theorem cell20_809604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 5].length) (baseStart_809604 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_809604 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_809604 prefixEnd_809604 := by exact prefixLift 809604
  have htrace : WordTrace (prefixWord ++ tailWord_809604) baseStart_809604 baseEnd_809604 := by
    simpa [prefixWord, tailWord_809604, baseEnd_809604] using wordTrace_append hprefix tailTrace_809604
  have hstable : (prefixWord ++ tailWord_809604).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809604).length < 2 ^ (prefixWord ++ tailWord_809604).sum := by decide
  have hdescent : baseEnd_809604 < baseStart_809604 := by decide
  rcases family_descends (prefixWord ++ tailWord_809604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809642 : List Nat := [3, 1, 5, 2, 9]
def baseStart_809642 : Nat := 118140960795 + 809642 * 2 ^ 59
def prefixEnd_809642 : Nat := 4983230072969 + 3 ^ 40 * 809642 * 2
def baseEnd_809642 : Nat := 4562255188670798415929

theorem tailTrace_809642 : CollatzResearch.WordTrace tailWord_809642 prefixEnd_809642 4562255188670798415929 := by
  unfold tailWord_809642
  simp only [CollatzResearch.WordTrace]
  refine ⟨7382517433203196172501795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19686713155208523126671453 7382517433203196172501795)
  ·
    refine ⟨11073776149804794258752693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7382517433203196172501795 11073776149804794258752693)
    ·
      refine ⟨1038166514044199461758065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11073776149804794258752693 1038166514044199461758065)
      ·
        refine ⟨778624885533149596318549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1038166514044199461758065 778624885533149596318549)
        ·
          refine ⟨4562255188670798415929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 778624885533149596318549 4562255188670798415929)
          ·
            rfl

theorem cell20_809642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 9].length) (baseStart_809642 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_809642 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_809642 prefixEnd_809642 := by exact prefixLift 809642
  have htrace : WordTrace (prefixWord ++ tailWord_809642) baseStart_809642 baseEnd_809642 := by
    simpa [prefixWord, tailWord_809642, baseEnd_809642] using wordTrace_append hprefix tailTrace_809642
  have hstable : (prefixWord ++ tailWord_809642).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809642).length < 2 ^ (prefixWord ++ tailWord_809642).sum := by decide
  have hdescent : baseEnd_809642 < baseStart_809642 := by decide
  rcases family_descends (prefixWord ++ tailWord_809642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809663 : List Nat := [1, 1, 2, 2, 2, 4, 3, 5]
def baseStart_809663 : Nat := 118140960795 + 809663 * 2 ^ 59
def prefixEnd_809663 : Nat := 4983230072969 + 3 ^ 40 * 809663 * 2
def baseEnd_809663 : Nat := 123184085084850643996721

theorem tailTrace_809663 : CollatzResearch.WordTrace tailWord_809663 prefixEnd_809663 123184085084850643996721 := by
  unfold tailWord_809663
  simp only [CollatzResearch.WordTrace]
  refine ⟨29530835665736705276521643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19687223777157803517681095 29530835665736705276521643)
  ·
    refine ⟨44296253498605057914782465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29530835665736705276521643 44296253498605057914782465)
    ·
      refine ⟨33222190123953793436086849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44296253498605057914782465 33222190123953793436086849)
      ·
        refine ⟨24916642592965345077065137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33222190123953793436086849 24916642592965345077065137)
        ·
          refine ⟨18687481944724008807798853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24916642592965345077065137 18687481944724008807798853)
          ·
            refine ⟨3503902864635751651462285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18687481944724008807798853 3503902864635751651462285)
            ·
              refine ⟨1313963574238406869298357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3503902864635751651462285 1313963574238406869298357)
              ·
                refine ⟨123184085084850643996721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1313963574238406869298357 123184085084850643996721)
                ·
                  rfl

theorem cell20_809663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 5].length) (baseStart_809663 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_809663 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_809663 prefixEnd_809663 := by exact prefixLift 809663
  have htrace : WordTrace (prefixWord ++ tailWord_809663) baseStart_809663 baseEnd_809663 := by
    simpa [prefixWord, tailWord_809663, baseEnd_809663] using wordTrace_append hprefix tailTrace_809663
  have hstable : (prefixWord ++ tailWord_809663).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809663).length < 2 ^ (prefixWord ++ tailWord_809663).sum := by decide
  have hdescent : baseEnd_809663 < baseStart_809663 := by decide
  rcases family_descends (prefixWord ++ tailWord_809663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809701 : List Nat := [1, 3, 1, 4, 1, 3, 7]
def baseStart_809701 : Nat := 118140960795 + 809701 * 2 ^ 59
def prefixEnd_809701 : Nat := 4983230072969 + 3 ^ 40 * 809701 * 2
def baseEnd_809701 : Nat := 41063288832221409858149

theorem tailTrace_809701 : CollatzResearch.WordTrace tailWord_809701 prefixEnd_809701 41063288832221409858149 := by
  unfold tailWord_809701
  simp only [CollatzResearch.WordTrace]
  refine ⟨29532221639599037766404957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19688147759732691844269971 29532221639599037766404957)
  ·
    refine ⟨11074583114849639162401859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29532221639599037766404957 11074583114849639162401859)
    ·
      refine ⟨16611874672274458743602789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11074583114849639162401859 16611874672274458743602789)
      ·
        refine ⟨3114726501051461014425523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16611874672274458743602789 3114726501051461014425523)
        ·
          refine ⟨4672089751577191521638285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3114726501051461014425523 4672089751577191521638285)
          ·
            refine ⟨1752033656841446820614357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4672089751577191521638285 1752033656841446820614357)
            ·
              refine ⟨41063288832221409858149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1752033656841446820614357 41063288832221409858149)
              ·
                rfl

theorem cell20_809701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 7].length) (baseStart_809701 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_809701 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_809701 prefixEnd_809701 := by exact prefixLift 809701
  have htrace : WordTrace (prefixWord ++ tailWord_809701) baseStart_809701 baseEnd_809701 := by
    simpa [prefixWord, tailWord_809701, baseEnd_809701] using wordTrace_append hprefix tailTrace_809701
  have hstable : (prefixWord ++ tailWord_809701).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809701).length < 2 ^ (prefixWord ++ tailWord_809701).sum := by decide
  have hdescent : baseEnd_809701 < baseStart_809701 := by decide
  rcases family_descends (prefixWord ++ tailWord_809701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809711 : List Nat := [1, 1, 2, 1, 5, 2, 2, 4, 2]
def baseStart_809711 : Nat := 118140960795 + 809711 * 2 ^ 59
def prefixEnd_809711 : Nat := 4983230072969 + 3 ^ 40 * 809711 * 2
def baseEnd_809711 : Nat := 369574163762477098389967

theorem tailTrace_809711 : CollatzResearch.WordTrace tailWord_809711 prefixEnd_809711 369574163762477098389967 := by
  unfold tailWord_809711
  simp only [CollatzResearch.WordTrace]
  refine ⟨29532586369562809474268987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19688390913041872982845991 29532586369562809474268987)
  ·
    refine ⟨44298879554344214211403481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29532586369562809474268987 44298879554344214211403481)
    ·
      refine ⟨33224159665758160658552611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44298879554344214211403481 33224159665758160658552611)
      ·
        refine ⟨49836239498637240987828917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33224159665758160658552611 49836239498637240987828917)
        ·
          refine ⟨4672147452997241342608961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49836239498637240987828917 4672147452997241342608961)
          ·
            refine ⟨3504110589747931006956721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4672147452997241342608961 3504110589747931006956721)
            ·
              refine ⟨2628082942310948255217541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3504110589747931006956721 2628082942310948255217541)
              ·
                refine ⟨492765551683302797853289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2628082942310948255217541 492765551683302797853289)
                ·
                  refine ⟨369574163762477098389967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 492765551683302797853289 369574163762477098389967)
                  ·
                    rfl

theorem cell20_809711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 4, 2].length) (baseStart_809711 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_809711 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_809711 prefixEnd_809711 := by exact prefixLift 809711
  have htrace : WordTrace (prefixWord ++ tailWord_809711) baseStart_809711 baseEnd_809711 := by
    simpa [prefixWord, tailWord_809711, baseEnd_809711] using wordTrace_append hprefix tailTrace_809711
  have hstable : (prefixWord ++ tailWord_809711).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809711).length < 2 ^ (prefixWord ++ tailWord_809711).sum := by decide
  have hdescent : baseEnd_809711 < baseStart_809711 := by decide
  rcases family_descends (prefixWord ++ tailWord_809711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809717 : List Nat := [1, 3, 6, 1, 1, 1, 3, 1, 3]
def baseStart_809717 : Nat := 118140960795 + 809717 * 2 ^ 59
def prefixEnd_809717 : Nat := 4983230072969 + 3 ^ 40 * 809717 * 2
def baseEnd_809717 : Nat := 369576902325967744189943

theorem tailTrace_809717 : CollatzResearch.WordTrace tailWord_809717 prefixEnd_809717 369576902325967744189943 := by
  unfold tailWord_809717
  simp only [CollatzResearch.WordTrace]
  refine ⟨29532805207541072498987405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19688536805027381665991603 29532805207541072498987405)
  ·
    refine ⟨11074801952827902187120277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29532805207541072498987405 11074801952827902187120277)
    ·
      refine ⟨519131341538807915021263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 11074801952827902187120277 519131341538807915021263)
      ·
        refine ⟨778697012308211872531895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 519131341538807915021263 778697012308211872531895)
        ·
          refine ⟨1168045518462317808797843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 778697012308211872531895 1168045518462317808797843)
          ·
            refine ⟨1752068277693476713196765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1168045518462317808797843 1752068277693476713196765)
            ·
              refine ⟨657025604135053767448787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1752068277693476713196765 657025604135053767448787)
              ·
                refine ⟨985538406202580651173181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 657025604135053767448787 985538406202580651173181)
                ·
                  refine ⟨369576902325967744189943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 985538406202580651173181 369576902325967744189943)
                  ·
                    rfl

theorem cell20_809717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 3, 1, 3].length) (baseStart_809717 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_809717 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_809717 prefixEnd_809717 := by exact prefixLift 809717
  have htrace : WordTrace (prefixWord ++ tailWord_809717) baseStart_809717 baseEnd_809717 := by
    simpa [prefixWord, tailWord_809717, baseEnd_809717] using wordTrace_append hprefix tailTrace_809717
  have hstable : (prefixWord ++ tailWord_809717).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809717).length < 2 ^ (prefixWord ++ tailWord_809717).sum := by decide
  have hdescent : baseEnd_809717 < baseStart_809717 := by decide
  rcases family_descends (prefixWord ++ tailWord_809717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809732 : List Nat := [2, 3, 2, 2, 1, 1, 1, 4, 4]
def baseStart_809732 : Nat := 118140960795 + 809732 * 2 ^ 59
def prefixEnd_809732 : Nat := 4983230072969 + 3 ^ 40 * 809732 * 2
def baseEnd_809732 : Nat := 369583748734694358689881

theorem tailTrace_809732 : CollatzResearch.WordTrace tailWord_809732 prefixEnd_809732 369583748734694358689881 := by
  unfold tailWord_809732
  simp only [CollatzResearch.WordTrace]
  refine ⟨14766676151243365030391725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19688901534991153373855633 14766676151243365030391725)
  ·
    refine ⟨5537503556716261886396897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14766676151243365030391725 5537503556716261886396897)
    ·
      refine ⟨4153127667537196414797673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5537503556716261886396897 4153127667537196414797673)
      ·
        refine ⟨3114845750652897311098255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4153127667537196414797673 3114845750652897311098255)
        ·
          refine ⟨4672268625979345966647383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3114845750652897311098255 4672268625979345966647383)
          ·
            refine ⟨7008402938969018949971075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4672268625979345966647383 7008402938969018949971075)
            ·
              refine ⟨10512604408453528424956613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7008402938969018949971075 10512604408453528424956613)
              ·
                refine ⟨1971113326585036579679365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10512604408453528424956613 1971113326585036579679365)
                ·
                  refine ⟨369583748734694358689881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1971113326585036579679365 369583748734694358689881)
                  ·
                    rfl

theorem cell20_809732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_809732 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_809732 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_809732 prefixEnd_809732 := by exact prefixLift 809732
  have htrace : WordTrace (prefixWord ++ tailWord_809732) baseStart_809732 baseEnd_809732 := by
    simpa [prefixWord, tailWord_809732, baseEnd_809732] using wordTrace_append hprefix tailTrace_809732
  have hstable : (prefixWord ++ tailWord_809732).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809732).length < 2 ^ (prefixWord ++ tailWord_809732).sum := by decide
  have hdescent : baseEnd_809732 < baseStart_809732 := by decide
  rcases family_descends (prefixWord ++ tailWord_809732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809735 : List Nat := [1, 1, 4, 4, 1, 3, 2, 4]
def baseStart_809735 : Nat := 118140960795 + 809735 * 2 ^ 59
def prefixEnd_809735 : Nat := 4983230072969 + 3 ^ 40 * 809735 * 2
def baseEnd_809735 : Nat := 123195039338813227196623

theorem tailTrace_809735 : CollatzResearch.WordTrace tailWord_809735 prefixEnd_809735 123195039338813227196623 := by
  unfold tailWord_809735
  simp only [CollatzResearch.WordTrace]
  refine ⟨29533461721475861573142659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19688974480983907715428439 29533461721475861573142659)
  ·
    refine ⟨44300192582213792359713989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29533461721475861573142659 44300192582213792359713989)
    ·
      refine ⟨8306286109165086067446373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44300192582213792359713989 8306286109165086067446373)
      ·
        refine ⟨1557428645468453637646195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8306286109165086067446373 1557428645468453637646195)
        ·
          refine ⟨2336142968202680456469293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1557428645468453637646195 2336142968202680456469293)
          ·
            refine ⟨876053613076005171175985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2336142968202680456469293 876053613076005171175985)
            ·
              refine ⟨657040209807003878381989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 876053613076005171175985 657040209807003878381989)
              ·
                refine ⟨123195039338813227196623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 657040209807003878381989 123195039338813227196623)
                ·
                  rfl

theorem cell20_809735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 2, 4].length) (baseStart_809735 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_809735 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_809735 prefixEnd_809735 := by exact prefixLift 809735
  have htrace : WordTrace (prefixWord ++ tailWord_809735) baseStart_809735 baseEnd_809735 := by
    simpa [prefixWord, tailWord_809735, baseEnd_809735] using wordTrace_append hprefix tailTrace_809735
  have hstable : (prefixWord ++ tailWord_809735).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809735).length < 2 ^ (prefixWord ++ tailWord_809735).sum := by decide
  have hdescent : baseEnd_809735 < baseStart_809735 := by decide
  rcases family_descends (prefixWord ++ tailWord_809735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809777 : List Nat := [1, 2, 2, 3, 2, 1, 4, 5]
def baseStart_809777 : Nat := 118140960795 + 809777 * 2 ^ 59
def prefixEnd_809777 : Nat := 4983230072969 + 3 ^ 40 * 809777 * 2
def baseEnd_809777 : Nat := 123201429320291400729899

theorem tailTrace_809777 : CollatzResearch.WordTrace tailWord_809777 prefixEnd_809777 123201429320291400729899 := by
  unfold tailWord_809777
  simp only [CollatzResearch.WordTrace]
  refine ⟨29534993587323702746171585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19689995724882468497447723 29534993587323702746171585)
  ·
    refine ⟨22151245190492777059628689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29534993587323702746171585 22151245190492777059628689)
    ·
      refine ⟨16613433892869582794721517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22151245190492777059628689 16613433892869582794721517)
      ·
        refine ⟨6230037709826093548020569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16613433892869582794721517 6230037709826093548020569)
        ·
          refine ⟨4672528282369570161015427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6230037709826093548020569 4672528282369570161015427)
          ·
            refine ⟨7008792423554355241523141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4672528282369570161015427 7008792423554355241523141)
            ·
              refine ⟨1314148579416441607785589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7008792423554355241523141 1314148579416441607785589)
              ·
                refine ⟨123201429320291400729899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1314148579416441607785589 123201429320291400729899)
                ·
                  rfl

theorem cell20_809777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 5].length) (baseStart_809777 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_809777 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_809777 prefixEnd_809777 := by exact prefixLift 809777
  have htrace : WordTrace (prefixWord ++ tailWord_809777) baseStart_809777 baseEnd_809777 := by
    simpa [prefixWord, tailWord_809777, baseEnd_809777] using wordTrace_append hprefix tailTrace_809777
  have hstable : (prefixWord ++ tailWord_809777).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809777).length < 2 ^ (prefixWord ++ tailWord_809777).sum := by decide
  have hdescent : baseEnd_809777 < baseStart_809777 := by decide
  rcases family_descends (prefixWord ++ tailWord_809777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809832 : List Nat := [2, 1, 4, 2, 1, 4, 1, 5]
def baseStart_809832 : Nat := 118140960795 + 809832 * 2 ^ 59
def prefixEnd_809832 : Nat := 4983230072969 + 3 ^ 40 * 809832 * 2
def baseEnd_809832 : Nat := 123209797153179485118713

theorem tailTrace_809832 : CollatzResearch.WordTrace tailWord_809832 prefixEnd_809832 123209797153179485118713 := by
  unfold tailWord_809832
  simp only [CollatzResearch.WordTrace]
  refine ⟨14768499801062223569711875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19691333068082964759615833 14768499801062223569711875)
  ·
    refine ⟨22152749701593335354567813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14768499801062223569711875 22152749701593335354567813)
    ·
      refine ⟨4153640569048750378981465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22152749701593335354567813 4153640569048750378981465)
      ·
        refine ⟨3115230426786562784236099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4153640569048750378981465 3115230426786562784236099)
        ·
          refine ⟨4672845640179844176354149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3115230426786562784236099 4672845640179844176354149)
          ·
            refine ⟨876158557533720783066403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4672845640179844176354149 876158557533720783066403)
            ·
              refine ⟨1314237836300581174599605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 876158557533720783066403 1314237836300581174599605)
              ·
                refine ⟨123209797153179485118713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1314237836300581174599605 123209797153179485118713)
                ·
                  rfl

theorem cell20_809832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 5].length) (baseStart_809832 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_809832 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_809832 prefixEnd_809832 := by exact prefixLift 809832
  have htrace : WordTrace (prefixWord ++ tailWord_809832) baseStart_809832 baseEnd_809832 := by
    simpa [prefixWord, tailWord_809832, baseEnd_809832] using wordTrace_append hprefix tailTrace_809832
  have hstable : (prefixWord ++ tailWord_809832).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809832).length < 2 ^ (prefixWord ++ tailWord_809832).sum := by decide
  have hdescent : baseEnd_809832 < baseStart_809832 := by decide
  rcases family_descends (prefixWord ++ tailWord_809832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809860 : List Nat := [2, 3, 2, 1, 1, 1, 1, 4, 5]
def baseStart_809860 : Nat := 118140960795 + 809860 * 2 ^ 59
def prefixEnd_809860 : Nat := 4983230072969 + 3 ^ 40 * 809860 * 2
def baseEnd_809860 : Nat := 369642171422494802422691

theorem tailTrace_809860 : CollatzResearch.WordTrace tailWord_809860 prefixEnd_809860 369642171422494802422691 := by
  unfold tailWord_809860
  simp only [CollatzResearch.WordTrace]
  refine ⟨14769010423011503960721517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19692013897348671947628689 14769010423011503960721517)
  ·
    refine ⟨5538378908629313985270569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14769010423011503960721517 5538378908629313985270569)
    ·
      refine ⟨4153784181471985488952927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5538378908629313985270569 4153784181471985488952927)
      ·
        refine ⟨6230676272207978233429391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4153784181471985488952927 6230676272207978233429391)
        ·
          refine ⟨9346014408311967350144087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6230676272207978233429391 9346014408311967350144087)
          ·
            refine ⟨14019021612467951025216131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9346014408311967350144087 14019021612467951025216131)
            ·
              refine ⟨21028532418701926537824197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14019021612467951025216131 21028532418701926537824197)
              ·
                refine ⟨3942849828506611225842037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21028532418701926537824197 3942849828506611225842037)
                ·
                  refine ⟨369642171422494802422691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3942849828506611225842037 369642171422494802422691)
                  ·
                    rfl

theorem cell20_809860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_809860 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_809860 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_809860 prefixEnd_809860 := by exact prefixLift 809860
  have htrace : WordTrace (prefixWord ++ tailWord_809860) baseStart_809860 baseEnd_809860 := by
    simpa [prefixWord, tailWord_809860, baseEnd_809860] using wordTrace_append hprefix tailTrace_809860
  have hstable : (prefixWord ++ tailWord_809860).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809860).length < 2 ^ (prefixWord ++ tailWord_809860).sum := by decide
  have hdescent : baseEnd_809860 < baseStart_809860 := by decide
  rcases family_descends (prefixWord ++ tailWord_809860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809863 : List Nat := [1, 1, 4, 2, 3, 1, 1, 5, 2]
def baseStart_809863 : Nat := 118140960795 + 809863 * 2 ^ 59
def prefixEnd_809863 : Nat := 4983230072969 + 3 ^ 40 * 809863 * 2
def baseEnd_809863 : Nat := 369643540704240125322679

theorem tailTrace_809863 : CollatzResearch.WordTrace tailWord_809863 prefixEnd_809863 369643540704240125322679 := by
  unfold tailWord_809863
  simp only [CollatzResearch.WordTrace]
  refine ⟨29538130265012139433802243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19692086843341426289201495 29538130265012139433802243)
  ·
    refine ⟨44307195397518209150703365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29538130265012139433802243 44307195397518209150703365)
    ·
      refine ⟨8307599137034664215756881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44307195397518209150703365 8307599137034664215756881)
      ·
        refine ⟨6230699352775998161817661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8307599137034664215756881 6230699352775998161817661)
        ·
          refine ⟨2336512257290999310681623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6230699352775998161817661 2336512257290999310681623)
          ·
            refine ⟨3504768385936498966022435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2336512257290999310681623 3504768385936498966022435)
            ·
              refine ⟨5257152578904748449033653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3504768385936498966022435 5257152578904748449033653)
              ·
                refine ⟨492858054272320167096905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5257152578904748449033653 492858054272320167096905)
                ·
                  refine ⟨369643540704240125322679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 492858054272320167096905 369643540704240125322679)
                  ·
                    rfl

theorem cell20_809863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 5, 2].length) (baseStart_809863 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_809863 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_809863 prefixEnd_809863 := by exact prefixLift 809863
  have htrace : WordTrace (prefixWord ++ tailWord_809863) baseStart_809863 baseEnd_809863 := by
    simpa [prefixWord, tailWord_809863, baseEnd_809863] using wordTrace_append hprefix tailTrace_809863
  have hstable : (prefixWord ++ tailWord_809863).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809863).length < 2 ^ (prefixWord ++ tailWord_809863).sum := by decide
  have hdescent : baseEnd_809863 < baseStart_809863 := by decide
  rcases family_descends (prefixWord ++ tailWord_809863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809877 : List Nat := [1, 3, 2, 1, 1, 4, 3, 2, 3]
def baseStart_809877 : Nat := 118140960795 + 809877 * 2 ^ 59
def prefixEnd_809877 : Nat := 4983230072969 + 3 ^ 40 * 809877 * 2
def baseEnd_809877 : Nat := 369649930685718298855955

theorem tailTrace_809877 : CollatzResearch.WordTrace tailWord_809877 prefixEnd_809877 369649930685718298855955 := by
  unfold tailWord_809877
  simp only [CollatzResearch.WordTrace]
  refine ⟨29538640886961419824811885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19692427257974279883207923 29538640886961419824811885)
  ·
    refine ⟨11076990332610532434304457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29538640886961419824811885 11076990332610532434304457)
    ·
      refine ⟨8307742749457899325728343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11076990332610532434304457 8307742749457899325728343)
      ·
        refine ⟨12461614124186848988592515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8307742749457899325728343 12461614124186848988592515)
        ·
          refine ⟨18692421186280273482888773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12461614124186848988592515 18692421186280273482888773)
          ·
            refine ⟨3504828972427551278041645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18692421186280273482888773 3504828972427551278041645)
            ·
              refine ⟨1314310864660331729265617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3504828972427551278041645 1314310864660331729265617)
              ·
                refine ⟨985733148495248796949213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1314310864660331729265617 985733148495248796949213)
                ·
                  refine ⟨369649930685718298855955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 985733148495248796949213 369649930685718298855955)
                  ·
                    rfl

theorem cell20_809877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 2, 3].length) (baseStart_809877 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_809877 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_809877 prefixEnd_809877 := by exact prefixLift 809877
  have htrace : WordTrace (prefixWord ++ tailWord_809877) baseStart_809877 baseEnd_809877 := by
    simpa [prefixWord, tailWord_809877, baseEnd_809877] using wordTrace_append hprefix tailTrace_809877
  have hstable : (prefixWord ++ tailWord_809877).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809877).length < 2 ^ (prefixWord ++ tailWord_809877).sum := by decide
  have hdescent : baseEnd_809877 < baseStart_809877 := by decide
  rcases family_descends (prefixWord ++ tailWord_809877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809910 : List Nat := [5, 1, 4, 1, 2, 1, 1, 3, 2]
def baseStart_809910 : Nat := 118140960795 + 809910 * 2 ^ 59
def prefixEnd_809910 : Nat := 4983230072969 + 3 ^ 40 * 809910 * 2
def baseEnd_809910 : Nat := 369664992784916850755821

theorem tailTrace_809910 : CollatzResearch.WordTrace tailWord_809910 prefixEnd_809910 369664992784916850755821 := by
  unfold tailWord_809910
  simp only [CollatzResearch.WordTrace]
  refine ⟨1846240280990116653797699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19693229663894577640508789 1846240280990116653797699)
  ·
    refine ⟨2769360421485174980696549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1846240280990116653797699 2769360421485174980696549)
    ·
      refine ⟨519255079028470308880603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2769360421485174980696549 519255079028470308880603)
      ·
        refine ⟨778882618542705463320905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 519255079028470308880603 778882618542705463320905)
        ·
          refine ⟨584161963907029097490679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 778882618542705463320905 584161963907029097490679)
          ·
            refine ⟨876242945860543646236019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 584161963907029097490679 876242945860543646236019)
            ·
              refine ⟨1314364418790815469354029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 876242945860543646236019 1314364418790815469354029)
              ·
                refine ⟨492886657046555801007761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1314364418790815469354029 492886657046555801007761)
                ·
                  refine ⟨369664992784916850755821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 492886657046555801007761 369664992784916850755821)
                  ·
                    rfl

theorem cell20_809910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 3, 2].length) (baseStart_809910 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_809910 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_809910 prefixEnd_809910 := by exact prefixLift 809910
  have htrace : WordTrace (prefixWord ++ tailWord_809910) baseStart_809910 baseEnd_809910 := by
    simpa [prefixWord, tailWord_809910, baseEnd_809910] using wordTrace_append hprefix tailTrace_809910
  have hstable : (prefixWord ++ tailWord_809910).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809910).length < 2 ^ (prefixWord ++ tailWord_809910).sum := by decide
  have hdescent : baseEnd_809910 < baseStart_809910 := by decide
  rcases family_descends (prefixWord ++ tailWord_809910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809936 : List Nat := [2, 1, 1, 1, 1, 2, 3, 6, 3]
def baseStart_809936 : Nat := 118140960795 + 809936 * 2 ^ 59
def prefixEnd_809936 : Nat := 4983230072969 + 3 ^ 40 * 809936 * 2
def baseEnd_809936 : Nat := 369676859893376315889047

theorem tailTrace_809936 : CollatzResearch.WordTrace tailWord_809936 prefixEnd_809936 369676859893376315889047 := by
  unfold tailWord_809936
  simp only [CollatzResearch.WordTrace]
  refine ⟨14770396396873836450604831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19693861862498448600806441 14770396396873836450604831)
  ·
    refine ⟨22155594595310754675907247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14770396396873836450604831 22155594595310754675907247)
    ·
      refine ⟨33233391892966132013860871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22155594595310754675907247 33233391892966132013860871)
      ·
        refine ⟨49850087839449198020791307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33233391892966132013860871 49850087839449198020791307)
        ·
          refine ⟨74775131759173797031186961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49850087839449198020791307 74775131759173797031186961)
          ·
            refine ⟨56081348819380347773390221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74775131759173797031186961 56081348819380347773390221)
            ·
              refine ⟨21030505807267630415021333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56081348819380347773390221 21030505807267630415021333)
              ·
                refine ⟨985804959715670175704125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21030505807267630415021333 985804959715670175704125)
                ·
                  refine ⟨369676859893376315889047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 985804959715670175704125 369676859893376315889047)
                  ·
                    rfl

theorem cell20_809936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 6, 3].length) (baseStart_809936 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_809936 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_809936 prefixEnd_809936 := by exact prefixLift 809936
  have htrace : WordTrace (prefixWord ++ tailWord_809936) baseStart_809936 baseEnd_809936 := by
    simpa [prefixWord, tailWord_809936, baseEnd_809936] using wordTrace_append hprefix tailTrace_809936
  have hstable : (prefixWord ++ tailWord_809936).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809936).length < 2 ^ (prefixWord ++ tailWord_809936).sum := by decide
  have hdescent : baseEnd_809936 < baseStart_809936 := by decide
  rcases family_descends (prefixWord ++ tailWord_809936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809943 : List Nat := [1, 1, 3, 2, 1, 1, 2, 5, 4]
def baseStart_809943 : Nat := 118140960795 + 809943 * 2 ^ 59
def prefixEnd_809943 : Nat := 4983230072969 + 3 ^ 40 * 809943 * 2
def baseEnd_809943 : Nat := 369680054884115402655685

theorem tailTrace_809943 : CollatzResearch.WordTrace tailWord_809943 prefixEnd_809943 369680054884115402655685 := by
  unfold tailWord_809943
  simp only [CollatzResearch.WordTrace]
  refine ⟨29541048104722313096714483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19694032069814875397809655 29541048104722313096714483)
  ·
    refine ⟨44311572157083469645071725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29541048104722313096714483 44311572157083469645071725)
    ·
      refine ⟨16616839558906301116901897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44311572157083469645071725 16616839558906301116901897)
      ·
        refine ⟨12462629669179725837676423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16616839558906301116901897 12462629669179725837676423)
        ·
          refine ⟨18693944503769588756514635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12462629669179725837676423 18693944503769588756514635)
          ·
            refine ⟨28040916755654383134771953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18693944503769588756514635 28040916755654383134771953)
            ·
              refine ⟨21030687566740787351078965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28040916755654383134771953 21030687566740787351078965)
              ·
                refine ⟨1971626959381948814163653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21030687566740787351078965 1971626959381948814163653)
                ·
                  refine ⟨369680054884115402655685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1971626959381948814163653 369680054884115402655685)
                  ·
                    rfl

theorem cell20_809943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 5, 4].length) (baseStart_809943 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_809943 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_809943 prefixEnd_809943 := by exact prefixLift 809943
  have htrace : WordTrace (prefixWord ++ tailWord_809943) baseStart_809943 baseEnd_809943 := by
    simpa [prefixWord, tailWord_809943, baseEnd_809943] using wordTrace_append hprefix tailTrace_809943
  have hstable : (prefixWord ++ tailWord_809943).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809943).length < 2 ^ (prefixWord ++ tailWord_809943).sum := by decide
  have hdescent : baseEnd_809943 < baseStart_809943 := by decide
  rcases family_descends (prefixWord ++ tailWord_809943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809949 : List Nat := [1, 4, 3, 1, 2, 3, 2, 1, 3]
def baseStart_809949 : Nat := 118140960795 + 809949 * 2 ^ 59
def prefixEnd_809949 : Nat := 4983230072969 + 3 ^ 40 * 809949 * 2
def baseEnd_809949 : Nat := 369682793447606048455661

theorem tailTrace_809949 : CollatzResearch.WordTrace tailWord_809949 prefixEnd_809949 369682793447606048455661 := by
  unfold tailWord_809949
  simp only [CollatzResearch.WordTrace]
  refine ⟨29541266942700576121432901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19694177961800384080955267 29541266942700576121432901)
  ·
    refine ⟨5538987551756358022768669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29541266942700576121432901 5538987551756358022768669)
    ·
      refine ⟨2077120331908634258538251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5538987551756358022768669 2077120331908634258538251)
      ·
        refine ⟨3115680497862951387807377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2077120331908634258538251 3115680497862951387807377)
        ·
          refine ⟨2336760373397213540855533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3115680497862951387807377 2336760373397213540855533)
          ·
            refine ⟨876285140023955077820825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2336760373397213540855533 876285140023955077820825)
            ·
              refine ⟨657213855017966308365619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 876285140023955077820825 657213855017966308365619)
              ·
                refine ⟨985820782526949462548429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 657213855017966308365619 985820782526949462548429)
                ·
                  refine ⟨369682793447606048455661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 985820782526949462548429 369682793447606048455661)
                  ·
                    rfl

theorem cell20_809949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 2, 1, 3].length) (baseStart_809949 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_809949 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_809949 prefixEnd_809949 := by exact prefixLift 809949
  have htrace : WordTrace (prefixWord ++ tailWord_809949) baseStart_809949 baseEnd_809949 := by
    simpa [prefixWord, tailWord_809949, baseEnd_809949] using wordTrace_append hprefix tailTrace_809949
  have hstable : (prefixWord ++ tailWord_809949).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809949).length < 2 ^ (prefixWord ++ tailWord_809949).sum := by decide
  have hdescent : baseEnd_809949 < baseStart_809949 := by decide
  rcases family_descends (prefixWord ++ tailWord_809949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809988 : List Nat := [2, 3, 2, 13]
def baseStart_809988 : Nat := 118140960795 + 809988 * 2 ^ 59
def prefixEnd_809988 : Nat := 4983230072969 + 3 ^ 40 * 809988 * 2
def baseEnd_809988 : Nat := 1521401621853066856607

theorem tailTrace_809988 : CollatzResearch.WordTrace tailWord_809988 prefixEnd_809988 1521401621853066856607 := by
  unfold tailWord_809988
  simp only [CollatzResearch.WordTrace]
  refine ⟨14771344694779642891051309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19695126259706190521401745 14771344694779642891051309)
  ·
    refine ⟨5539254260542366084144241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14771344694779642891051309 5539254260542366084144241)
    ·
      refine ⟨4154440695406774563108181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5539254260542366084144241 4154440695406774563108181)
      ·
        refine ⟨1521401621853066856607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 4154440695406774563108181 1521401621853066856607)
        ·
          rfl

theorem cell20_809988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 13].length) (baseStart_809988 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_809988 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_809988 prefixEnd_809988 := by exact prefixLift 809988
  have htrace : WordTrace (prefixWord ++ tailWord_809988) baseStart_809988 baseEnd_809988 := by
    simpa [prefixWord, tailWord_809988, baseEnd_809988] using wordTrace_append hprefix tailTrace_809988
  have hstable : (prefixWord ++ tailWord_809988).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809988).length < 2 ^ (prefixWord ++ tailWord_809988).sum := by decide
  have hdescent : baseEnd_809988 < baseStart_809988 := by decide
  rcases family_descends (prefixWord ++ tailWord_809988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809991 : List Nat := [1, 1, 4, 3, 1, 1, 4, 2, 3]
def baseStart_809991 : Nat := 118140960795 + 809991 * 2 ^ 59
def prefixEnd_809991 : Nat := 4983230072969 + 3 ^ 40 * 809991 * 2
def baseEnd_809991 : Nat := 369701963392040569055489

theorem tailTrace_809991 : CollatzResearch.WordTrace tailWord_809991 prefixEnd_809991 369701963392040569055489 := by
  unfold tailWord_809991
  simp only [CollatzResearch.WordTrace]
  refine ⟨29542798808548417294461827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19695199205698944862974551 29542798808548417294461827)
  ·
    refine ⟨44314198212822625941692741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29542798808548417294461827 44314198212822625941692741)
    ·
      refine ⟨8308912164904242364067389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44314198212822625941692741 8308912164904242364067389)
      ·
        refine ⟨3115842061839090886525271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8308912164904242364067389 3115842061839090886525271)
        ·
          refine ⟨4673763092758636329787907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3115842061839090886525271 4673763092758636329787907)
          ·
            refine ⟨7010644639137954494681861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4673763092758636329787907 7010644639137954494681861)
            ·
              refine ⟨1314495869838366467752849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7010644639137954494681861 1314495869838366467752849)
              ·
                refine ⟨985871902378774850814637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1314495869838366467752849 985871902378774850814637)
                ·
                  refine ⟨369701963392040569055489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 985871902378774850814637 369701963392040569055489)
                  ·
                    rfl

theorem cell20_809991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 2, 3].length) (baseStart_809991 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_809991 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_809991 prefixEnd_809991 := by exact prefixLift 809991
  have htrace : WordTrace (prefixWord ++ tailWord_809991) baseStart_809991 baseEnd_809991 := by
    simpa [prefixWord, tailWord_809991, baseEnd_809991] using wordTrace_append hprefix tailTrace_809991
  have hstable : (prefixWord ++ tailWord_809991).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809991).length < 2 ^ (prefixWord ++ tailWord_809991).sum := by decide
  have hdescent : baseEnd_809991 < baseStart_809991 := by decide
  rcases family_descends (prefixWord ++ tailWord_809991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809994 : List Nat := [3, 1, 2, 2, 3, 1, 4, 2, 2]
def baseStart_809994 : Nat := 118140960795 + 809994 * 2 ^ 59
def prefixEnd_809994 : Nat := 4983230072969 + 3 ^ 40 * 809994 * 2
def baseEnd_809994 : Nat := 369703332673785891955477

theorem tailTrace_809994 : CollatzResearch.WordTrace tailWord_809994 prefixEnd_809994 369703332673785891955477 := by
  unfold tailWord_809994
  simp only [CollatzResearch.WordTrace]
  refine ⟨7385727056884387201705259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19695272151691699204547357 7385727056884387201705259)
  ·
    refine ⟨11078590585326580802557889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7385727056884387201705259 11078590585326580802557889)
    ·
      refine ⟨8308942938994935601918417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11078590585326580802557889 8308942938994935601918417)
      ·
        refine ⟨6231707204246201701438813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8308942938994935601918417 6231707204246201701438813)
        ·
          refine ⟨2336890201592325638039555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6231707204246201701438813 2336890201592325638039555)
          ·
            refine ⟨3505335302388488457059333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2336890201592325638039555 3505335302388488457059333)
            ·
              refine ⟨657250369197841585698625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3505335302388488457059333 657250369197841585698625)
              ·
                refine ⟨492937776898381189273969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 657250369197841585698625 492937776898381189273969)
                ·
                  refine ⟨369703332673785891955477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 492937776898381189273969 369703332673785891955477)
                  ·
                    rfl

theorem cell20_809994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 4, 2, 2].length) (baseStart_809994 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_809994 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_809994 prefixEnd_809994 := by exact prefixLift 809994
  have htrace : WordTrace (prefixWord ++ tailWord_809994) baseStart_809994 baseEnd_809994 := by
    simpa [prefixWord, tailWord_809994, baseEnd_809994] using wordTrace_append hprefix tailTrace_809994
  have hstable : (prefixWord ++ tailWord_809994).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809994).length < 2 ^ (prefixWord ++ tailWord_809994).sum := by decide
  have hdescent : baseEnd_809994 < baseStart_809994 := by decide
  rcases family_descends (prefixWord ++ tailWord_809994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810005 : List Nat := [1, 3, 2, 1, 4, 1, 3, 5]
def baseStart_810005 : Nat := 118140960795 + 810005 * 2 ^ 59
def prefixEnd_810005 : Nat := 4983230072969 + 3 ^ 40 * 810005 * 2
def baseEnd_810005 : Nat := 123236117791172914196255

theorem tailTrace_810005 : CollatzResearch.WordTrace tailWord_810005 prefixEnd_810005 123236117791172914196255 := by
  unfold tailWord_810005
  simp only [CollatzResearch.WordTrace]
  refine ⟨29543309430497697685471469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19695539620331798456980979 29543309430497697685471469)
  ·
    refine ⟨11078741036436636632051801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29543309430497697685471469 11078741036436636632051801)
    ·
      refine ⟨8309055777327477474038851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11078741036436636632051801 8309055777327477474038851)
      ·
        refine ⟨12463583665991216211058277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8309055777327477474038851 12463583665991216211058277)
        ·
          refine ⟨2336921937373353039573427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12463583665991216211058277 2336921937373353039573427)
          ·
            refine ⟨3505382906060029559360141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2336921937373353039573427 3505382906060029559360141)
            ·
              refine ⟨1314518589772511084760053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3505382906060029559360141 1314518589772511084760053)
              ·
                refine ⟨123236117791172914196255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1314518589772511084760053 123236117791172914196255)
                ·
                  rfl

theorem cell20_810005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 5].length) (baseStart_810005 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_810005 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_810005 prefixEnd_810005 := by exact prefixLift 810005
  have htrace : WordTrace (prefixWord ++ tailWord_810005) baseStart_810005 baseEnd_810005 := by
    simpa [prefixWord, tailWord_810005, baseEnd_810005] using wordTrace_append hprefix tailTrace_810005
  have hstable : (prefixWord ++ tailWord_810005).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810005).length < 2 ^ (prefixWord ++ tailWord_810005).sum := by decide
  have hdescent : baseEnd_810005 < baseStart_810005 := by decide
  rcases family_descends (prefixWord ++ tailWord_810005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810019 : List Nat := [1, 1, 1, 4, 3, 2, 1, 1, 6]
def baseStart_810019 : Nat := 118140960795 + 810019 * 2 ^ 59
def prefixEnd_810019 : Nat := 4983230072969 + 3 ^ 40 * 810019 * 2
def baseEnd_810019 : Nat := 369714743354996916122041

theorem tailTrace_810019 : CollatzResearch.WordTrace tailWord_810019 prefixEnd_810019 369714743354996916122041 := by
  unfold tailWord_810019
  simp only [CollatzResearch.WordTrace]
  refine ⟨29543820052446978076481111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19695880034964652050987407 29543820052446978076481111)
  ·
    refine ⟨44315730078670467114721667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29543820052446978076481111 44315730078670467114721667)
    ·
      refine ⟨66473595118005700672082501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44315730078670467114721667 66473595118005700672082501)
      ·
        refine ⟨12463799084626068876015469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66473595118005700672082501 12463799084626068876015469)
        ·
          refine ⟨4673924656734775828505801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12463799084626068876015469 4673924656734775828505801)
          ·
            refine ⟨3505443492551081871379351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4673924656734775828505801 3505443492551081871379351)
            ·
              refine ⟨5258165238826622807069027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3505443492551081871379351 5258165238826622807069027)
              ·
                refine ⟨7887247858239934210603541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5258165238826622807069027 7887247858239934210603541)
                ·
                  refine ⟨369714743354996916122041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7887247858239934210603541 369714743354996916122041)
                  ·
                    rfl

theorem cell20_810019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 6].length) (baseStart_810019 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_810019 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_810019 prefixEnd_810019 := by exact prefixLift 810019
  have htrace : WordTrace (prefixWord ++ tailWord_810019) baseStart_810019 baseEnd_810019 := by
    simpa [prefixWord, tailWord_810019, baseEnd_810019] using wordTrace_append hprefix tailTrace_810019
  have hstable : (prefixWord ++ tailWord_810019).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810019).length < 2 ^ (prefixWord ++ tailWord_810019).sum := by decide
  have hdescent : baseEnd_810019 < baseStart_810019 := by decide
  rcases family_descends (prefixWord ++ tailWord_810019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810046 : List Nat := [4, 2, 1, 3, 1, 1, 3, 2, 3]
def baseStart_810046 : Nat := 118140960795 + 810046 * 2 ^ 59
def prefixEnd_810046 : Nat := 4983230072969 + 3 ^ 40 * 810046 * 2
def baseEnd_810046 : Nat := 369727066890704822221931

theorem tailTrace_810046 : CollatzResearch.WordTrace tailWord_810046 prefixEnd_810046 369727066890704822221931 := by
  unfold tailWord_810046
  simp only [CollatzResearch.WordTrace]
  refine ⟨3693100602918645210964249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19696536548899441125142661 3693100602918645210964249)
  ·
    refine ⟨2769825452188983908223187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3693100602918645210964249 2769825452188983908223187)
    ·
      refine ⟨4154738178283475862334781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2769825452188983908223187 4154738178283475862334781)
      ·
        refine ⟨1558026816856303448375543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4154738178283475862334781 1558026816856303448375543)
        ·
          refine ⟨2337040225284455172563315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1558026816856303448375543 2337040225284455172563315)
          ·
            refine ⟨3505560337926682758844973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2337040225284455172563315 3505560337926682758844973)
            ·
              refine ⟨1314585126722506034566865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3505560337926682758844973 1314585126722506034566865)
              ·
                refine ⟨985938845041879525925149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1314585126722506034566865 985938845041879525925149)
                ·
                  refine ⟨369727066890704822221931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 985938845041879525925149 369727066890704822221931)
                  ·
                    rfl

theorem cell20_810046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_810046 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_810046 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_810046 prefixEnd_810046 := by exact prefixLift 810046
  have htrace : WordTrace (prefixWord ++ tailWord_810046) baseStart_810046 baseEnd_810046 := by
    simpa [prefixWord, tailWord_810046, baseEnd_810046] using wordTrace_append hprefix tailTrace_810046
  have hstable : (prefixWord ++ tailWord_810046).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810046).length < 2 ^ (prefixWord ++ tailWord_810046).sum := by decide
  have hdescent : baseEnd_810046 < baseStart_810046 := by decide
  rcases family_descends (prefixWord ++ tailWord_810046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810081 : List Nat := [1, 2, 3, 1, 1, 2, 6, 4]
def baseStart_810081 : Nat := 118140960795 + 810081 * 2 ^ 59
def prefixEnd_810081 : Nat := 4983230072969 + 3 ^ 40 * 810081 * 2
def baseEnd_810081 : Nat := 123247680614800085351707

theorem tailTrace_810081 : CollatzResearch.WordTrace tailWord_810081 prefixEnd_810081 123247680614800085351707 := by
  unfold tailWord_810081
  simp only [CollatzResearch.WordTrace]
  refine ⟨29546081378222362665238097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19697387585481575110158731 29546081378222362665238097)
  ·
    refine ⟨22159561033666771998928573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29546081378222362665238097 22159561033666771998928573)
    ·
      refine ⟨8309835387625039499598215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22159561033666771998928573 8309835387625039499598215)
      ·
        refine ⟨12464753081437559249397323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8309835387625039499598215 12464753081437559249397323)
        ·
          refine ⟨18697129622156338874095985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12464753081437559249397323 18697129622156338874095985)
          ·
            refine ⟨14022847216617254155571989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18697129622156338874095985 14022847216617254155571989)
            ·
              refine ⟨657320963278933788542437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 14022847216617254155571989 657320963278933788542437)
              ·
                refine ⟨123247680614800085351707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 657320963278933788542437 123247680614800085351707)
                ·
                  rfl

theorem cell20_810081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 6, 4].length) (baseStart_810081 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_810081 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_810081 prefixEnd_810081 := by exact prefixLift 810081
  have htrace : WordTrace (prefixWord ++ tailWord_810081) baseStart_810081 baseEnd_810081 := by
    simpa [prefixWord, tailWord_810081, baseEnd_810081] using wordTrace_append hprefix tailTrace_810081
  have hstable : (prefixWord ++ tailWord_810081).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810081).length < 2 ^ (prefixWord ++ tailWord_810081).sum := by decide
  have hdescent : baseEnd_810081 < baseStart_810081 := by decide
  rcases family_descends (prefixWord ++ tailWord_810081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810112 : List Nat := [2, 1, 1, 2, 1, 3, 2, 6, 2]
def baseStart_810112 : Nat := 118140960795 + 810112 * 2 ^ 59
def prefixEnd_810112 : Nat := 4983230072969 + 3 ^ 40 * 810112 * 2
def baseEnd_810112 : Nat := 369757191089101926021661

theorem tailTrace_810112 : CollatzResearch.WordTrace tailWord_810112 prefixEnd_810112 369757191089101926021661 := by
  unfold tailWord_810112
  simp only [CollatzResearch.WordTrace]
  refine ⟨14773606020555027479808295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19698141360740036639744393 14773606020555027479808295)
  ·
    refine ⟨22160409030832541219712443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14773606020555027479808295 22160409030832541219712443)
    ·
      refine ⟨33240613546248811829568665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22160409030832541219712443 33240613546248811829568665)
      ·
        refine ⟨24930460159686608872176499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33240613546248811829568665 24930460159686608872176499)
        ·
          refine ⟨37395690239529913308264749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24930460159686608872176499 37395690239529913308264749)
          ·
            refine ⟨14023383839823717490599281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37395690239529913308264749 14023383839823717490599281)
            ·
              refine ⟨10517537879867788117949461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14023383839823717490599281 10517537879867788117949461)
              ·
                refine ⟨493009588118802568028881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10517537879867788117949461 493009588118802568028881)
                ·
                  refine ⟨369757191089101926021661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 493009588118802568028881 369757191089101926021661)
                  ·
                    rfl

theorem cell20_810112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 6, 2].length) (baseStart_810112 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_810112 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_810112 prefixEnd_810112 := by exact prefixLift 810112
  have htrace : WordTrace (prefixWord ++ tailWord_810112) baseStart_810112 baseEnd_810112 := by
    simpa [prefixWord, tailWord_810112, baseEnd_810112] using wordTrace_append hprefix tailTrace_810112
  have hstable : (prefixWord ++ tailWord_810112).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810112).length < 2 ^ (prefixWord ++ tailWord_810112).sum := by decide
  have hdescent : baseEnd_810112 < baseStart_810112 := by decide
  rcases family_descends (prefixWord ++ tailWord_810112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810147 : List Nat := [1, 1, 1, 4, 1, 1, 1, 3, 7]
def baseStart_810147 : Nat := 118140960795 + 810147 * 2 ^ 59
def prefixEnd_810147 : Nat := 4983230072969 + 3 ^ 40 * 810147 * 2
def baseEnd_810147 : Nat := 369773166042797359854851

theorem tailTrace_810147 : CollatzResearch.WordTrace tailWord_810147 prefixEnd_810147 369773166042797359854851 := by
  unfold tailWord_810147
  simp only [CollatzResearch.WordTrace]
  refine ⟨29548488595983255937140695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19698992397322170624760463 29548488595983255937140695)
  ·
    refine ⟨44322732893974883905711043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29548488595983255937140695 44322732893974883905711043)
    ·
      refine ⟨66484099340962325858566565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44322732893974883905711043 66484099340962325858566565)
      ·
        refine ⟨12465768626430436098481231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66484099340962325858566565 12465768626430436098481231)
        ·
          refine ⟨18698652939645654147721847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12465768626430436098481231 18698652939645654147721847)
          ·
            refine ⟨28047979409468481221582771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18698652939645654147721847 28047979409468481221582771)
            ·
              refine ⟨42071969114202721832374157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28047979409468481221582771 42071969114202721832374157)
              ·
                refine ⟨15776988417826020687140309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42071969114202721832374157 15776988417826020687140309)
                ·
                  refine ⟨369773166042797359854851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15776988417826020687140309 369773166042797359854851)
                  ·
                    rfl

theorem cell20_810147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 7].length) (baseStart_810147 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_810147 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_810147 prefixEnd_810147 := by exact prefixLift 810147
  have htrace : WordTrace (prefixWord ++ tailWord_810147) baseStart_810147 baseEnd_810147 := by
    simpa [prefixWord, tailWord_810147, baseEnd_810147] using wordTrace_append hprefix tailTrace_810147
  have hstable : (prefixWord ++ tailWord_810147).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810147).length < 2 ^ (prefixWord ++ tailWord_810147).sum := by decide
  have hdescent : baseEnd_810147 < baseStart_810147 := by decide
  rcases family_descends (prefixWord ++ tailWord_810147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810157 : List Nat := [1, 5, 2, 1, 3, 8]
def baseStart_810157 : Nat := 118140960795 + 810157 * 2 ^ 59
def prefixEnd_810157 : Nat := 4983230072969 + 3 ^ 40 * 810157 * 2
def baseEnd_810157 : Nat := 13695471493158584056351

theorem tailTrace_810157 : CollatzResearch.WordTrace tailWord_810157 prefixEnd_810157 13695471493158584056351 := by
  unfold tailWord_810157
  simp only [CollatzResearch.WordTrace]
  refine ⟨29548853325947027645004725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19699235550631351763336483 29548853325947027645004725)
  ·
    refine ⟨2770204999307533841719193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29548853325947027645004725 2770204999307533841719193)
    ·
      refine ⟨2077653749480650381289395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2770204999307533841719193 2077653749480650381289395)
      ·
        refine ⟨3116480624220975571934093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2077653749480650381289395 3116480624220975571934093)
        ·
          refine ⟨1168680234082865839475285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3116480624220975571934093 1168680234082865839475285)
          ·
            refine ⟨13695471493158584056351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1168680234082865839475285 13695471493158584056351)
            ·
              rfl

theorem cell20_810157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 8].length) (baseStart_810157 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_810157 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_810157 prefixEnd_810157 := by exact prefixLift 810157
  have htrace : WordTrace (prefixWord ++ tailWord_810157) baseStart_810157 baseEnd_810157 := by
    simpa [prefixWord, tailWord_810157, baseEnd_810157] using wordTrace_append hprefix tailTrace_810157
  have hstable : (prefixWord ++ tailWord_810157).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810157).length < 2 ^ (prefixWord ++ tailWord_810157).sum := by decide
  have hdescent : baseEnd_810157 < baseStart_810157 := by decide
  rcases family_descends (prefixWord ++ tailWord_810157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810174 : List Nat := [4, 2, 1, 1, 3, 3, 1, 5]
def baseStart_810174 : Nat := 118140960795 + 810174 * 2 ^ 59
def prefixEnd_810174 : Nat := 4983230072969 + 3 ^ 40 * 810174 * 2
def baseEnd_810174 : Nat := 123261829859501755318247

theorem tailTrace_810174 : CollatzResearch.WordTrace tailWord_810174 prefixEnd_810174 123261829859501755318247 := by
  unfold tailWord_810174
  simp only [CollatzResearch.WordTrace]
  refine ⟨3693684170860679943546697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19699648911256959698915717 3693684170860679943546697)
  ·
    refine ⟨2770263128145509957660023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3693684170860679943546697 2770263128145509957660023)
    ·
      refine ⟨4155394692218264936490035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2770263128145509957660023 4155394692218264936490035)
      ·
        refine ⟨6233092038327397404735053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4155394692218264936490035 6233092038327397404735053)
        ·
          refine ⟨2337409514372774026775645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6233092038327397404735053 2337409514372774026775645)
          ·
            refine ⟨876528567889790260040867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2337409514372774026775645 876528567889790260040867)
            ·
              refine ⟨1314792851834685390061301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 876528567889790260040867 1314792851834685390061301)
              ·
                refine ⟨123261829859501755318247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1314792851834685390061301 123261829859501755318247)
                ·
                  rfl

theorem cell20_810174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 5].length) (baseStart_810174 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_810174 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_810174 prefixEnd_810174 := by exact prefixLift 810174
  have htrace : WordTrace (prefixWord ++ tailWord_810174) baseStart_810174 baseEnd_810174 := by
    simpa [prefixWord, tailWord_810174, baseEnd_810174] using wordTrace_append hprefix tailTrace_810174
  have hstable : (prefixWord ++ tailWord_810174).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810174).length < 2 ^ (prefixWord ++ tailWord_810174).sum := by decide
  have hdescent : baseEnd_810174 < baseStart_810174 := by decide
  rcases family_descends (prefixWord ++ tailWord_810174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810215 : List Nat := [1, 1, 5, 3, 3, 1, 1, 2, 3]
def baseStart_810215 : Nat := 118140960795 + 810215 * 2 ^ 59
def prefixEnd_810215 : Nat := 4983230072969 + 3 ^ 40 * 810215 * 2
def baseEnd_810215 : Nat := 369804203095691345587907

theorem tailTrace_810215 : CollatzResearch.WordTrace tailWord_810215 prefixEnd_810215 369804203095691345587907 := by
  unfold tailWord_810215
  simp only [CollatzResearch.WordTrace]
  refine ⟨29550968759736903550616099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19700645839824602367077399 29550968759736903550616099)
  ·
    refine ⟨44326453139605355325924149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29550968759736903550616099 44326453139605355325924149)
    ·
      refine ⟨4155604981838002061805389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44326453139605355325924149 4155604981838002061805389)
      ·
        refine ⟨1558351868189250773177021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4155604981838002061805389 1558351868189250773177021)
        ·
          refine ⟨584381950570969039941383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1558351868189250773177021 584381950570969039941383)
          ·
            refine ⟨876572925856453559912075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 584381950570969039941383 876572925856453559912075)
            ·
              refine ⟨1314859388784680339868113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 876572925856453559912075 1314859388784680339868113)
              ·
                refine ⟨986144541588510254901085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1314859388784680339868113 986144541588510254901085)
                ·
                  refine ⟨369804203095691345587907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 986144541588510254901085 369804203095691345587907)
                  ·
                    rfl

theorem cell20_810215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 2, 3].length) (baseStart_810215 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_810215 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_810215 prefixEnd_810215 := by exact prefixLift 810215
  have htrace : WordTrace (prefixWord ++ tailWord_810215) baseStart_810215 baseEnd_810215 := by
    simpa [prefixWord, tailWord_810215, baseEnd_810215] using wordTrace_append hprefix tailTrace_810215
  have hstable : (prefixWord ++ tailWord_810215).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810215).length < 2 ^ (prefixWord ++ tailWord_810215).sum := by decide
  have hdescent : baseEnd_810215 < baseStart_810215 := by decide
  rcases family_descends (prefixWord ++ tailWord_810215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810216 : List Nat := [2, 1, 4, 1, 2, 1, 9]
def baseStart_810216 : Nat := 118140960795 + 810216 * 2 ^ 59
def prefixEnd_810216 : Nat := 4983230072969 + 3 ^ 40 * 810216 * 2
def baseEnd_810216 : Nat := 41089406613659976283841

theorem tailTrace_810216 : CollatzResearch.WordTrace tailWord_810216 prefixEnd_810216 41089406613659976283841 := by
  unfold tailWord_810216
  simp only [CollatzResearch.WordTrace]
  refine ⟨14775502616366640360701251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19700670155155520480935001 14775502616366640360701251)
  ·
    refine ⟨22163253924549960541051877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14775502616366640360701251 22163253924549960541051877)
    ·
      refine ⟨4155610110853117601447227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22163253924549960541051877 4155610110853117601447227)
      ·
        refine ⟨6233415166279676402170841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4155610110853117601447227 6233415166279676402170841)
        ·
          refine ⟨4675061374709757301628131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6233415166279676402170841 4675061374709757301628131)
          ·
            refine ⟨7012592062064635952442197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4675061374709757301628131 7012592062064635952442197)
            ·
              refine ⟨41089406613659976283841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7012592062064635952442197 41089406613659976283841)
              ·
                rfl

theorem cell20_810216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 9].length) (baseStart_810216 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_810216 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_810216 prefixEnd_810216 := by exact prefixLift 810216
  have htrace : WordTrace (prefixWord ++ tailWord_810216) baseStart_810216 baseEnd_810216 := by
    simpa [prefixWord, tailWord_810216, baseEnd_810216] using wordTrace_append hprefix tailTrace_810216
  have hstable : (prefixWord ++ tailWord_810216).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810216).length < 2 ^ (prefixWord ++ tailWord_810216).sum := by decide
  have hdescent : baseEnd_810216 < baseStart_810216 := by decide
  rcases family_descends (prefixWord ++ tailWord_810216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810219 : List Nat := [1, 1, 1, 1, 2, 8, 1, 2, 3]
def baseStart_810219 : Nat := 118140960795 + 810219 * 2 ^ 59
def prefixEnd_810219 : Nat := 4983230072969 + 3 ^ 40 * 810219 * 2
def baseEnd_810219 : Nat := 369806028804685109454557

theorem tailTrace_810219 : CollatzResearch.WordTrace tailWord_810219 prefixEnd_810219 369806028804685109454557 := by
  unfold tailWord_810219
  simp only [CollatzResearch.WordTrace]
  refine ⟨29551114651722412233761711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19700743101148274822507807 29551114651722412233761711)
  ·
    refine ⟨44326671977583618350642567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29551114651722412233761711 44326671977583618350642567)
    ·
      refine ⟨66490007966375427525963851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44326671977583618350642567 66490007966375427525963851)
      ·
        refine ⟨99735011949563141288945777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66490007966375427525963851 99735011949563141288945777)
        ·
          refine ⟨74801258962172355966709333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99735011949563141288945777 74801258962172355966709333)
          ·
            refine ⟨876577253462957296484875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 74801258962172355966709333 876577253462957296484875)
            ·
              refine ⟨1314865880194435944727313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 876577253462957296484875 1314865880194435944727313)
              ·
                refine ⟨986149410145826958545485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1314865880194435944727313 986149410145826958545485)
                ·
                  refine ⟨369806028804685109454557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 986149410145826958545485 369806028804685109454557)
                  ·
                    rfl

theorem cell20_810219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 2, 3].length) (baseStart_810219 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_810219 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_810219 prefixEnd_810219 := by exact prefixLift 810219
  have htrace : WordTrace (prefixWord ++ tailWord_810219) baseStart_810219 baseEnd_810219 := by
    simpa [prefixWord, tailWord_810219, baseEnd_810219] using wordTrace_append hprefix tailTrace_810219
  have hstable : (prefixWord ++ tailWord_810219).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810219).length < 2 ^ (prefixWord ++ tailWord_810219).sum := by decide
  have hdescent : baseEnd_810219 < baseStart_810219 := by decide
  rcases family_descends (prefixWord ++ tailWord_810219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810236 : List Nat := [2, 2, 2, 1, 5, 1, 3, 1, 3]
def baseStart_810236 : Nat := 118140960795 + 810236 * 2 ^ 59
def prefixEnd_810236 : Nat := 4983230072969 + 3 ^ 40 * 810236 * 2
def baseEnd_810236 : Nat := 369813788067908605887821

theorem tailTrace_810236 : CollatzResearch.WordTrace tailWord_810236 prefixEnd_810236 369813788067908605887821 := by
  unfold tailWord_810236
  simp only [CollatzResearch.WordTrace]
  refine ⟨14775867346330412068565281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19701156461773882758087041 14775867346330412068565281)
  ·
    refine ⟨11081900509747809051423961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14775867346330412068565281 11081900509747809051423961)
    ·
      refine ⟨8311425382310856788567971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11081900509747809051423961 8311425382310856788567971)
      ·
        refine ⟨12467138073466285182851957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8311425382310856788567971 12467138073466285182851957)
        ·
          refine ⟨1168794194387464235892371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12467138073466285182851957 1168794194387464235892371)
          ·
            refine ⟨1753191291581196353838557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1168794194387464235892371 1753191291581196353838557)
            ·
              refine ⟨657446734342948632689459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1753191291581196353838557 657446734342948632689459)
              ·
                refine ⟨986170101514422949034189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 657446734342948632689459 986170101514422949034189)
                ·
                  refine ⟨369813788067908605887821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 986170101514422949034189 369813788067908605887821)
                  ·
                    rfl

theorem cell20_810236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 3, 1, 3].length) (baseStart_810236 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_810236 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_810236 prefixEnd_810236 := by exact prefixLift 810236
  have htrace : WordTrace (prefixWord ++ tailWord_810236) baseStart_810236 baseEnd_810236 := by
    simpa [prefixWord, tailWord_810236, baseEnd_810236] using wordTrace_append hprefix tailTrace_810236
  have hstable : (prefixWord ++ tailWord_810236).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810236).length < 2 ^ (prefixWord ++ tailWord_810236).sum := by decide
  have hdescent : baseEnd_810236 < baseStart_810236 := by decide
  rcases family_descends (prefixWord ++ tailWord_810236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810271 : List Nat := [1, 1, 2, 4, 4, 2, 6]
def baseStart_810271 : Nat := 118140960795 + 810271 * 2 ^ 59
def prefixEnd_810271 : Nat := 4983230072969 + 3 ^ 40 * 810271 * 2
def baseEnd_810271 : Nat := 41092195891289337746779

theorem tailTrace_810271 : CollatzResearch.WordTrace tailWord_810271 prefixEnd_810271 41092195891289337746779 := by
  unfold tailWord_810271
  simp only [CollatzResearch.WordTrace]
  refine ⟨29553011247534025114654667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19702007498356016743103111 29553011247534025114654667)
  ·
    refine ⟨44329516871301037671982001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29553011247534025114654667 44329516871301037671982001)
    ·
      refine ⟨33247137653475778253986501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44329516871301037671982001 33247137653475778253986501)
      ·
        refine ⟨6233838310026708422622469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33247137653475778253986501 6233838310026708422622469)
        ·
          refine ⟨1168844683130007829241713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6233838310026708422622469 1168844683130007829241713)
          ·
            refine ⟨876633512347505871931285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1168844683130007829241713 876633512347505871931285)
            ·
              refine ⟨41092195891289337746779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 876633512347505871931285 41092195891289337746779)
              ·
                rfl

theorem cell20_810271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 6].length) (baseStart_810271 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_810271 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_810271 prefixEnd_810271 := by exact prefixLift 810271
  have htrace : WordTrace (prefixWord ++ tailWord_810271) baseStart_810271 baseEnd_810271 := by
    simpa [prefixWord, tailWord_810271, baseEnd_810271] using wordTrace_append hprefix tailTrace_810271
  have hstable : (prefixWord ++ tailWord_810271).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810271).length < 2 ^ (prefixWord ++ tailWord_810271).sum := by decide
  have hdescent : baseEnd_810271 < baseStart_810271 := by decide
  rcases family_descends (prefixWord ++ tailWord_810271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810336 : List Nat := [2, 1, 1, 3, 4, 3, 2, 2, 2]
def baseStart_810336 : Nat := 118140960795 + 810336 * 2 ^ 59
def prefixEnd_810336 : Nat := 4983230072969 + 3 ^ 40 * 810336 * 2
def baseEnd_810336 : Nat := 369859430792752702554079

theorem tailTrace_810336 : CollatzResearch.WordTrace tailWord_810336 prefixEnd_810336 369859430792752702554079 := by
  unfold tailWord_810336
  simp only [CollatzResearch.WordTrace]
  refine ⟨14777690996149270607885431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19703587994865694143847241 14777690996149270607885431)
  ·
    refine ⟨22166536494223905911828147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14777690996149270607885431 22166536494223905911828147)
    ·
      refine ⟨33249804741335858867742221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22166536494223905911828147 33249804741335858867742221)
      ·
        refine ⟨12468676778000947075403333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33249804741335858867742221 12468676778000947075403333)
        ·
          refine ⟨2337876895875177576638125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12468676778000947075403333 2337876895875177576638125)
          ·
            refine ⟨876703835953191591239297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2337876895875177576638125 876703835953191591239297)
            ·
              refine ⟨657527876964893693429473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 876703835953191591239297 657527876964893693429473)
              ·
                refine ⟨493145907723670270072105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 657527876964893693429473 493145907723670270072105)
                ·
                  refine ⟨369859430792752702554079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 493145907723670270072105 369859430792752702554079)
                  ·
                    rfl

theorem cell20_810336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 2, 2, 2].length) (baseStart_810336 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_810336 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_810336 prefixEnd_810336 := by exact prefixLift 810336
  have htrace : WordTrace (prefixWord ++ tailWord_810336) baseStart_810336 baseEnd_810336 := by
    simpa [prefixWord, tailWord_810336, baseEnd_810336] using wordTrace_append hprefix tailTrace_810336
  have hstable : (prefixWord ++ tailWord_810336).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810336).length < 2 ^ (prefixWord ++ tailWord_810336).sum := by decide
  have hdescent : baseEnd_810336 < baseStart_810336 := by decide
  rcases family_descends (prefixWord ++ tailWord_810336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810337 : List Nat := [1, 2, 3, 1, 1, 1, 1, 5, 5]
def baseStart_810337 : Nat := 118140960795 + 810337 * 2 ^ 59
def prefixEnd_810337 : Nat := 4983230072969 + 3 ^ 40 * 810337 * 2
def baseEnd_810337 : Nat := 369859887220001143520741

theorem tailTrace_810337 : CollatzResearch.WordTrace tailWord_810337 prefixEnd_810337 369859887220001143520741 := by
  unfold tailWord_810337
  simp only [CollatzResearch.WordTrace]
  refine ⟨29555418465294918386557265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19703612310196612257704843 29555418465294918386557265)
  ·
    refine ⟨22166563848971188789917949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29555418465294918386557265 22166563848971188789917949)
    ·
      refine ⟨8312461443364195796219231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22166563848971188789917949 8312461443364195796219231)
      ·
        refine ⟨12468692165046293694328847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8312461443364195796219231 12468692165046293694328847)
        ·
          refine ⟨18703038247569440541493271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12468692165046293694328847 18703038247569440541493271)
          ·
            refine ⟨28054557371354160812239907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18703038247569440541493271 28054557371354160812239907)
            ·
              refine ⟨42081836057031241218359861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28054557371354160812239907 42081836057031241218359861)
              ·
                refine ⟨3945172130346678864221237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42081836057031241218359861 3945172130346678864221237)
                ·
                  refine ⟨369859887220001143520741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3945172130346678864221237 369859887220001143520741)
                  ·
                    rfl

theorem cell20_810337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 5, 5].length) (baseStart_810337 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_810337 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_810337 prefixEnd_810337 := by exact prefixLift 810337
  have htrace : WordTrace (prefixWord ++ tailWord_810337) baseStart_810337 baseEnd_810337 := by
    simpa [prefixWord, tailWord_810337, baseEnd_810337] using wordTrace_append hprefix tailTrace_810337
  have hstable : (prefixWord ++ tailWord_810337).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810337).length < 2 ^ (prefixWord ++ tailWord_810337).sum := by decide
  have hdescent : baseEnd_810337 < baseStart_810337 := by decide
  rcases family_descends (prefixWord ++ tailWord_810337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810354 : List Nat := [3, 2, 1, 2, 1, 2, 1, 5, 3]
def baseStart_810354 : Nat := 118140960795 + 810354 * 2 ^ 59
def prefixEnd_810354 : Nat := 4983230072969 + 3 ^ 40 * 810354 * 2
def baseEnd_810354 : Nat := 369867646483224639954005

theorem tailTrace_810354 : CollatzResearch.WordTrace tailWord_810354 prefixEnd_810354 369867646483224639954005 := by
  unfold tailWord_810354
  simp only [CollatzResearch.WordTrace]
  refine ⟨7389009626558332572481529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19704025670822220193284077 7389009626558332572481529)
  ·
    refine ⟨5541757219918749429361147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7389009626558332572481529 5541757219918749429361147)
    ·
      refine ⟨8312635829878124144041721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5541757219918749429361147 8312635829878124144041721)
      ·
        refine ⟨6234476872408593108031291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8312635829878124144041721 6234476872408593108031291)
        ·
          refine ⟨9351715308612889662046937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6234476872408593108031291 9351715308612889662046937)
          ·
            refine ⟨7013786481459667246535203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9351715308612889662046937 7013786481459667246535203)
            ·
              refine ⟨10520679722189500869802805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7013786481459667246535203 10520679722189500869802805)
              ·
                refine ⟨986313723955265706544013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10520679722189500869802805 986313723955265706544013)
                ·
                  refine ⟨369867646483224639954005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 986313723955265706544013 369867646483224639954005)
                  ·
                    rfl

theorem cell20_810354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 5, 3].length) (baseStart_810354 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_810354 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_810354 prefixEnd_810354 := by exact prefixLift 810354
  have htrace : WordTrace (prefixWord ++ tailWord_810354) baseStart_810354 baseEnd_810354 := by
    simpa [prefixWord, tailWord_810354, baseEnd_810354] using wordTrace_append hprefix tailTrace_810354
  have hstable : (prefixWord ++ tailWord_810354).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810354).length < 2 ^ (prefixWord ++ tailWord_810354).sum := by decide
  have hdescent : baseEnd_810354 < baseStart_810354 := by decide
  rcases family_descends (prefixWord ++ tailWord_810354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810388 : List Nat := [2, 4, 2, 1, 2, 3, 1, 2, 3]
def baseStart_810388 : Nat := 118140960795 + 810388 * 2 ^ 59
def prefixEnd_810388 : Nat := 4983230072969 + 3 ^ 40 * 810388 * 2
def baseEnd_810388 : Nat := 369883165009671632820533

theorem tailTrace_810388 : CollatzResearch.WordTrace tailWord_810388 prefixEnd_810388 369883165009671632820533 := by
  unfold tailWord_810388
  simp only [CollatzResearch.WordTrace]
  refine ⟨14778639294055077048331909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19704852392073436064442545 14778639294055077048331909)
  ·
    refine ⟨2770994867635326946562233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14778639294055077048331909 2770994867635326946562233)
    ·
      refine ⟨2078246150726495209921675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2770994867635326946562233 2078246150726495209921675)
      ·
        refine ⟨3117369226089742814882513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2078246150726495209921675 3117369226089742814882513)
        ·
          refine ⟨2338026919567307111161885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3117369226089742814882513 2338026919567307111161885)
          ·
            refine ⟨876760094837740166685707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2338026919567307111161885 876760094837740166685707)
            ·
              refine ⟨1315140142256610250028561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 876760094837740166685707 1315140142256610250028561)
              ·
                refine ⟨986355106692457687521421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1315140142256610250028561 986355106692457687521421)
                ·
                  refine ⟨369883165009671632820533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 986355106692457687521421 369883165009671632820533)
                  ·
                    rfl

theorem cell20_810388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 2, 3].length) (baseStart_810388 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_810388 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_810388 prefixEnd_810388 := by exact prefixLift 810388
  have htrace : WordTrace (prefixWord ++ tailWord_810388) baseStart_810388 baseEnd_810388 := by
    simpa [prefixWord, tailWord_810388, baseEnd_810388] using wordTrace_append hprefix tailTrace_810388
  have hstable : (prefixWord ++ tailWord_810388).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810388).length < 2 ^ (prefixWord ++ tailWord_810388).sum := by decide
  have hdescent : baseEnd_810388 < baseStart_810388 := by decide
  rcases family_descends (prefixWord ++ tailWord_810388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810399 : List Nat := [1, 1, 2, 5, 1, 2, 1, 3, 4]
def baseStart_810399 : Nat := 118140960795 + 810399 * 2 ^ 59
def prefixEnd_810399 : Nat := 4983230072969 + 3 ^ 40 * 810399 * 2
def baseEnd_810399 : Nat := 369888185709404483453821

theorem tailTrace_810399 : CollatzResearch.WordTrace tailWord_810399 prefixEnd_810399 369888185709404483453821 := by
  unfold tailWord_810399
  simp only [CollatzResearch.WordTrace]
  refine ⟨29557679791070302975314251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19705119860713535316876167 29557679791070302975314251)
  ·
    refine ⟨44336519686605454462971377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29557679791070302975314251 44336519686605454462971377)
    ·
      refine ⟨33252389764954090847228533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44336519686605454462971377 33252389764954090847228533)
      ·
        refine ⟨3117411540464446016927675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33252389764954090847228533 3117411540464446016927675)
        ·
          refine ⟨4676117310696669025391513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3117411540464446016927675 4676117310696669025391513)
          ·
            refine ⟨3507087983022501769043635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4676117310696669025391513 3507087983022501769043635)
            ·
              refine ⟨5260631974533752653565453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3507087983022501769043635 5260631974533752653565453)
              ·
                refine ⟨1972736990450157245087045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5260631974533752653565453 1972736990450157245087045)
                ·
                  refine ⟨369888185709404483453821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1972736990450157245087045 369888185709404483453821)
                  ·
                    rfl

theorem cell20_810399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 3, 4].length) (baseStart_810399 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_810399 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_810399 prefixEnd_810399 := by exact prefixLift 810399
  have htrace : WordTrace (prefixWord ++ tailWord_810399) baseStart_810399 baseEnd_810399 := by
    simpa [prefixWord, tailWord_810399, baseEnd_810399] using wordTrace_append hprefix tailTrace_810399
  have hstable : (prefixWord ++ tailWord_810399).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810399).length < 2 ^ (prefixWord ++ tailWord_810399).sum := by decide
  have hdescent : baseEnd_810399 < baseStart_810399 := by decide
  rcases family_descends (prefixWord ++ tailWord_810399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810444 : List Nat := [2, 2, 1, 4, 2, 1, 8]
def baseStart_810444 : Nat := 118140960795 + 810444 * 2 ^ 59
def prefixEnd_810444 : Nat := 4983230072969 + 3 ^ 40 * 810444 * 2
def baseEnd_810444 : Nat := 41100969437287147439293

theorem tailTrace_810444 : CollatzResearch.WordTrace tailWord_810444 prefixEnd_810444 41100969437287147439293 := by
  unfold tailWord_810444
  simp only [CollatzResearch.WordTrace]
  refine ⟨14779660537953637830351193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19706214050604850440468257 14779660537953637830351193)
  ·
    refine ⟨11084745403465228372763395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14779660537953637830351193 11084745403465228372763395)
    ·
      refine ⟨16627118105197842559145093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11084745403465228372763395 16627118105197842559145093)
      ·
        refine ⟨3117584644724595479839705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16627118105197842559145093 3117584644724595479839705)
        ·
          refine ⟨2338188483543446609879779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3117584644724595479839705 2338188483543446609879779)
          ·
            refine ⟨3507282725315169914819669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2338188483543446609879779 3507282725315169914819669)
            ·
              refine ⟨41100969437287147439293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3507282725315169914819669 41100969437287147439293)
              ·
                rfl

theorem cell20_810444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 8].length) (baseStart_810444 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_810444 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_810444 prefixEnd_810444 := by exact prefixLift 810444
  have htrace : WordTrace (prefixWord ++ tailWord_810444) baseStart_810444 baseEnd_810444 := by
    simpa [prefixWord, tailWord_810444, baseEnd_810444] using wordTrace_append hprefix tailTrace_810444
  have hstable : (prefixWord ++ tailWord_810444).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810444).length < 2 ^ (prefixWord ++ tailWord_810444).sum := by decide
  have hdescent : baseEnd_810444 < baseStart_810444 := by decide
  rcases family_descends (prefixWord ++ tailWord_810444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810461 : List Nat := [1, 4, 3, 1, 1, 3, 2, 5]
def baseStart_810461 : Nat := 118140960795 + 810461 * 2 ^ 59
def prefixEnd_810461 : Nat := 4983230072969 + 3 ^ 40 * 810461 * 2
def baseEnd_810461 : Nat := 123305494732935941128967

theorem tailTrace_810461 : CollatzResearch.WordTrace tailWord_810461 prefixEnd_810461 123305494732935941128967 := by
  unfold tailWord_810461
  simp only [CollatzResearch.WordTrace]
  refine ⟨29559941116845687564071237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19706627411230458376047491 29559941116845687564071237)
  ·
    refine ⟨5542488959408566418263357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29559941116845687564071237 5542488959408566418263357)
    ·
      refine ⟨2078433359778212406848759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5542488959408566418263357 2078433359778212406848759)
      ·
        refine ⟨3117650039667318610273139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2078433359778212406848759 3117650039667318610273139)
        ·
          refine ⟨4676475059500977915409709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3117650039667318610273139 4676475059500977915409709)
          ·
            refine ⟨1753678147312866718278641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4676475059500977915409709 1753678147312866718278641)
            ·
              refine ⟨1315258610484650038708981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1753678147312866718278641 1315258610484650038708981)
              ·
                refine ⟨123305494732935941128967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1315258610484650038708981 123305494732935941128967)
                ·
                  rfl

theorem cell20_810461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 5].length) (baseStart_810461 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_810461 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_810461 prefixEnd_810461 := by exact prefixLift 810461
  have htrace : WordTrace (prefixWord ++ tailWord_810461) baseStart_810461 baseEnd_810461 := by
    simpa [prefixWord, tailWord_810461, baseEnd_810461] using wordTrace_append hprefix tailTrace_810461
  have hstable : (prefixWord ++ tailWord_810461).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810461).length < 2 ^ (prefixWord ++ tailWord_810461).sum := by decide
  have hdescent : baseEnd_810461 < baseStart_810461 := by decide
  rcases family_descends (prefixWord ++ tailWord_810461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810506 : List Nat := [3, 1, 2, 2, 2, 2, 1, 4, 3]
def baseStart_810506 : Nat := 118140960795 + 810506 * 2 ^ 59
def prefixEnd_810506 : Nat := 4983230072969 + 3 ^ 40 * 810506 * 2
def baseEnd_810506 : Nat := 369937023424987666886717

theorem tailTrace_810506 : CollatzResearch.WordTrace tailWord_810506 prefixEnd_810506 369937023424987666886717 := by
  unfold tailWord_810506
  simp only [CollatzResearch.WordTrace]
  refine ⟨7390395600420665062364843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19707721601121773499639581 7390395600420665062364843)
  ·
    refine ⟨11085593400630997593547265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7390395600420665062364843 11085593400630997593547265)
    ·
      refine ⟨8314195050473248195160449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11085593400630997593547265 8314195050473248195160449)
      ·
        refine ⟨6235646287854936146370337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8314195050473248195160449 6235646287854936146370337)
        ·
          refine ⟨4676734715891202109777753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6235646287854936146370337 4676734715891202109777753)
          ·
            refine ⟨3507551036918401582333315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4676734715891202109777753 3507551036918401582333315)
            ·
              refine ⟨5261326555377602373499973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3507551036918401582333315 5261326555377602373499973)
              ·
                refine ⟨986498729133300445031245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5261326555377602373499973 986498729133300445031245)
                ·
                  refine ⟨369937023424987666886717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 986498729133300445031245 369937023424987666886717)
                  ·
                    rfl

theorem cell20_810506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 4, 3].length) (baseStart_810506 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_810506 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_810506 prefixEnd_810506 := by exact prefixLift 810506
  have htrace : WordTrace (prefixWord ++ tailWord_810506) baseStart_810506 baseEnd_810506 := by
    simpa [prefixWord, tailWord_810506, baseEnd_810506] using wordTrace_append hprefix tailTrace_810506
  have hstable : (prefixWord ++ tailWord_810506).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810506).length < 2 ^ (prefixWord ++ tailWord_810506).sum := by decide
  have hdescent : baseEnd_810506 < baseStart_810506 := by decide
  rcases family_descends (prefixWord ++ tailWord_810506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810565 : List Nat := [1, 3, 1, 1, 1, 4, 3, 1, 5]
def baseStart_810565 : Nat := 118140960795 + 810565 * 2 ^ 59
def prefixEnd_810565 : Nat := 4983230072969 + 3 ^ 40 * 810565 * 2
def baseEnd_810565 : Nat := 369963952632645683919809

theorem tailTrace_810565 : CollatzResearch.WordTrace tailWord_810565 prefixEnd_810565 369963952632645683919809 := by
  unfold tailWord_810565
  simp only [CollatzResearch.WordTrace]
  refine ⟨29563734308468913325857149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19709156205645942217238099 29563734308468913325857149)
  ·
    refine ⟨11086400365675842497196431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29563734308468913325857149 11086400365675842497196431)
    ·
      refine ⟨16629600548513763745794647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11086400365675842497196431 16629600548513763745794647)
      ·
        refine ⟨24944400822770645618691971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16629600548513763745794647 24944400822770645618691971)
        ·
          refine ⟨37416601234155968428037957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24944400822770645618691971 37416601234155968428037957)
          ·
            refine ⟨7015612731404244080257117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37416601234155968428037957 7015612731404244080257117)
            ·
              refine ⟨2630854774276591530096419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7015612731404244080257117 2630854774276591530096419)
              ·
                refine ⟨3946282161414887295144629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2630854774276591530096419 3946282161414887295144629)
                ·
                  refine ⟨369963952632645683919809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3946282161414887295144629 369963952632645683919809)
                  ·
                    rfl

theorem cell20_810565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 1, 5].length) (baseStart_810565 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_810565 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_810565 prefixEnd_810565 := by exact prefixLift 810565
  have htrace : WordTrace (prefixWord ++ tailWord_810565) baseStart_810565 baseEnd_810565 := by
    simpa [prefixWord, tailWord_810565, baseEnd_810565] using wordTrace_append hprefix tailTrace_810565
  have hstable : (prefixWord ++ tailWord_810565).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810565).length < 2 ^ (prefixWord ++ tailWord_810565).sum := by decide
  have hdescent : baseEnd_810565 < baseStart_810565 := by decide
  rcases family_descends (prefixWord ++ tailWord_810565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810596 : List Nat := [2, 3, 1, 1, 2, 4, 1, 6]
def baseStart_810596 : Nat := 118140960795 + 810596 * 2 ^ 59
def prefixEnd_810596 : Nat := 4983230072969 + 3 ^ 40 * 810596 * 2
def baseEnd_810596 : Nat := 123326033959115784628783

theorem tailTrace_810596 : CollatzResearch.WordTrace tailWord_810596 prefixEnd_810596 123326033959115784628783 := by
  unfold tailWord_810596
  simp only [CollatzResearch.WordTrace]
  refine ⟨14782432485678302810117821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19709909980904403746823761 14782432485678302810117821)
  ·
    refine ⟨5543412182129363553794183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14782432485678302810117821 5543412182129363553794183)
    ·
      refine ⟨8315118273194045330691275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5543412182129363553794183 8315118273194045330691275)
      ·
        refine ⟨12472677409791067996036913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8315118273194045330691275 12472677409791067996036913)
        ·
          refine ⟨9354508057343300997027685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12472677409791067996036913 9354508057343300997027685)
          ·
            refine ⟨1753970260751868936942691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9354508057343300997027685 1753970260751868936942691)
            ·
              refine ⟨2630955391127803405414037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1753970260751868936942691 2630955391127803405414037)
              ·
                refine ⟨123326033959115784628783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2630955391127803405414037 123326033959115784628783)
                ·
                  rfl

theorem cell20_810596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 6].length) (baseStart_810596 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_810596 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_810596 prefixEnd_810596 := by exact prefixLift 810596
  have htrace : WordTrace (prefixWord ++ tailWord_810596) baseStart_810596 baseEnd_810596 := by
    simpa [prefixWord, tailWord_810596, baseEnd_810596] using wordTrace_append hprefix tailTrace_810596
  have hstable : (prefixWord ++ tailWord_810596).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810596).length < 2 ^ (prefixWord ++ tailWord_810596).sum := by decide
  have hdescent : baseEnd_810596 < baseStart_810596 := by decide
  rcases family_descends (prefixWord ++ tailWord_810596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810613 : List Nat := [1, 3, 4, 2, 1, 3, 6]
def baseStart_810613 : Nat := 118140960795 + 810613 * 2 ^ 59
def prefixEnd_810613 : Nat := 4983230072969 + 3 ^ 40 * 810613 * 2
def baseEnd_810613 : Nat := 41109540126730094479957

theorem tailTrace_810613 : CollatzResearch.WordTrace tailWord_810613 prefixEnd_810613 41109540126730094479957 := by
  unfold tailWord_810613
  simp only [CollatzResearch.WordTrace]
  refine ⟨29565485012295017523604493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19710323341530011682402995 29565485012295017523604493)
  ·
    refine ⟨11087056879610631571351685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29565485012295017523604493 11087056879610631571351685)
    ·
      refine ⟨2078823164926993419628441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11087056879610631571351685 2078823164926993419628441)
      ·
        refine ⟨1559117373695245064721331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2078823164926993419628441 1559117373695245064721331)
        ·
          refine ⟨2338676060542867597081997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1559117373695245064721331 2338676060542867597081997)
          ·
            refine ⟨877003522703575348905749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2338676060542867597081997 877003522703575348905749)
            ·
              refine ⟨41109540126730094479957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 877003522703575348905749 41109540126730094479957)
              ·
                rfl

theorem cell20_810613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 6].length) (baseStart_810613 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_810613 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_810613 prefixEnd_810613 := by exact prefixLift 810613
  have htrace : WordTrace (prefixWord ++ tailWord_810613) baseStart_810613 baseEnd_810613 := by
    simpa [prefixWord, tailWord_810613, baseEnd_810613] using wordTrace_append hprefix tailTrace_810613
  have hstable : (prefixWord ++ tailWord_810613).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810613).length < 2 ^ (prefixWord ++ tailWord_810613).sum := by decide
  have hdescent : baseEnd_810613 < baseStart_810613 := by decide
  rcases family_descends (prefixWord ++ tailWord_810613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810634 : List Nat := [3, 1, 2, 3, 2, 1, 1, 7]
def baseStart_810634 : Nat := 118140960795 + 810634 * 2 ^ 59
def prefixEnd_810634 : Nat := 4983230072969 + 3 ^ 40 * 810634 * 2
def baseEnd_810634 : Nat := 123331815370929370206509

theorem tailTrace_810634 : CollatzResearch.WordTrace tailWord_810634 prefixEnd_810634 123331815370929370206509 := by
  unfold tailWord_810634
  simp only [CollatzResearch.WordTrace]
  refine ⟨7391562736304734527529739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19710833963479292073412637 7391562736304734527529739)
  ·
    refine ⟨11087344104457101791294609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7391562736304734527529739 11087344104457101791294609)
    ·
      refine ⟨8315508078342826343470957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11087344104457101791294609 8315508078342826343470957)
      ·
        refine ⟨3118315529378559878801609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8315508078342826343470957 3118315529378559878801609)
        ·
          refine ⟨2338736647033919909101207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3118315529378559878801609 2338736647033919909101207)
          ·
            refine ⟨3508104970550879863651811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2338736647033919909101207 3508104970550879863651811)
            ·
              refine ⟨5262157455826319795477717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3508104970550879863651811 5262157455826319795477717)
              ·
                refine ⟨123331815370929370206509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5262157455826319795477717 123331815370929370206509)
                ·
                  rfl

theorem cell20_810634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 7].length) (baseStart_810634 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_810634 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_810634 prefixEnd_810634 := by exact prefixLift 810634
  have htrace : WordTrace (prefixWord ++ tailWord_810634) baseStart_810634 baseEnd_810634 := by
    simpa [prefixWord, tailWord_810634, baseEnd_810634] using wordTrace_append hprefix tailTrace_810634
  have hstable : (prefixWord ++ tailWord_810634).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810634).length < 2 ^ (prefixWord ++ tailWord_810634).sum := by decide
  have hdescent : baseEnd_810634 < baseStart_810634 := by decide
  rcases family_descends (prefixWord ++ tailWord_810634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810678 : List Nat := [5, 1, 3, 1, 1, 2, 1, 4, 2]
def baseStart_810678 : Nat := 118140960795 + 810678 * 2 ^ 59
def prefixEnd_810678 : Nat := 4983230072969 + 3 ^ 40 * 810678 * 2
def baseEnd_810678 : Nat := 370015528911719513152681

theorem tailTrace_810678 : CollatzResearch.WordTrace tailWord_810678 prefixEnd_810678 370015528911719513152681 := by
  unfold tailWord_810678
  simp only [CollatzResearch.WordTrace]
  refine ⟨1847990984816220851545043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19711903838039689083147125 1847990984816220851545043)
  ·
    refine ⟨2771986477224331277317565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1847990984816220851545043 2771986477224331277317565)
    ·
      refine ⟨1039494928959124228994087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2771986477224331277317565 1039494928959124228994087)
      ·
        refine ⟨1559242393438686343491131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1039494928959124228994087 1559242393438686343491131)
        ·
          refine ⟨2338863590158029515236697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1559242393438686343491131 2338863590158029515236697)
          ·
            refine ⟨1754147692618522136427523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2338863590158029515236697 1754147692618522136427523)
            ·
              refine ⟨2631221538927783204641285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1754147692618522136427523 2631221538927783204641285)
              ·
                refine ⟨493354038548959350870241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2631221538927783204641285 493354038548959350870241)
                ·
                  refine ⟨370015528911719513152681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 493354038548959350870241 370015528911719513152681)
                  ·
                    rfl

theorem cell20_810678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 4, 2].length) (baseStart_810678 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_810678 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_810678 prefixEnd_810678 := by exact prefixLift 810678
  have htrace : WordTrace (prefixWord ++ tailWord_810678) baseStart_810678 baseEnd_810678 := by
    simpa [prefixWord, tailWord_810678, baseEnd_810678] using wordTrace_append hprefix tailTrace_810678
  have hstable : (prefixWord ++ tailWord_810678).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810678).length < 2 ^ (prefixWord ++ tailWord_810678).sum := by decide
  have hdescent : baseEnd_810678 < baseStart_810678 := by decide
  rcases family_descends (prefixWord ++ tailWord_810678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810682 : List Nat := [3, 1, 1, 1, 2, 5, 1, 4, 2]
def baseStart_810682 : Nat := 118140960795 + 810682 * 2 ^ 59
def prefixEnd_810682 : Nat := 4983230072969 + 3 ^ 40 * 810682 * 2
def baseEnd_810682 : Nat := 370017354620713277019331

theorem tailTrace_810682 : CollatzResearch.WordTrace tailWord_810682 prefixEnd_810682 370017354620713277019331 := by
  unfold tailWord_810682
  simp only [CollatzResearch.WordTrace]
  refine ⟨7392000412261260576966575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19712001099363361538577533 7392000412261260576966575)
  ·
    refine ⟨11088000618391890865449863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7392000412261260576966575 11088000618391890865449863)
    ·
      refine ⟨16632000927587836298174795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11088000618391890865449863 16632000927587836298174795)
      ·
        refine ⟨24948001391381754447262193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16632000927587836298174795 24948001391381754447262193)
        ·
          refine ⟨18711001043536315835446645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24948001391381754447262193 18711001043536315835446645)
          ·
            refine ⟨1754156347831529609573123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18711001043536315835446645 1754156347831529609573123)
            ·
              refine ⟨2631234521747294414359685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1754156347831529609573123 2631234521747294414359685)
              ·
                refine ⟨493356472827617702692441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2631234521747294414359685 493356472827617702692441)
                ·
                  refine ⟨370017354620713277019331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 493356472827617702692441 370017354620713277019331)
                  ·
                    rfl

theorem cell20_810682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 4, 2].length) (baseStart_810682 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_810682 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_810682 prefixEnd_810682 := by exact prefixLift 810682
  have htrace : WordTrace (prefixWord ++ tailWord_810682) baseStart_810682 baseEnd_810682 := by
    simpa [prefixWord, tailWord_810682, baseEnd_810682] using wordTrace_append hprefix tailTrace_810682
  have hstable : (prefixWord ++ tailWord_810682).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810682).length < 2 ^ (prefixWord ++ tailWord_810682).sum := by decide
  have hdescent : baseEnd_810682 < baseStart_810682 := by decide
  rcases family_descends (prefixWord ++ tailWord_810682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810716 : List Nat := [2, 2, 5, 1, 2, 1, 2, 3, 2]
def baseStart_810716 : Nat := 118140960795 + 810716 * 2 ^ 59
def prefixEnd_810716 : Nat := 4983230072969 + 3 ^ 40 * 810716 * 2
def baseEnd_810716 : Nat := 370032873147160269885859

theorem tailTrace_810716 : CollatzResearch.WordTrace tailWord_810716 prefixEnd_810716 370032873147160269885859 := by
  unfold tailWord_810716
  simp only [CollatzResearch.WordTrace]
  refine ⟨14784620865460933057302001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19712827820614577409736001 14784620865460933057302001)
  ·
    refine ⟨11088465649095699792976501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14784620865460933057302001 11088465649095699792976501)
    ·
      refine ⟨1039543654602721855591547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11088465649095699792976501 1039543654602721855591547)
      ·
        refine ⟨1559315481904082783387321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1039543654602721855591547 1559315481904082783387321)
        ·
          refine ⟨1169486611428062087540491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1559315481904082783387321 1169486611428062087540491)
          ·
            refine ⟨1754229917142093131310737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1169486611428062087540491 1754229917142093131310737)
            ·
              refine ⟨1315672437856569848483053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1754229917142093131310737 1315672437856569848483053)
              ·
                refine ⟨493377164196213693181145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1315672437856569848483053 493377164196213693181145)
                ·
                  refine ⟨370032873147160269885859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 493377164196213693181145 370032873147160269885859)
                  ·
                    rfl

theorem cell20_810716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 3, 2].length) (baseStart_810716 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_810716 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_810716 prefixEnd_810716 := by exact prefixLift 810716
  have htrace : WordTrace (prefixWord ++ tailWord_810716) baseStart_810716 baseEnd_810716 := by
    simpa [prefixWord, tailWord_810716, baseEnd_810716] using wordTrace_append hprefix tailTrace_810716
  have hstable : (prefixWord ++ tailWord_810716).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810716).length < 2 ^ (prefixWord ++ tailWord_810716).sum := by decide
  have hdescent : baseEnd_810716 < baseStart_810716 := by decide
  rcases family_descends (prefixWord ++ tailWord_810716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810724 : List Nat := [2, 3, 1, 1, 1, 3, 1, 2, 6]
def baseStart_810724 : Nat := 118140960795 + 810724 * 2 ^ 59
def prefixEnd_810724 : Nat := 4983230072969 + 3 ^ 40 * 810724 * 2
def baseEnd_810724 : Nat := 370036524565147797619159

theorem tailTrace_810724 : CollatzResearch.WordTrace tailWord_810724 prefixEnd_810724 370036524565147797619159 := by
  unfold tailWord_810724
  simp only [CollatzResearch.WordTrace]
  refine ⟨14784766757446441740447613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19713022343261922320596817 14784766757446441740447613)
  ·
    refine ⟨5544287534042415652667855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14784766757446441740447613 5544287534042415652667855)
    ·
      refine ⟨8316431301063623479001783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5544287534042415652667855 8316431301063623479001783)
      ·
        refine ⟨12474646951595435218502675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8316431301063623479001783 12474646951595435218502675)
        ·
          refine ⟨18711970427393152827754013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12474646951595435218502675 18711970427393152827754013)
          ·
            refine ⟨7016988910272432310407755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18711970427393152827754013 7016988910272432310407755)
            ·
              refine ⟨10525483365408648465611633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7016988910272432310407755 10525483365408648465611633)
              ·
                refine ⟨7894112524056486349208725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10525483365408648465611633 7894112524056486349208725)
                ·
                  refine ⟨370036524565147797619159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7894112524056486349208725 370036524565147797619159)
                  ·
                    rfl

theorem cell20_810724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_810724 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_810724 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_810724 prefixEnd_810724 := by exact prefixLift 810724
  have htrace : WordTrace (prefixWord ++ tailWord_810724) baseStart_810724 baseEnd_810724 := by
    simpa [prefixWord, tailWord_810724, baseEnd_810724] using wordTrace_append hprefix tailTrace_810724
  have hstable : (prefixWord ++ tailWord_810724).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810724).length < 2 ^ (prefixWord ++ tailWord_810724).sum := by decide
  have hdescent : baseEnd_810724 < baseStart_810724 := by decide
  rcases family_descends (prefixWord ++ tailWord_810724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810727 : List Nat := [1, 1, 5, 4, 1, 1, 7]
def baseStart_810727 : Nat := 118140960795 + 810727 * 2 ^ 59
def prefixEnd_810727 : Nat := 4983230072969 + 3 ^ 40 * 810727 * 2
def baseEnd_810727 : Nat := 41115321538543680057683

theorem tailTrace_810727 : CollatzResearch.WordTrace tailWord_810727 prefixEnd_810727 41115321538543680057683 := by
  unfold tailWord_810727
  simp only [CollatzResearch.WordTrace]
  refine ⟨29569642933882014993254435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19713095289254676662169623 29569642933882014993254435)
  ·
    refine ⟨44354464400823022489881653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29569642933882014993254435 44354464400823022489881653)
    ·
      refine ⟨4158231037577158358426405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44354464400823022489881653 4158231037577158358426405)
      ·
        refine ⟨779668319545717192204951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4158231037577158358426405 779668319545717192204951)
        ·
          refine ⟨1169502479318575788307427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 779668319545717192204951 1169502479318575788307427)
          ·
            refine ⟨1754253718977863682461141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1169502479318575788307427 1754253718977863682461141)
            ·
              refine ⟨41115321538543680057683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1754253718977863682461141 41115321538543680057683)
              ·
                rfl

theorem cell20_810727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 7].length) (baseStart_810727 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_810727 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_810727 prefixEnd_810727 := by exact prefixLift 810727
  have htrace : WordTrace (prefixWord ++ tailWord_810727) baseStart_810727 baseEnd_810727 := by
    simpa [prefixWord, tailWord_810727, baseEnd_810727] using wordTrace_append hprefix tailTrace_810727
  have hstable : (prefixWord ++ tailWord_810727).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810727).length < 2 ^ (prefixWord ++ tailWord_810727).sum := by decide
  have hdescent : baseEnd_810727 < baseStart_810727 := by decide
  rcases family_descends (prefixWord ++ tailWord_810727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810755 : List Nat := [1, 1, 1, 3, 2, 2, 2, 5, 3]
def baseStart_810755 : Nat := 118140960795 + 810755 * 2 ^ 59
def prefixEnd_810755 : Nat := 4983230072969 + 3 ^ 40 * 810755 * 2
def baseEnd_810755 : Nat := 370050673809849467585699

theorem tailTrace_810755 : CollatzResearch.WordTrace tailWord_810755 prefixEnd_810755 370050673809849467585699 := by
  unfold tailWord_810755
  simp only [CollatzResearch.WordTrace]
  refine ⟨29570664177780575775273719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19713776118520383850182479 29570664177780575775273719)
  ·
    refine ⟨44355996266670863662910579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29570664177780575775273719 44355996266670863662910579)
    ·
      refine ⟨66533994400006295494365869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44355996266670863662910579 66533994400006295494365869)
      ·
        refine ⟨24950247900002360810387201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66533994400006295494365869 24950247900002360810387201)
        ·
          refine ⟨18712685925001770607790401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24950247900002360810387201 18712685925001770607790401)
          ·
            refine ⟨14034514443751327955842801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18712685925001770607790401 14034514443751327955842801)
            ·
              refine ⟨10525885832813495966882101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14034514443751327955842801 10525885832813495966882101)
              ·
                refine ⟨986801796826265246895197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10525885832813495966882101 986801796826265246895197)
                ·
                  refine ⟨370050673809849467585699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 986801796826265246895197 370050673809849467585699)
                  ·
                    rfl

theorem cell20_810755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 5, 3].length) (baseStart_810755 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_810755 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_810755 prefixEnd_810755 := by exact prefixLift 810755
  have htrace : WordTrace (prefixWord ++ tailWord_810755) baseStart_810755 baseEnd_810755 := by
    simpa [prefixWord, tailWord_810755, baseEnd_810755] using wordTrace_append hprefix tailTrace_810755
  have hstable : (prefixWord ++ tailWord_810755).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810755).length < 2 ^ (prefixWord ++ tailWord_810755).sum := by decide
  have hdescent : baseEnd_810755 < baseStart_810755 := by decide
  rcases family_descends (prefixWord ++ tailWord_810755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810775 : List Nat := [1, 1, 3, 4, 2, 3, 1, 3, 2]
def baseStart_810775 : Nat := 118140960795 + 810775 * 2 ^ 59
def prefixEnd_810775 : Nat := 4983230072969 + 3 ^ 40 * 810775 * 2
def baseEnd_810775 : Nat := 370059802354818286918951

theorem tailTrace_810775 : CollatzResearch.WordTrace tailWord_810775 prefixEnd_810775 370059802354818286918951 := by
  unfold tailWord_810775
  simp only [CollatzResearch.WordTrace]
  refine ⟨29571393637708119191001779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19714262425138746127334519 29571393637708119191001779)
  ·
    refine ⟨44357090456562178786502669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29571393637708119191001779 44357090456562178786502669)
    ·
      refine ⟨16633908921210817044938501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44357090456562178786502669 16633908921210817044938501)
      ·
        refine ⟨3118857922727028195925969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16633908921210817044938501 3118857922727028195925969)
        ·
          refine ⟨2339143442045271146944477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3118857922727028195925969 2339143442045271146944477)
          ·
            refine ⟨877178790766976680104179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2339143442045271146944477 877178790766976680104179)
            ·
              refine ⟨1315768186150465020156269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 877178790766976680104179 1315768186150465020156269)
              ·
                refine ⟨493413069806424382558601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1315768186150465020156269 493413069806424382558601)
                ·
                  refine ⟨370059802354818286918951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 493413069806424382558601 370059802354818286918951)
                  ·
                    rfl

theorem cell20_810775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 3, 2].length) (baseStart_810775 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_810775 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_810775 prefixEnd_810775 := by exact prefixLift 810775
  have htrace : WordTrace (prefixWord ++ tailWord_810775) baseStart_810775 baseEnd_810775 := by
    simpa [prefixWord, tailWord_810775, baseEnd_810775] using wordTrace_append hprefix tailTrace_810775
  have hstable : (prefixWord ++ tailWord_810775).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810775).length < 2 ^ (prefixWord ++ tailWord_810775).sum := by decide
  have hdescent : baseEnd_810775 < baseStart_810775 := by decide
  rcases family_descends (prefixWord ++ tailWord_810775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810806 : List Nat := [5, 1, 2, 2, 1, 1, 4, 1, 3]
def baseStart_810806 : Nat := 118140960795 + 810806 * 2 ^ 59
def prefixEnd_810806 : Nat := 4983230072969 + 3 ^ 40 * 810806 * 2
def baseEnd_810806 : Nat := 370073951599519956885491

theorem tailTrace_810806 : CollatzResearch.WordTrace tailWord_810806 prefixEnd_810806 370073951599519956885491 := by
  unfold tailWord_810806
  simp only [CollatzResearch.WordTrace]
  refine ⟨1848282768787238217836267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19715016200397207656920181 1848282768787238217836267)
  ·
    refine ⟨2772424153180857326754401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1848282768787238217836267 2772424153180857326754401)
    ·
      refine ⟨2079318114885642995065801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2772424153180857326754401 2079318114885642995065801)
      ·
        refine ⟨1559488586164232246299351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2079318114885642995065801 1559488586164232246299351)
        ·
          refine ⟨2339232879246348369449027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1559488586164232246299351 2339232879246348369449027)
          ·
            refine ⟨3508849318869522554173541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2339232879246348369449027 3508849318869522554173541)
            ·
              refine ⟨657909247288035478907539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3508849318869522554173541 657909247288035478907539)
              ·
                refine ⟨986863870932053218361309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 657909247288035478907539 986863870932053218361309)
                ·
                  refine ⟨370073951599519956885491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 986863870932053218361309 370073951599519956885491)
                  ·
                    rfl

theorem cell20_810806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 4, 1, 3].length) (baseStart_810806 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_810806 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_810806 prefixEnd_810806 := by exact prefixLift 810806
  have htrace : WordTrace (prefixWord ++ tailWord_810806) baseStart_810806 baseEnd_810806 := by
    simpa [prefixWord, tailWord_810806, baseEnd_810806] using wordTrace_append hprefix tailTrace_810806
  have hstable : (prefixWord ++ tailWord_810806).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810806).length < 2 ^ (prefixWord ++ tailWord_810806).sum := by decide
  have hdescent : baseEnd_810806 < baseStart_810806 := by decide
  rcases family_descends (prefixWord ++ tailWord_810806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810810 : List Nat := [3, 1, 1, 1, 5, 2, 1, 3, 3]
def baseStart_810810 : Nat := 118140960795 + 810810 * 2 ^ 59
def prefixEnd_810810 : Nat := 4983230072969 + 3 ^ 40 * 810810 * 2
def baseEnd_810810 : Nat := 370075777308513720752141

theorem tailTrace_810810 : CollatzResearch.WordTrace tailWord_810810 prefixEnd_810810 370075777308513720752141 := by
  unfold tailWord_810810
  simp only [CollatzResearch.WordTrace]
  refine ⟨7393167548145330042131471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19715113461720880112350589 7393167548145330042131471)
  ·
    refine ⟨11089751322217995063197207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7393167548145330042131471 11089751322217995063197207)
    ·
      refine ⟨16634626983326992594795811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11089751322217995063197207 16634626983326992594795811)
      ·
        refine ⟨24951940474990488892193717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16634626983326992594795811 24951940474990488892193717)
        ·
          refine ⟨2339244419530358333643161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24951940474990488892193717 2339244419530358333643161)
          ·
            refine ⟨1754433314647768750232371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2339244419530358333643161 1754433314647768750232371)
            ·
              refine ⟨2631649971971653125348557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1754433314647768750232371 2631649971971653125348557)
              ·
                refine ⟨986868739489369922005709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2631649971971653125348557 986868739489369922005709)
                ·
                  refine ⟨370075777308513720752141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 986868739489369922005709 370075777308513720752141)
                  ·
                    rfl

theorem cell20_810810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 3, 3].length) (baseStart_810810 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_810810 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_810810 prefixEnd_810810 := by exact prefixLift 810810
  have htrace : WordTrace (prefixWord ++ tailWord_810810) baseStart_810810 baseEnd_810810 := by
    simpa [prefixWord, tailWord_810810, baseEnd_810810] using wordTrace_append hprefix tailTrace_810810
  have hstable : (prefixWord ++ tailWord_810810).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810810).length < 2 ^ (prefixWord ++ tailWord_810810).sum := by decide
  have hdescent : baseEnd_810810 < baseStart_810810 := by decide
  rcases family_descends (prefixWord ++ tailWord_810810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810848 : List Nat := [2, 1, 1, 3, 3, 3, 2, 2, 3]
def baseStart_810848 : Nat := 118140960795 + 810848 * 2 ^ 59
def prefixEnd_810848 : Nat := 4983230072969 + 3 ^ 40 * 810848 * 2
def baseEnd_810848 : Nat := 370093121543954477485319

theorem tailTrace_810848 : CollatzResearch.WordTrace tailWord_810848 prefixEnd_810848 370093121543954477485319 := by
  unfold tailWord_810848
  simp only [CollatzResearch.WordTrace]
  refine ⟨14787028083221826329204599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19716037444295768438939465 14787028083221826329204599)
  ·
    refine ⟨22180542124832739493806899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14787028083221826329204599 22180542124832739493806899)
    ·
      refine ⟨33270813187249109240710349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22180542124832739493806899 33270813187249109240710349)
      ·
        refine ⟨12476554945218415965266381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33270813187249109240710349 12476554945218415965266381)
        ·
          refine ⟨4678708104456905986974893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12476554945218415965266381 4678708104456905986974893)
          ·
            refine ⟨1754515539171339745115585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4678708104456905986974893 1754515539171339745115585)
            ·
              refine ⟨1315886654378504808836689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1754515539171339745115585 1315886654378504808836689)
              ·
                refine ⟨986914990783878606627517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1315886654378504808836689 986914990783878606627517)
                ·
                  refine ⟨370093121543954477485319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 986914990783878606627517 370093121543954477485319)
                  ·
                    rfl

theorem cell20_810848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 2, 3].length) (baseStart_810848 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_810848 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_810848 prefixEnd_810848 := by exact prefixLift 810848
  have htrace : WordTrace (prefixWord ++ tailWord_810848) baseStart_810848 baseEnd_810848 := by
    simpa [prefixWord, tailWord_810848, baseEnd_810848] using wordTrace_append hprefix tailTrace_810848
  have hstable : (prefixWord ++ tailWord_810848).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810848).length < 2 ^ (prefixWord ++ tailWord_810848).sum := by decide
  have hdescent : baseEnd_810848 < baseStart_810848 := by decide
  rcases family_descends (prefixWord ++ tailWord_810848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810858 : List Nat := [3, 1, 3, 4, 1, 2, 1, 5]
def baseStart_810858 : Nat := 118140960795 + 810858 * 2 ^ 59
def prefixEnd_810858 : Nat := 4983230072969 + 3 ^ 40 * 810858 * 2
def baseEnd_810858 : Nat := 123365895272146295717315

theorem tailTrace_810858 : CollatzResearch.WordTrace tailWord_810858 prefixEnd_810858 123365895272146295717315 := by
  unfold tailWord_810858
  simp only [CollatzResearch.WordTrace]
  refine ⟨7393605224101856091568307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19716280597604949577515485 7393605224101856091568307)
  ·
    refine ⟨11090407836152784137352461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7393605224101856091568307 11090407836152784137352461)
    ·
      refine ⟨4158902938557294051507173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11090407836152784137352461 4158902938557294051507173)
      ·
        refine ⟨779794300979492634657595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4158902938557294051507173 779794300979492634657595)
        ·
          refine ⟨1169691451469238951986393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 779794300979492634657595 1169691451469238951986393)
          ·
            refine ⟨877268588601929213989795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1169691451469238951986393 877268588601929213989795)
            ·
              refine ⟨1315902882902893820984693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 877268588601929213989795 1315902882902893820984693)
              ·
                refine ⟨123365895272146295717315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1315902882902893820984693 123365895272146295717315)
                ·
                  rfl

theorem cell20_810858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 5].length) (baseStart_810858 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_810858 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_810858 prefixEnd_810858 := by exact prefixLift 810858
  have htrace : WordTrace (prefixWord ++ tailWord_810858) baseStart_810858 baseEnd_810858 := by
    simpa [prefixWord, tailWord_810858, baseEnd_810858] using wordTrace_append hprefix tailTrace_810858
  have hstable : (prefixWord ++ tailWord_810858).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810858).length < 2 ^ (prefixWord ++ tailWord_810858).sum := by decide
  have hdescent : baseEnd_810858 < baseStart_810858 := by decide
  rcases family_descends (prefixWord ++ tailWord_810858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810900 : List Nat := [2, 4, 2, 1, 1, 3, 7]
def baseStart_810900 : Nat := 118140960795 + 810900 * 2 ^ 59
def prefixEnd_810900 : Nat := 4983230072969 + 3 ^ 40 * 810900 * 2
def baseEnd_810900 : Nat := 41124095084541489750197

theorem tailTrace_810900 : CollatzResearch.WordTrace tailWord_810900 prefixEnd_810900 41124095084541489750197 := by
  unfold tailWord_810900
  simp only [CollatzResearch.WordTrace]
  refine ⟨14787976381127632769651077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19717301841503510359534769 14787976381127632769651077)
  ·
    refine ⟨2772745571461431144309577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14787976381127632769651077 2772745571461431144309577)
    ·
      refine ⟨2079559178596073358232183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2772745571461431144309577 2079559178596073358232183)
      ·
        refine ⟨3119338767894110037348275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2079559178596073358232183 3119338767894110037348275)
        ·
          refine ⟨4679008151841165056022413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3119338767894110037348275 4679008151841165056022413)
          ·
            refine ⟨1754628056940436896008405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4679008151841165056022413 1754628056940436896008405)
            ·
              refine ⟨41124095084541489750197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1754628056940436896008405 41124095084541489750197)
              ·
                rfl

theorem cell20_810900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 7].length) (baseStart_810900 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_810900 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_810900 prefixEnd_810900 := by exact prefixLift 810900
  have htrace : WordTrace (prefixWord ++ tailWord_810900) baseStart_810900 baseEnd_810900 := by
    simpa [prefixWord, tailWord_810900, baseEnd_810900] using wordTrace_append hprefix tailTrace_810900
  have hstable : (prefixWord ++ tailWord_810900).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810900).length < 2 ^ (prefixWord ++ tailWord_810900).sum := by decide
  have hdescent : baseEnd_810900 < baseStart_810900 := by decide
  rcases family_descends (prefixWord ++ tailWord_810900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810965 : List Nat := [1, 3, 2, 3, 2, 2, 3, 2, 2]
def baseStart_810965 : Nat := 118140960795 + 810965 * 2 ^ 59
def prefixEnd_810965 : Nat := 4983230072969 + 3 ^ 40 * 810965 * 2
def baseEnd_810965 : Nat := 370146523532022070584841

theorem tailTrace_810965 : CollatzResearch.WordTrace tailWord_810965 prefixEnd_810965 370146523532022070584841 := by
  unfold tailWord_810965
  simp only [CollatzResearch.WordTrace]
  refine ⟨29578323507019781640418349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19718882338013187760278899 29578323507019781640418349)
  ·
    refine ⟨11091871315132418115156881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29578323507019781640418349 11091871315132418115156881)
    ·
      refine ⟨8318903486349313586367661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11091871315132418115156881 8318903486349313586367661)
      ·
        refine ⟨3119588807380992594887873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8318903486349313586367661 3119588807380992594887873)
        ·
          refine ⟨2339691605535744446165905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3119588807380992594887873 2339691605535744446165905)
          ·
            refine ⟨1754768704151808334624429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2339691605535744446165905 1754768704151808334624429)
            ·
              refine ⟨658038264056928125484161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1754768704151808334624429 658038264056928125484161)
              ·
                refine ⟨493528698042696094113121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 658038264056928125484161 493528698042696094113121)
                ·
                  refine ⟨370146523532022070584841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 493528698042696094113121 370146523532022070584841)
                  ·
                    rfl

theorem cell20_810965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 3, 2, 2].length) (baseStart_810965 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_810965 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_810965 prefixEnd_810965 := by exact prefixLift 810965
  have htrace : WordTrace (prefixWord ++ tailWord_810965) baseStart_810965 baseEnd_810965 := by
    simpa [prefixWord, tailWord_810965, baseEnd_810965] using wordTrace_append hprefix tailTrace_810965
  have hstable : (prefixWord ++ tailWord_810965).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810965).length < 2 ^ (prefixWord ++ tailWord_810965).sum := by decide
  have hdescent : baseEnd_810965 < baseStart_810965 := by decide
  rcases family_descends (prefixWord ++ tailWord_810965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810979 : List Nat := [1, 1, 1, 6, 1, 4, 2, 1, 3]
def baseStart_810979 : Nat := 118140960795 + 810979 * 2 ^ 59
def prefixEnd_810979 : Nat := 4983230072969 + 3 ^ 40 * 810979 * 2
def baseEnd_810979 : Nat := 370152913513500244118117

theorem tailTrace_810979 : CollatzResearch.WordTrace tailWord_810979 prefixEnd_810979 370152913513500244118117 := by
  unfold tailWord_810979
  simp only [CollatzResearch.WordTrace]
  refine ⟨29578834128969062031427991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19719222752646041354285327 29578834128969062031427991)
  ·
    refine ⟨44368251193453593047141987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29578834128969062031427991 44368251193453593047141987)
    ·
      refine ⟨66552376790180389570712981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44368251193453593047141987 66552376790180389570712981)
      ·
        refine ⟨3119642662039705761127171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 66552376790180389570712981 3119642662039705761127171)
        ·
          refine ⟨4679463993059558641690757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3119642662039705761127171 4679463993059558641690757)
          ·
            refine ⟨877399498698667245317017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4679463993059558641690757 877399498698667245317017)
            ·
              refine ⟨658049624024000433987763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 877399498698667245317017 658049624024000433987763)
              ·
                refine ⟨987074436036000650981645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 658049624024000433987763 987074436036000650981645)
                ·
                  refine ⟨370152913513500244118117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 987074436036000650981645 370152913513500244118117)
                  ·
                    rfl

theorem cell20_810979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 2, 1, 3].length) (baseStart_810979 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_810979 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_810979 prefixEnd_810979 := by exact prefixLift 810979
  have htrace : WordTrace (prefixWord ++ tailWord_810979) baseStart_810979 baseEnd_810979 := by
    simpa [prefixWord, tailWord_810979, baseEnd_810979] using wordTrace_append hprefix tailTrace_810979
  have hstable : (prefixWord ++ tailWord_810979).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810979).length < 2 ^ (prefixWord ++ tailWord_810979).sum := by decide
  have hdescent : baseEnd_810979 < baseStart_810979 := by decide
  rcases family_descends (prefixWord ++ tailWord_810979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811031 : List Nat := [1, 1, 3, 5, 2, 2, 1, 5]
def baseStart_811031 : Nat := 118140960795 + 811031 * 2 ^ 59
def prefixEnd_811031 : Nat := 4983230072969 + 3 ^ 40 * 811031 * 2
def baseEnd_811031 : Nat := 123392215910139724794857

theorem tailTrace_811031 : CollatzResearch.WordTrace tailWord_811031 prefixEnd_811031 123392215910139724794857 := by
  unfold tailWord_811031
  simp only [CollatzResearch.WordTrace]
  refine ⟨29580730724780674912320947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19720487149853783274880631 29580730724780674912320947)
  ·
    refine ⟨44371096087171012368481421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29580730724780674912320947 44371096087171012368481421)
    ·
      refine ⟨16639161032689129638180533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44371096087171012368481421 16639161032689129638180533)
      ·
        refine ⟨1559921346814605903579425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16639161032689129638180533 1559921346814605903579425)
        ·
          refine ⟨1169941010110954427684569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1559921346814605903579425 1169941010110954427684569)
          ·
            refine ⟨877455757583215820763427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1169941010110954427684569 877455757583215820763427)
            ·
              refine ⟨1316183636374823731145141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 877455757583215820763427 1316183636374823731145141)
              ·
                refine ⟨123392215910139724794857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1316183636374823731145141 123392215910139724794857)
                ·
                  rfl

theorem cell20_811031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 5].length) (baseStart_811031 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_811031 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_811031 prefixEnd_811031 := by exact prefixLift 811031
  have htrace : WordTrace (prefixWord ++ tailWord_811031) baseStart_811031 baseEnd_811031 := by
    simpa [prefixWord, tailWord_811031, baseEnd_811031] using wordTrace_append hprefix tailTrace_811031
  have hstable : (prefixWord ++ tailWord_811031).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811031).length < 2 ^ (prefixWord ++ tailWord_811031).sum := by decide
  have hdescent : baseEnd_811031 < baseStart_811031 := by decide
  rcases family_descends (prefixWord ++ tailWord_811031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811048 : List Nat := [2, 1, 5, 3, 1, 1, 3, 4]
def baseStart_811048 : Nat := 118140960795 + 811048 * 2 ^ 59
def prefixEnd_811048 : Nat := 4983230072969 + 3 ^ 40 * 811048 * 2
def baseEnd_811048 : Nat := 123394802331214223605945

theorem tailTrace_811048 : CollatzResearch.WordTrace tailWord_811048 prefixEnd_811048 123394802331214223605945 := by
  unfold tailWord_811048
  simp only [CollatzResearch.WordTrace]
  refine ⟨14790675382859543407844899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19720900510479391210459865 14790675382859543407844899)
  ·
    refine ⟨22186013074289315111767349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14790675382859543407844899 22186013074289315111767349)
    ·
      refine ⟨2079938725714623291728189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22186013074289315111767349 2079938725714623291728189)
      ·
        refine ⟨779977022142983734398071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2079938725714623291728189 779977022142983734398071)
        ·
          refine ⟨1169965533214475601597107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 779977022142983734398071 1169965533214475601597107)
          ·
            refine ⟨1754948299821713402395661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1169965533214475601597107 1754948299821713402395661)
            ·
              refine ⟨658105612433142525898373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1754948299821713402395661 658105612433142525898373)
              ·
                refine ⟨123394802331214223605945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 658105612433142525898373 123394802331214223605945)
                ·
                  rfl

theorem cell20_811048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 3, 4].length) (baseStart_811048 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_811048 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_811048 prefixEnd_811048 := by exact prefixLift 811048
  have htrace : WordTrace (prefixWord ++ tailWord_811048) baseStart_811048 baseEnd_811048 := by
    simpa [prefixWord, tailWord_811048, baseEnd_811048] using wordTrace_append hprefix tailTrace_811048
  have hstable : (prefixWord ++ tailWord_811048).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811048).length < 2 ^ (prefixWord ++ tailWord_811048).sum := by decide
  have hdescent : baseEnd_811048 < baseStart_811048 := by decide
  rcases family_descends (prefixWord ++ tailWord_811048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811087 : List Nat := [1, 1, 2, 1, 1, 2, 2, 2, 8]
def baseStart_811087 : Nat := 118140960795 + 811087 * 2 ^ 59
def prefixEnd_811087 : Nat := 4983230072969 + 3 ^ 40 * 811087 * 2
def baseEnd_811087 : Nat := 370202207656331868517675

theorem tailTrace_811087 : CollatzResearch.WordTrace tailWord_811087 prefixEnd_811087 370202207656331868517675 := by
  unfold tailWord_811087
  simp only [CollatzResearch.WordTrace]
  refine ⟨29582773212577796476359515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19721848808385197650906343 29582773212577796476359515)
  ·
    refine ⟨44374159818866694714539273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29582773212577796476359515 44374159818866694714539273)
    ·
      refine ⟨33280619864150021035904455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44374159818866694714539273 33280619864150021035904455)
      ·
        refine ⟨49920929796225031553856683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33280619864150021035904455 49920929796225031553856683)
        ·
          refine ⟨74881394694337547330785025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49920929796225031553856683 74881394694337547330785025)
          ·
            refine ⟨56161046020753160498088769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74881394694337547330785025 56161046020753160498088769)
            ·
              refine ⟨42120784515564870373566577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56161046020753160498088769 42120784515564870373566577)
              ·
                refine ⟨31590588386673652780174933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42120784515564870373566577 31590588386673652780174933)
                ·
                  refine ⟨370202207656331868517675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31590588386673652780174933 370202207656331868517675)
                  ·
                    rfl

theorem cell20_811087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 8].length) (baseStart_811087 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_811087 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_811087 prefixEnd_811087 := by exact prefixLift 811087
  have htrace : WordTrace (prefixWord ++ tailWord_811087) baseStart_811087 baseEnd_811087 := by
    simpa [prefixWord, tailWord_811087, baseEnd_811087] using wordTrace_append hprefix tailTrace_811087
  have hstable : (prefixWord ++ tailWord_811087).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811087).length < 2 ^ (prefixWord ++ tailWord_811087).sum := by decide
  have hdescent : baseEnd_811087 < baseStart_811087 := by decide
  rcases family_descends (prefixWord ++ tailWord_811087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811104 : List Nat := [2, 1, 1, 3, 2, 3, 2, 2, 4]
def baseStart_811104 : Nat := 118140960795 + 811104 * 2 ^ 59
def prefixEnd_811104 : Nat := 4983230072969 + 3 ^ 40 * 811104 * 2
def baseEnd_811104 : Nat := 370209966919555364950939

theorem tailTrace_811104 : CollatzResearch.WordTrace tailWord_811104 prefixEnd_811104 370209966919555364950939 := by
  unfold tailWord_811104
  simp only [CollatzResearch.WordTrace]
  refine ⟨14791696626758104189864183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19722262169010805586485577 14791696626758104189864183)
  ·
    refine ⟨22187544940137156284796275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14791696626758104189864183 22187544940137156284796275)
    ·
      refine ⟨33281317410205734427194413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22187544940137156284796275 33281317410205734427194413)
      ·
        refine ⟨12480494028827150410197905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33281317410205734427194413 12480494028827150410197905)
        ·
          refine ⟨9360370521620362807648429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12480494028827150410197905 9360370521620362807648429)
          ·
            refine ⟨3510138945607636052868161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9360370521620362807648429 3510138945607636052868161)
            ·
              refine ⟨2632604209205727039651121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3510138945607636052868161 2632604209205727039651121)
              ·
                refine ⟨1974453156904295279738341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2632604209205727039651121 1974453156904295279738341)
                ·
                  refine ⟨370209966919555364950939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1974453156904295279738341 370209966919555364950939)
                  ·
                    rfl

theorem cell20_811104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 2, 4].length) (baseStart_811104 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_811104 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_811104 prefixEnd_811104 := by exact prefixLift 811104
  have htrace : WordTrace (prefixWord ++ tailWord_811104) baseStart_811104 baseEnd_811104 := by
    simpa [prefixWord, tailWord_811104, baseEnd_811104] using wordTrace_append hprefix tailTrace_811104
  have hstable : (prefixWord ++ tailWord_811104).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811104).length < 2 ^ (prefixWord ++ tailWord_811104).sum := by decide
  have hdescent : baseEnd_811104 < baseStart_811104 := by decide
  rcases family_descends (prefixWord ++ tailWord_811104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811111 : List Nat := [1, 1, 5, 1, 1, 2, 3, 6]
def baseStart_811111 : Nat := 118140960795 + 811111 * 2 ^ 59
def prefixEnd_811111 : Nat := 4983230072969 + 3 ^ 40 * 811111 * 2
def baseEnd_811111 : Nat := 123404387303431483905859

theorem tailTrace_811111 : CollatzResearch.WordTrace tailWord_811111 prefixEnd_811111 123404387303431483905859 := by
  unfold tailWord_811111
  simp only [CollatzResearch.WordTrace]
  refine ⟨29583648564490848575233187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19722432376327232383488791 29583648564490848575233187)
  ·
    refine ⟨44375472846736272862849781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29583648564490848575233187 44375472846736272862849781)
    ·
      refine ⟨4160200579381525580892167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44375472846736272862849781 4160200579381525580892167)
      ·
        refine ⟨6240300869072288371338251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4160200579381525580892167 6240300869072288371338251)
        ·
          refine ⟨9360451303608432557007377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6240300869072288371338251 9360451303608432557007377)
          ·
            refine ⟨7020338477706324417755533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9360451303608432557007377 7020338477706324417755533)
            ·
              refine ⟨2632626929139871656658325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7020338477706324417755533 2632626929139871656658325)
              ·
                refine ⟨123404387303431483905859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2632626929139871656658325 123404387303431483905859)
                ·
                  rfl

theorem cell20_811111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 6].length) (baseStart_811111 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_811111 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_811111 prefixEnd_811111 := by exact prefixLift 811111
  have htrace : WordTrace (prefixWord ++ tailWord_811111) baseStart_811111 baseEnd_811111 := by
    simpa [prefixWord, tailWord_811111, baseEnd_811111] using wordTrace_append hprefix tailTrace_811111
  have hstable : (prefixWord ++ tailWord_811111).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811111).length < 2 ^ (prefixWord ++ tailWord_811111).sum := by decide
  have hdescent : baseEnd_811111 < baseStart_811111 := by decide
  rcases family_descends (prefixWord ++ tailWord_811111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811189 : List Nat := [1, 3, 3, 4, 2, 1, 2, 2, 2]
def baseStart_811189 : Nat := 118140960795 + 811189 * 2 ^ 59
def prefixEnd_811189 : Nat := 4983230072969 + 3 ^ 40 * 811189 * 2
def baseEnd_811189 : Nat := 370248763235672847117259

theorem tailTrace_811189 : CollatzResearch.WordTrace tailWord_811189 prefixEnd_811189 370248763235672847117259 := by
  unfold tailWord_811189
  simp only [CollatzResearch.WordTrace]
  refine ⟨29586493458208267896572621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19724328972138845264381747 29586493458208267896572621)
  ·
    refine ⟨11094935046828100461214733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29586493458208267896572621 11094935046828100461214733)
    ·
      refine ⟨4160600642560537672955525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11094935046828100461214733 4160600642560537672955525)
      ·
        refine ⟨780112620480100813679161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4160600642560537672955525 780112620480100813679161)
        ·
          refine ⟨585084465360075610259371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 780112620480100813679161 585084465360075610259371)
          ·
            refine ⟨877626698040113415389057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 585084465360075610259371 877626698040113415389057)
            ·
              refine ⟨658220023530085061541793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 877626698040113415389057 658220023530085061541793)
              ·
                refine ⟨493665017647563796156345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 658220023530085061541793 493665017647563796156345)
                ·
                  refine ⟨370248763235672847117259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 493665017647563796156345 370248763235672847117259)
                  ·
                    rfl

theorem cell20_811189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 2, 2, 2].length) (baseStart_811189 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_811189 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_811189 prefixEnd_811189 := by exact prefixLift 811189
  have htrace : WordTrace (prefixWord ++ tailWord_811189) baseStart_811189 baseEnd_811189 := by
    simpa [prefixWord, tailWord_811189, baseEnd_811189] using wordTrace_append hprefix tailTrace_811189
  have hstable : (prefixWord ++ tailWord_811189).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811189).length < 2 ^ (prefixWord ++ tailWord_811189).sum := by decide
  have hdescent : baseEnd_811189 < baseStart_811189 := by decide
  rcases family_descends (prefixWord ++ tailWord_811189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811194 : List Nat := [3, 1, 1, 1, 2, 2, 2, 3, 5]
def baseStart_811194 : Nat := 118140960795 + 811194 * 2 ^ 59
def prefixEnd_811194 : Nat := 4983230072969 + 3 ^ 40 * 811194 * 2
def baseEnd_811194 : Nat := 370251045371915051950571

theorem tailTrace_811194 : CollatzResearch.WordTrace tailWord_811194 prefixEnd_811194 370251045371915051950571 := by
  unfold tailWord_811194
  simp only [CollatzResearch.WordTrace]
  refine ⟨7396668955797538437626159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19724450548793435833669757 7396668955797538437626159)
  ·
    refine ⟨11095003433696307656439239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7396668955797538437626159 11095003433696307656439239)
    ·
      refine ⟨16642505150544461484658859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11095003433696307656439239 16642505150544461484658859)
      ·
        refine ⟨24963757725816692226988289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16642505150544461484658859 24963757725816692226988289)
        ·
          refine ⟨18722818294362519170241217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24963757725816692226988289 18722818294362519170241217)
          ·
            refine ⟨14042113720771889377680913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18722818294362519170241217 14042113720771889377680913)
            ·
              refine ⟨10531585290578917033260685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14042113720771889377680913 10531585290578917033260685)
              ·
                refine ⟨3949344483967093887472757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10531585290578917033260685 3949344483967093887472757)
                ·
                  refine ⟨370251045371915051950571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3949344483967093887472757 370251045371915051950571)
                  ·
                    rfl

theorem cell20_811194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 3, 5].length) (baseStart_811194 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_811194 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_811194 prefixEnd_811194 := by exact prefixLift 811194
  have htrace : WordTrace (prefixWord ++ tailWord_811194) baseStart_811194 baseEnd_811194 := by
    simpa [prefixWord, tailWord_811194, baseEnd_811194] using wordTrace_append hprefix tailTrace_811194
  have hstable : (prefixWord ++ tailWord_811194).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811194).length < 2 ^ (prefixWord ++ tailWord_811194).sum := by decide
  have hdescent : baseEnd_811194 < baseStart_811194 := by decide
  rcases family_descends (prefixWord ++ tailWord_811194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811204 : List Nat := [2, 3, 3, 1, 2, 1, 3, 5]
def baseStart_811204 : Nat := 118140960795 + 811204 * 2 ^ 59
def prefixEnd_811204 : Nat := 4983230072969 + 3 ^ 40 * 811204 * 2
def baseEnd_811204 : Nat := 123418536548133153872399

theorem tailTrace_811204 : CollatzResearch.WordTrace tailWord_811204 prefixEnd_811204 123418536548133153872399 := by
  unfold tailWord_811204
  simp only [CollatzResearch.WordTrace]
  refine ⟨14793520276576962729184333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19724693702102616972245777 14793520276576962729184333)
  ·
    refine ⟨5547570103716361023444125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14793520276576962729184333 5547570103716361023444125)
    ·
      refine ⟨2080338788893635383791547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5547570103716361023444125 2080338788893635383791547)
      ·
        refine ⟨3120508183340453075687321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2080338788893635383791547 3120508183340453075687321)
        ·
          refine ⟨2340381137505339806765491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3120508183340453075687321 2340381137505339806765491)
          ·
            refine ⟨3510571706258009710148237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2340381137505339806765491 3510571706258009710148237)
            ·
              refine ⟨1316464389846753641305589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3510571706258009710148237 1316464389846753641305589)
              ·
                refine ⟨123418536548133153872399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1316464389846753641305589 123418536548133153872399)
                ·
                  rfl

theorem cell20_811204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 5].length) (baseStart_811204 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_811204 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_811204 prefixEnd_811204 := by exact prefixLift 811204
  have htrace : WordTrace (prefixWord ++ tailWord_811204) baseStart_811204 baseEnd_811204 := by
    simpa [prefixWord, tailWord_811204, baseEnd_811204] using wordTrace_append hprefix tailTrace_811204
  have hstable : (prefixWord ++ tailWord_811204).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811204).length < 2 ^ (prefixWord ++ tailWord_811204).sum := by decide
  have hdescent : baseEnd_811204 < baseStart_811204 := by decide
  rcases family_descends (prefixWord ++ tailWord_811204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811218 : List Nat := [3, 2, 2, 2, 1, 2, 1, 1, 6]
def baseStart_811218 : Nat := 118140960795 + 811218 * 2 ^ 59
def prefixEnd_811218 : Nat := 4983230072969 + 3 ^ 40 * 811218 * 2
def baseEnd_811218 : Nat := 370261999625877635150473

theorem tailTrace_811218 : CollatzResearch.WordTrace tailWord_811218 prefixEnd_811218 370261999625877635150473 := by
  unfold tailWord_811218
  simp only [CollatzResearch.WordTrace]
  refine ⟨7396887793775801462344577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19725034116735470566252205 7396887793775801462344577)
  ·
    refine ⟨5547665845331851096758433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7396887793775801462344577 5547665845331851096758433)
    ·
      refine ⟨4160749383998888322568825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5547665845331851096758433 4160749383998888322568825)
      ·
        refine ⟨3120562037999166241926619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4160749383998888322568825 3120562037999166241926619)
        ·
          refine ⟨4680843056998749362889929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3120562037999166241926619 4680843056998749362889929)
          ·
            refine ⟨3510632292749062022167447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4680843056998749362889929 3510632292749062022167447)
            ·
              refine ⟨5265948439123593033251171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3510632292749062022167447 5265948439123593033251171)
              ·
                refine ⟨7898922658685389549876757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5265948439123593033251171 7898922658685389549876757)
                ·
                  refine ⟨370261999625877635150473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7898922658685389549876757 370261999625877635150473)
                  ·
                    rfl

theorem cell20_811218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_811218 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_811218 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_811218 prefixEnd_811218 := by exact prefixLift 811218
  have htrace : WordTrace (prefixWord ++ tailWord_811218) baseStart_811218 baseEnd_811218 := by
    simpa [prefixWord, tailWord_811218, baseEnd_811218] using wordTrace_append hprefix tailTrace_811218
  have hstable : (prefixWord ++ tailWord_811218).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811218).length < 2 ^ (prefixWord ++ tailWord_811218).sum := by decide
  have hdescent : baseEnd_811218 < baseStart_811218 := by decide
  rcases family_descends (prefixWord ++ tailWord_811218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811221 : List Nat := [1, 3, 2, 4, 2, 1, 3, 4]
def baseStart_811221 : Nat := 118140960795 + 811221 * 2 ^ 59
def prefixEnd_811221 : Nat := 4983230072969 + 3 ^ 40 * 811221 * 2
def baseEnd_811221 : Nat := 123421122969207652683487

theorem tailTrace_811221 : CollatzResearch.WordTrace tailWord_811221 prefixEnd_811221 123421122969207652683487 := by
  unfold tailWord_811221
  simp only [CollatzResearch.WordTrace]
  refine ⟨29587660594092337361737517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19725107062728224907825011 29587660594092337361737517)
  ·
    refine ⟨11095372722784626510651569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29587660594092337361737517 11095372722784626510651569)
    ·
      refine ⟨8321529542088469882988677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11095372722784626510651569 8321529542088469882988677)
      ·
        refine ⟨1560286789141588103060377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8321529542088469882988677 1560286789141588103060377)
        ·
          refine ⟨1170215091856191077295283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1560286789141588103060377 1170215091856191077295283)
          ·
            refine ⟨1755322637784286615942925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1170215091856191077295283 1755322637784286615942925)
            ·
              refine ⟨658245989169107480978597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1755322637784286615942925 658245989169107480978597)
              ·
                refine ⟨123421122969207652683487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 658245989169107480978597 123421122969207652683487)
                ·
                  rfl

theorem cell20_811221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 3, 4].length) (baseStart_811221 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_811221 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_811221 prefixEnd_811221 := by exact prefixLift 811221
  have htrace : WordTrace (prefixWord ++ tailWord_811221) baseStart_811221 baseEnd_811221 := by
    simpa [prefixWord, tailWord_811221, baseEnd_811221] using wordTrace_append hprefix tailTrace_811221
  have hstable : (prefixWord ++ tailWord_811221).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811221).length < 2 ^ (prefixWord ++ tailWord_811221).sum := by decide
  have hdescent : baseEnd_811221 < baseStart_811221 := by decide
  rcases family_descends (prefixWord ++ tailWord_811221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811232 : List Nat := [2, 1, 1, 3, 1, 3, 2, 2, 5]
def baseStart_811232 : Nat := 118140960795 + 811232 * 2 ^ 59
def prefixEnd_811232 : Nat := 4983230072969 + 3 ^ 40 * 811232 * 2
def baseEnd_811232 : Nat := 370268389607355808683749

theorem tailTrace_811232 : CollatzResearch.WordTrace tailWord_811232 prefixEnd_811232 370268389607355808683749 := by
  unfold tailWord_811232
  simp only [CollatzResearch.WordTrace]
  refine ⟨14794030898526243120193975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19725374531368324160258633 14794030898526243120193975)
  ·
    refine ⟨22191046347789364680290963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14794030898526243120193975 22191046347789364680290963)
    ·
      refine ⟨33286569521684047020436445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22191046347789364680290963 33286569521684047020436445)
      ·
        refine ⟨12482463570631517632663667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33286569521684047020436445 12482463570631517632663667)
        ·
          refine ⟨18723695355947276448995501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12482463570631517632663667 18723695355947276448995501)
          ·
            refine ⟨7021385758480228668373313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18723695355947276448995501 7021385758480228668373313)
            ·
              refine ⟨5266039318860171501279985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7021385758480228668373313 5266039318860171501279985)
              ·
                refine ⟨3949529489145128625959989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5266039318860171501279985 3949529489145128625959989)
                ·
                  refine ⟨370268389607355808683749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3949529489145128625959989 370268389607355808683749)
                  ·
                    rfl

theorem cell20_811232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 2, 5].length) (baseStart_811232 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_811232 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_811232 prefixEnd_811232 := by exact prefixLift 811232
  have htrace : WordTrace (prefixWord ++ tailWord_811232) baseStart_811232 baseEnd_811232 := by
    simpa [prefixWord, tailWord_811232, baseEnd_811232] using wordTrace_append hprefix tailTrace_811232
  have hstable : (prefixWord ++ tailWord_811232).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811232).length < 2 ^ (prefixWord ++ tailWord_811232).sum := by decide
  have hdescent : baseEnd_811232 < baseStart_811232 := by decide
  rcases family_descends (prefixWord ++ tailWord_811232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811245 : List Nat := [1, 5, 1, 2, 3, 2, 1, 2, 3]
def baseStart_811245 : Nat := 118140960795 + 811245 * 2 ^ 59
def prefixEnd_811245 : Nat := 4983230072969 + 3 ^ 40 * 811245 * 2
def baseEnd_811245 : Nat := 370274323161585541250363

theorem tailTrace_811245 : CollatzResearch.WordTrace tailWord_811245 prefixEnd_811245 370274323161585541250363 := by
  unfold tailWord_811245
  simp only [CollatzResearch.WordTrace]
  refine ⟨29588535946005389460611189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19725690630670259640407459 29588535946005389460611189)
  ·
    refine ⟨2773925244938005261932299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29588535946005389460611189 2773925244938005261932299)
    ·
      refine ⟨4160887867407007892898449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2773925244938005261932299 4160887867407007892898449)
      ·
        refine ⟨3120665900555255919673837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4160887867407007892898449 3120665900555255919673837)
        ·
          refine ⟨1170249712708220969877689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3120665900555255919673837 1170249712708220969877689)
          ·
            refine ⟨877687284531165727408267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1170249712708220969877689 877687284531165727408267)
            ·
              refine ⟨1316530926796748591112401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 877687284531165727408267 1316530926796748591112401)
              ·
                refine ⟨987398195097561443334301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1316530926796748591112401 987398195097561443334301)
                ·
                  refine ⟨370274323161585541250363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 987398195097561443334301 370274323161585541250363)
                  ·
                    rfl

theorem cell20_811245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 2, 3].length) (baseStart_811245 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_811245 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_811245 prefixEnd_811245 := by exact prefixLift 811245
  have htrace : WordTrace (prefixWord ++ tailWord_811245) baseStart_811245 baseEnd_811245 := by
    simpa [prefixWord, tailWord_811245, baseEnd_811245] using wordTrace_append hprefix tailTrace_811245
  have hstable : (prefixWord ++ tailWord_811245).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811245).length < 2 ^ (prefixWord ++ tailWord_811245).sum := by decide
  have hdescent : baseEnd_811245 < baseStart_811245 := by decide
  rcases family_descends (prefixWord ++ tailWord_811245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811249 : List Nat := [1, 2, 2, 2, 2, 1, 5, 2, 3]
def baseStart_811249 : Nat := 118140960795 + 811249 * 2 ^ 59
def prefixEnd_811249 : Nat := 4983230072969 + 3 ^ 40 * 811249 * 2
def baseEnd_811249 : Nat := 370276148870579305117013

theorem tailTrace_811249 : CollatzResearch.WordTrace tailWord_811249 prefixEnd_811249 370276148870579305117013 := by
  unfold tailWord_811249
  simp only [CollatzResearch.WordTrace]
  refine ⟨29588681837990898143756801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19725787891993932095837867 29588681837990898143756801)
  ·
    refine ⟨22191511378493173607817601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29588681837990898143756801 22191511378493173607817601)
    ·
      refine ⟨16643633533869880205863201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22191511378493173607817601 16643633533869880205863201)
      ·
        refine ⟨12482725150402410154397401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16643633533869880205863201 12482725150402410154397401)
        ·
          refine ⟨9362043862801807615798051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12482725150402410154397401 9362043862801807615798051)
          ·
            refine ⟨14043065794202711423697077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9362043862801807615798051 14043065794202711423697077)
            ·
              refine ⟨1316537418206504195971601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14043065794202711423697077 1316537418206504195971601)
              ·
                refine ⟨987403063654878146978701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1316537418206504195971601 987403063654878146978701)
                ·
                  refine ⟨370276148870579305117013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 987403063654878146978701 370276148870579305117013)
                  ·
                    rfl

theorem cell20_811249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 2, 3].length) (baseStart_811249 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_811249 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_811249 prefixEnd_811249 := by exact prefixLift 811249
  have htrace : WordTrace (prefixWord ++ tailWord_811249) baseStart_811249 baseEnd_811249 := by
    simpa [prefixWord, tailWord_811249, baseEnd_811249] using wordTrace_append hprefix tailTrace_811249
  have hstable : (prefixWord ++ tailWord_811249).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811249).length < 2 ^ (prefixWord ++ tailWord_811249).sum := by decide
  have hdescent : baseEnd_811249 < baseStart_811249 := by decide
  rcases family_descends (prefixWord ++ tailWord_811249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811303 : List Nat := [1, 1, 8, 1, 1, 1, 3, 2, 2]
def baseStart_811303 : Nat := 118140960795 + 811303 * 2 ^ 59
def prefixEnd_811303 : Nat := 4983230072969 + 3 ^ 40 * 811303 * 2
def baseEnd_811303 : Nat := 370300795941995117316793

theorem tailTrace_811303 : CollatzResearch.WordTrace tailWord_811303 prefixEnd_811303 370300795941995117316793 := by
  unfold tailWord_811303
  simp only [CollatzResearch.WordTrace]
  refine ⟨29590651379795265366222563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19727100919863510244148375 29590651379795265366222563)
  ·
    refine ⟨44385977069692898049333845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29590651379795265366222563 44385977069692898049333845)
    ·
      refine ⟨520148168785463649015631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 44385977069692898049333845 520148168785463649015631)
      ·
        refine ⟨780222253178195473523447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 520148168785463649015631 780222253178195473523447)
        ·
          refine ⟨1170333379767293210285171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 780222253178195473523447 1170333379767293210285171)
          ·
            refine ⟨1755500069650939815427757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1170333379767293210285171 1755500069650939815427757)
            ·
              refine ⟨658312526119102430785409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1755500069650939815427757 658312526119102430785409)
              ·
                refine ⟨493734394589326823089057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 658312526119102430785409 493734394589326823089057)
                ·
                  refine ⟨370300795941995117316793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 493734394589326823089057 370300795941995117316793)
                  ·
                    rfl

theorem cell20_811303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 3, 2, 2].length) (baseStart_811303 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_811303 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_811303 prefixEnd_811303 := by exact prefixLift 811303
  have htrace : WordTrace (prefixWord ++ tailWord_811303) baseStart_811303 baseEnd_811303 := by
    simpa [prefixWord, tailWord_811303, baseEnd_811303] using wordTrace_append hprefix tailTrace_811303
  have hstable : (prefixWord ++ tailWord_811303).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811303).length < 2 ^ (prefixWord ++ tailWord_811303).sum := by decide
  have hdescent : baseEnd_811303 < baseStart_811303 := by decide
  rcases family_descends (prefixWord ++ tailWord_811303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811308 : List Nat := [2, 2, 1, 1, 1, 3, 4, 1, 5]
def baseStart_811308 : Nat := 118140960795 + 811308 * 2 ^ 59
def prefixEnd_811308 : Nat := 4983230072969 + 3 ^ 40 * 811308 * 2
def baseEnd_811308 : Nat := 370303078078237322150105

theorem tailTrace_811308 : CollatzResearch.WordTrace tailWord_811308 prefixEnd_811308 370303078078237322150105 := by
  unfold tailWord_811308
  simp only [CollatzResearch.WordTrace]
  refine ⟨14795416872388575610077289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19727222496518100813436385 14795416872388575610077289)
  ·
    refine ⟨11096562654291431707557967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14795416872388575610077289 11096562654291431707557967)
    ·
      refine ⟨16644843981437147561336951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11096562654291431707557967 16644843981437147561336951)
      ·
        refine ⟨24967265972155721342005427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16644843981437147561336951 24967265972155721342005427)
        ·
          refine ⟨37450898958233582013008141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24967265972155721342005427 37450898958233582013008141)
          ·
            refine ⟨14044087109337593254878053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37450898958233582013008141 14044087109337593254878053)
            ·
              refine ⟨2633266333000798735289635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14044087109337593254878053 2633266333000798735289635)
              ·
                refine ⟨3949899499501198102934453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2633266333000798735289635 3949899499501198102934453)
                ·
                  refine ⟨370303078078237322150105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3949899499501198102934453 370303078078237322150105)
                  ·
                    rfl

theorem cell20_811308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 5].length) (baseStart_811308 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_811308 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_811308 prefixEnd_811308 := by exact prefixLift 811308
  have htrace : WordTrace (prefixWord ++ tailWord_811308) baseStart_811308 baseEnd_811308 := by
    simpa [prefixWord, tailWord_811308, baseEnd_811308] using wordTrace_append hprefix tailTrace_811308
  have hstable : (prefixWord ++ tailWord_811308).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811308).length < 2 ^ (prefixWord ++ tailWord_811308).sum := by decide
  have hdescent : baseEnd_811308 < baseStart_811308 := by decide
  rcases family_descends (prefixWord ++ tailWord_811308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811321 : List Nat := [1, 2, 1, 6, 1, 3, 2, 1, 3]
def baseStart_811321 : Nat := 118140960795 + 811321 * 2 ^ 59
def prefixEnd_811321 : Nat := 4983230072969 + 3 ^ 40 * 811321 * 2
def baseEnd_811321 : Nat := 370309011632467054716719

theorem tailTrace_811321 : CollatzResearch.WordTrace tailWord_811321 prefixEnd_811321 370309011632467054716719 := by
  unfold tailWord_811321
  simp only [CollatzResearch.WordTrace]
  refine ⟨29591307893730054440377817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19727538595820036293585211 29591307893730054440377817)
  ·
    refine ⟨22193480920297540830283363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29591307893730054440377817 22193480920297540830283363)
    ·
      refine ⟨33290221380446311245425045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22193480920297540830283363 33290221380446311245425045)
      ·
        refine ⟨1560479127208420839629299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 33290221380446311245425045 1560479127208420839629299)
        ·
          refine ⟨2340718690812631259443949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1560479127208420839629299 2340718690812631259443949)
          ·
            refine ⟨877769509054736722291481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2340718690812631259443949 877769509054736722291481)
            ·
              refine ⟨658327131791052541718611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 877769509054736722291481 658327131791052541718611)
              ·
                refine ⟨987490697686578812577917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 658327131791052541718611 987490697686578812577917)
                ·
                  refine ⟨370309011632467054716719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 987490697686578812577917 370309011632467054716719)
                  ·
                    rfl

theorem cell20_811321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 2, 1, 3].length) (baseStart_811321 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_811321 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_811321 prefixEnd_811321 := by exact prefixLift 811321
  have htrace : WordTrace (prefixWord ++ tailWord_811321) baseStart_811321 baseEnd_811321 := by
    simpa [prefixWord, tailWord_811321, baseEnd_811321] using wordTrace_append hprefix tailTrace_811321
  have hstable : (prefixWord ++ tailWord_811321).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811321).length < 2 ^ (prefixWord ++ tailWord_811321).sum := by decide
  have hdescent : baseEnd_811321 < baseStart_811321 := by decide
  rcases family_descends (prefixWord ++ tailWord_811321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811346 : List Nat := [3, 2, 2, 1, 1, 1, 2, 1, 7]
def baseStart_811346 : Nat := 118140960795 + 811346 * 2 ^ 59
def prefixEnd_811346 : Nat := 4983230072969 + 3 ^ 40 * 811346 * 2
def baseEnd_811346 : Nat := 370320422313678078883283

theorem tailTrace_811346 : CollatzResearch.WordTrace tailWord_811346 prefixEnd_811346 370320422313678078883283 := by
  unfold tailWord_811346
  simp only [CollatzResearch.WordTrace]
  refine ⟨7398054929659870927509473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19728146479092989140025261 7398054929659870927509473)
  ·
    refine ⟨5548541197244903195632105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7398054929659870927509473 5548541197244903195632105)
    ·
      refine ⟨4161405897933677396724079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5548541197244903195632105 4161405897933677396724079)
      ·
        refine ⟨6242108846900516095086119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4161405897933677396724079 6242108846900516095086119)
        ·
          refine ⟨9363163270350774142629179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6242108846900516095086119 9363163270350774142629179)
          ·
            refine ⟨14044744905526161213943769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9363163270350774142629179 14044744905526161213943769)
            ·
              refine ⟨10533558679144620910457827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14044744905526161213943769 10533558679144620910457827)
              ·
                refine ⟨15800338018716931365686741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10533558679144620910457827 15800338018716931365686741)
                ·
                  refine ⟨370320422313678078883283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15800338018716931365686741 370320422313678078883283)
                  ·
                    rfl

theorem cell20_811346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_811346 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_811346 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_811346 prefixEnd_811346 := by exact prefixLift 811346
  have htrace : WordTrace (prefixWord ++ tailWord_811346) baseStart_811346 baseEnd_811346 := by
    simpa [prefixWord, tailWord_811346, baseEnd_811346] using wordTrace_append hprefix tailTrace_811346
  have hstable : (prefixWord ++ tailWord_811346).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811346).length < 2 ^ (prefixWord ++ tailWord_811346).sum := by decide
  have hdescent : baseEnd_811346 < baseStart_811346 := by decide
  rcases family_descends (prefixWord ++ tailWord_811346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811356 : List Nat := [2, 2, 4, 3, 1, 8]
def baseStart_811356 : Nat := 118140960795 + 811356 * 2 ^ 59
def prefixEnd_811356 : Nat := 4983230072969 + 3 ^ 40 * 811356 * 2
def baseEnd_811356 : Nat := 13715740243931944020367

theorem tailTrace_811356 : CollatzResearch.WordTrace tailWord_811356 prefixEnd_811356 13715740243931944020367 := by
  unfold tailWord_811356
  simp only [CollatzResearch.WordTrace]
  refine ⟨14796292224301627708950961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19728389632402170278601281 14796292224301627708950961)
  ·
    refine ⟨11097219168226220781713221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14796292224301627708950961 11097219168226220781713221)
    ·
      refine ⟨2080728594042416396571229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11097219168226220781713221 2080728594042416396571229)
      ·
        refine ⟨780273222765906148714211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2080728594042416396571229 780273222765906148714211)
        ·
          refine ⟨1170409834148859223071317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 780273222765906148714211 1170409834148859223071317)
          ·
            refine ⟨13715740243931944020367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1170409834148859223071317 13715740243931944020367)
            ·
              rfl

theorem cell20_811356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 8].length) (baseStart_811356 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_811356 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_811356 prefixEnd_811356 := by exact prefixLift 811356
  have htrace : WordTrace (prefixWord ++ tailWord_811356) baseStart_811356 baseEnd_811356 := by
    simpa [prefixWord, tailWord_811356, baseEnd_811356] using wordTrace_append hprefix tailTrace_811356
  have hstable : (prefixWord ++ tailWord_811356).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811356).length < 2 ^ (prefixWord ++ tailWord_811356).sum := by decide
  have hdescent : baseEnd_811356 < baseStart_811356 := by decide
  rcases family_descends (prefixWord ++ tailWord_811356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811360 : List Nat := [2, 1, 1, 3, 13]
def baseStart_811360 : Nat := 118140960795 + 811360 * 2 ^ 59
def prefixEnd_811360 : Nat := 4983230072969 + 3 ^ 40 * 811360 * 2
def baseEnd_811360 : Nat := 4571935954261188301439

theorem tailTrace_811360 : CollatzResearch.WordTrace tailWord_811360 prefixEnd_811360 4571935954261188301439 := by
  unfold tailWord_811360
  simp only [CollatzResearch.WordTrace]
  refine ⟨14796365170294382050523767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19728486893725842734031689 14796365170294382050523767)
  ·
    refine ⟨22194547755441573075785651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14796365170294382050523767 22194547755441573075785651)
    ·
      refine ⟨33291821633162359613678477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22194547755441573075785651 33291821633162359613678477)
      ·
        refine ⟨12484433112435884855129429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33291821633162359613678477 12484433112435884855129429)
        ·
          refine ⟨4571935954261188301439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 12484433112435884855129429 4571935954261188301439)
          ·
            rfl

theorem cell20_811360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 13].length) (baseStart_811360 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_811360 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_811360 prefixEnd_811360 := by exact prefixLift 811360
  have htrace : WordTrace (prefixWord ++ tailWord_811360) baseStart_811360 baseEnd_811360 := by
    simpa [prefixWord, tailWord_811360, baseEnd_811360] using wordTrace_append hprefix tailTrace_811360
  have hstable : (prefixWord ++ tailWord_811360).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811360).length < 2 ^ (prefixWord ++ tailWord_811360).sum := by decide
  have hdescent : baseEnd_811360 < baseStart_811360 := by decide
  rcases family_descends (prefixWord ++ tailWord_811360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811363 : List Nat := [1, 1, 1, 5, 2, 1, 4, 2, 3]
def baseStart_811363 : Nat := 118140960795 + 811363 * 2 ^ 59
def prefixEnd_811363 : Nat := 4983230072969 + 3 ^ 40 * 811363 * 2
def baseEnd_811363 : Nat := 370328181576901575316547

theorem tailTrace_811363 : CollatzResearch.WordTrace tailWord_811363 prefixEnd_811363 370328181576901575316547 := by
  unfold tailWord_811363
  simp only [CollatzResearch.WordTrace]
  refine ⟨29592839759577895613406743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19728559839718597075604495 29592839759577895613406743)
  ·
    refine ⟨44389259639366843420110115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29592839759577895613406743 44389259639366843420110115)
    ·
      refine ⟨66583889459050265130165173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44389259639366843420110115 66583889459050265130165173)
      ·
        refine ⟨6242239636785962355952985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 66583889459050265130165173 6242239636785962355952985)
        ·
          refine ⟨4681679727589471766964739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6242239636785962355952985 4681679727589471766964739)
          ·
            refine ⟨7022519591384207650447109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4681679727589471766964739 7022519591384207650447109)
            ·
              refine ⟨1316722423384538934458833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7022519591384207650447109 1316722423384538934458833)
              ·
                refine ⟨987541817538404200844125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1316722423384538934458833 987541817538404200844125)
                ·
                  refine ⟨370328181576901575316547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 987541817538404200844125 370328181576901575316547)
                  ·
                    rfl

theorem cell20_811363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 2, 3].length) (baseStart_811363 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_811363 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_811363 prefixEnd_811363 := by exact prefixLift 811363
  have htrace : WordTrace (prefixWord ++ tailWord_811363) baseStart_811363 baseEnd_811363 := by
    simpa [prefixWord, tailWord_811363, baseEnd_811363] using wordTrace_append hprefix tailTrace_811363
  have hstable : (prefixWord ++ tailWord_811363).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811363).length < 2 ^ (prefixWord ++ tailWord_811363).sum := by decide
  have hdescent : baseEnd_811363 < baseStart_811363 := by decide
  rcases family_descends (prefixWord ++ tailWord_811363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811391 : List Nat := [1, 1, 2, 2, 1, 1, 2, 6, 4]
def baseStart_811391 : Nat := 118140960795 + 811391 * 2 ^ 59
def prefixEnd_811391 : Nat := 4983230072969 + 3 ^ 40 * 811391 * 2
def baseEnd_811391 : Nat := 370340961539857922383099

theorem tailTrace_811391 : CollatzResearch.WordTrace tailWord_811391 prefixEnd_811391 370340961539857922383099 := by
  unfold tailWord_811391
  simp only [CollatzResearch.WordTrace]
  refine ⟨29593861003476456395426027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19729240668984304263617351 29593861003476456395426027)
  ·
    refine ⟨44390791505214684593139041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29593861003476456395426027 44390791505214684593139041)
    ·
      refine ⟨33293093628911013444854281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44390791505214684593139041 33293093628911013444854281)
      ·
        refine ⟨24969820221683260083640711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33293093628911013444854281 24969820221683260083640711)
        ·
          refine ⟨37454730332524890125461067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24969820221683260083640711 37454730332524890125461067)
          ·
            refine ⟨56182095498787335188191601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37454730332524890125461067 56182095498787335188191601)
            ·
              refine ⟨42136571624090501391143701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56182095498787335188191601 42136571624090501391143701)
              ·
                refine ⟨1975151794879242252709861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 42136571624090501391143701 1975151794879242252709861)
                ·
                  refine ⟨370340961539857922383099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1975151794879242252709861 370340961539857922383099)
                  ·
                    rfl

theorem cell20_811391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 6, 4].length) (baseStart_811391 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_811391 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_811391 prefixEnd_811391 := by exact prefixLift 811391
  have htrace : WordTrace (prefixWord ++ tailWord_811391) baseStart_811391 baseEnd_811391 := by
    simpa [prefixWord, tailWord_811391, baseEnd_811391] using wordTrace_append hprefix tailTrace_811391
  have hstable : (prefixWord ++ tailWord_811391).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811391).length < 2 ^ (prefixWord ++ tailWord_811391).sum := by decide
  have hdescent : baseEnd_811391 < baseStart_811391 := by decide
  rcases family_descends (prefixWord ++ tailWord_811391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811414 : List Nat := [5, 3, 1, 2, 1, 1, 1, 1, 5]
def baseStart_811414 : Nat := 118140960795 + 811414 * 2 ^ 59
def prefixEnd_811414 : Nat := 4983230072969 + 3 ^ 40 * 811414 * 2
def baseEnd_811414 : Nat := 370351459366572064616339

theorem tailTrace_811414 : CollatzResearch.WordTrace tailWord_811414 prefixEnd_811414 370351459366572064616339 := by
  unfold tailWord_811414
  simp only [CollatzResearch.WordTrace]
  refine ⟨1849668742649570707719581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19729799921595420882342197 1849668742649570707719581)
  ·
    refine ⟨693625778493589015394843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1849668742649570707719581 693625778493589015394843)
    ·
      refine ⟨1040438667740383523092265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 693625778493589015394843 1040438667740383523092265)
      ·
        refine ⟨780329000805287642319199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1040438667740383523092265 780329000805287642319199)
        ·
          refine ⟨1170493501207931463478799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 780329000805287642319199 1170493501207931463478799)
          ·
            refine ⟨1755740251811897195218199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1170493501207931463478799 1755740251811897195218199)
            ·
              refine ⟨2633610377717845792827299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1755740251811897195218199 2633610377717845792827299)
              ·
                refine ⟨3950415566576768689240949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2633610377717845792827299 3950415566576768689240949)
                ·
                  refine ⟨370351459366572064616339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3950415566576768689240949 370351459366572064616339)
                  ·
                    rfl

theorem cell20_811414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_811414 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_811414 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_811414 prefixEnd_811414 := by exact prefixLift 811414
  have htrace : WordTrace (prefixWord ++ tailWord_811414) baseStart_811414 baseEnd_811414 := by
    simpa [prefixWord, tailWord_811414, baseEnd_811414] using wordTrace_append hprefix tailTrace_811414
  have hstable : (prefixWord ++ tailWord_811414).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811414).length < 2 ^ (prefixWord ++ tailWord_811414).sum := by decide
  have hdescent : baseEnd_811414 < baseStart_811414 := by decide
  rcases family_descends (prefixWord ++ tailWord_811414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811418 : List Nat := [3, 1, 1, 4, 1, 4, 1, 2, 3]
def baseStart_811418 : Nat := 118140960795 + 811418 * 2 ^ 59
def prefixEnd_811418 : Nat := 4983230072969 + 3 ^ 40 * 811418 * 2
def baseEnd_811418 : Nat := 370353285075565828482989

theorem tailTrace_811418 : CollatzResearch.WordTrace tailWord_811418 prefixEnd_811418 370353285075565828482989 := by
  unfold tailWord_811418
  simp only [CollatzResearch.WordTrace]
  refine ⟨7398711443594660001664727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19729897182919093337772605 7398711443594660001664727)
  ·
    refine ⟨11098067165391990002497091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7398711443594660001664727 11098067165391990002497091)
    ·
      refine ⟨16647100748087985003745637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11098067165391990002497091 16647100748087985003745637)
      ·
        refine ⟨3121331390266497188202307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16647100748087985003745637 3121331390266497188202307)
        ·
          refine ⟨4681997085399745782303461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3121331390266497188202307 4681997085399745782303461)
          ·
            refine ⟨877874453512452334181899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4681997085399745782303461 877874453512452334181899)
            ·
              refine ⟨1316811680268678501272849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 877874453512452334181899 1316811680268678501272849)
              ·
                refine ⟨987608760201508875954637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1316811680268678501272849 987608760201508875954637)
                ·
                  refine ⟨370353285075565828482989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 987608760201508875954637 370353285075565828482989)
                  ·
                    rfl

theorem cell20_811418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 2, 3].length) (baseStart_811418 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_811418 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_811418 prefixEnd_811418 := by exact prefixLift 811418
  have htrace : WordTrace (prefixWord ++ tailWord_811418) baseStart_811418 baseEnd_811418 := by
    simpa [prefixWord, tailWord_811418, baseEnd_811418] using wordTrace_append hprefix tailTrace_811418
  have hstable : (prefixWord ++ tailWord_811418).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811418).length < 2 ^ (prefixWord ++ tailWord_811418).sum := by decide
  have hdescent : baseEnd_811418 < baseStart_811418 := by decide
  rcases family_descends (prefixWord ++ tailWord_811418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811436 : List Nat := [2, 2, 1, 1, 1, 1, 3, 9]
def baseStart_811436 : Nat := 118140960795 + 811436 * 2 ^ 59
def prefixEnd_811436 : Nat := 4983230072969 + 3 ^ 40 * 811436 * 2
def baseEnd_811436 : Nat := 123453833588679255294305

theorem tailTrace_811436 : CollatzResearch.WordTrace tailWord_811436 prefixEnd_811436 123453833588679255294305 := by
  unfold tailWord_811436
  simp only [CollatzResearch.WordTrace]
  refine ⟨14797751144156714540407081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19730334858875619387209441 14797751144156714540407081)
  ·
    refine ⟨11098313358117535905305311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14797751144156714540407081 11098313358117535905305311)
    ·
      refine ⟨16647470037176303857957967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11098313358117535905305311 16647470037176303857957967)
      ·
        refine ⟨24971205055764455786936951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16647470037176303857957967 24971205055764455786936951)
        ·
          refine ⟨37456807583646683680405427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24971205055764455786936951 37456807583646683680405427)
          ·
            refine ⟨56185211375470025520608141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37456807583646683680405427 56185211375470025520608141)
            ·
              refine ⟨21069454265801259570228053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56185211375470025520608141 21069454265801259570228053)
              ·
                refine ⟨123453833588679255294305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21069454265801259570228053 123453833588679255294305)
                ·
                  rfl

theorem cell20_811436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 9].length) (baseStart_811436 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_811436 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_811436 prefixEnd_811436 := by exact prefixLift 811436
  have htrace : WordTrace (prefixWord ++ tailWord_811436) baseStart_811436 baseEnd_811436 := by
    simpa [prefixWord, tailWord_811436, baseEnd_811436] using wordTrace_append hprefix tailTrace_811436
  have hstable : (prefixWord ++ tailWord_811436).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811436).length < 2 ^ (prefixWord ++ tailWord_811436).sum := by decide
  have hdescent : baseEnd_811436 < baseStart_811436 := by decide
  rcases family_descends (prefixWord ++ tailWord_811436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811453 : List Nat := [1, 4, 1, 2, 2, 3, 1, 6]
def baseStart_811453 : Nat := 118140960795 + 811453 * 2 ^ 59
def prefixEnd_811453 : Nat := 4983230072969 + 3 ^ 40 * 811453 * 2
def baseEnd_811453 : Nat := 123456420009753754105393

theorem tailTrace_811453 : CollatzResearch.WordTrace tailWord_811453 prefixEnd_811453 123456420009753754105393 := by
  unfold tailWord_811453
  simp only [CollatzResearch.WordTrace]
  refine ⟨29596122329251840984183013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19730748219501227322788675 29596122329251840984183013)
  ·
    refine ⟨5549272936734720184534315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29596122329251840984183013 5549272936734720184534315)
    ·
      refine ⟨8323909405102080276801473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5549272936734720184534315 8323909405102080276801473)
      ·
        refine ⟨6242932053826560207601105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8323909405102080276801473 6242932053826560207601105)
        ·
          refine ⟨4682199040369920155700829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6242932053826560207601105 4682199040369920155700829)
          ·
            refine ⟨1755824640138720058387811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4682199040369920155700829 1755824640138720058387811)
            ·
              refine ⟨2633736960208080087581717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1755824640138720058387811 2633736960208080087581717)
              ·
                refine ⟨123456420009753754105393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2633736960208080087581717 123456420009753754105393)
                ·
                  rfl

theorem cell20_811453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 6].length) (baseStart_811453 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_811453 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_811453 prefixEnd_811453 := by exact prefixLift 811453
  have htrace : WordTrace (prefixWord ++ tailWord_811453) baseStart_811453 baseEnd_811453 := by
    simpa [prefixWord, tailWord_811453, baseEnd_811453] using wordTrace_append hprefix tailTrace_811453
  have hstable : (prefixWord ++ tailWord_811453).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811453).length < 2 ^ (prefixWord ++ tailWord_811453).sum := by decide
  have hdescent : baseEnd_811453 < baseStart_811453 := by decide
  rcases family_descends (prefixWord ++ tailWord_811453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811463 : List Nat := [1, 1, 4, 1, 1, 4, 3, 3, 2]
def baseStart_811463 : Nat := 118140960795 + 811463 * 2 ^ 59
def prefixEnd_811463 : Nat := 4983230072969 + 3 ^ 40 * 811463 * 2
def baseEnd_811463 : Nat := 370373824301745671982805

theorem tailTrace_811463 : CollatzResearch.WordTrace tailWord_811463 prefixEnd_811463 370373824301745671982805 := by
  unfold tailWord_811463
  simp only [CollatzResearch.WordTrace]
  refine ⟨29596487059215612692047043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19730991372810408461364695 29596487059215612692047043)
  ·
    refine ⟨44394730588823419038070565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29596487059215612692047043 44394730588823419038070565)
    ·
      refine ⟨8324011985404391069638231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44394730588823419038070565 8324011985404391069638231)
      ·
        refine ⟨12486017978106586604457347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8324011985404391069638231 12486017978106586604457347)
        ·
          refine ⟨18729026967159879906686021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12486017978106586604457347 18729026967159879906686021)
          ·
            refine ⟨3511692556342477482503629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18729026967159879906686021 3511692556342477482503629)
            ·
              refine ⟨1316884708628429055938861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3511692556342477482503629 1316884708628429055938861)
              ·
                refine ⟨493831765735660895977073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1316884708628429055938861 493831765735660895977073)
                ·
                  refine ⟨370373824301745671982805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 493831765735660895977073 370373824301745671982805)
                  ·
                    rfl

theorem cell20_811463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 3, 2].length) (baseStart_811463 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_811463 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_811463 prefixEnd_811463 := by exact prefixLift 811463
  have htrace : WordTrace (prefixWord ++ tailWord_811463) baseStart_811463 baseEnd_811463 := by
    simpa [prefixWord, tailWord_811463, baseEnd_811463] using wordTrace_append hprefix tailTrace_811463
  have hstable : (prefixWord ++ tailWord_811463).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811463).length < 2 ^ (prefixWord ++ tailWord_811463).sum := by decide
  have hdescent : baseEnd_811463 < baseStart_811463 := by decide
  rcases family_descends (prefixWord ++ tailWord_811463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811505 : List Nat := [1, 2, 2, 2, 3, 1, 2, 1, 6]
def baseStart_811505 : Nat := 118140960795 + 811505 * 2 ^ 59
def prefixEnd_811505 : Nat := 4983230072969 + 3 ^ 40 * 811505 * 2
def baseEnd_811505 : Nat := 370392994246180192582633

theorem tailTrace_811505 : CollatzResearch.WordTrace tailWord_811505 prefixEnd_811505 370392994246180192582633 := by
  unfold tailWord_811505
  simp only [CollatzResearch.WordTrace]
  refine ⟨29598018925063453865075969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19732012616708969243383979 29598018925063453865075969)
  ·
    refine ⟨22198514193797590398806977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29598018925063453865075969 22198514193797590398806977)
    ·
      refine ⟨16648885645348192799105233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22198514193797590398806977 16648885645348192799105233)
      ·
        refine ⟨12486664234011144599328925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16648885645348192799105233 12486664234011144599328925)
        ·
          refine ⟨4682499087754179224748347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12486664234011144599328925 4682499087754179224748347)
          ·
            refine ⟨7023748631631268837122521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4682499087754179224748347 7023748631631268837122521)
            ·
              refine ⟨5267811473723451627841891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7023748631631268837122521 5267811473723451627841891)
              ·
                refine ⟨7901717210585177441762837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5267811473723451627841891 7901717210585177441762837)
                ·
                  refine ⟨370392994246180192582633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7901717210585177441762837 370392994246180192582633)
                  ·
                    rfl

theorem cell20_811505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 6].length) (baseStart_811505 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_811505 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_811505 prefixEnd_811505 := by exact prefixLift 811505
  have htrace : WordTrace (prefixWord ++ tailWord_811505) baseStart_811505 baseEnd_811505 := by
    simpa [prefixWord, tailWord_811505, baseEnd_811505] using wordTrace_append hprefix tailTrace_811505
  have hstable : (prefixWord ++ tailWord_811505).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811505).length < 2 ^ (prefixWord ++ tailWord_811505).sum := by decide
  have hdescent : baseEnd_811505 < baseStart_811505 := by decide
  rcases family_descends (prefixWord ++ tailWord_811505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811512 : List Nat := [2, 1, 2, 1, 1, 4, 1, 8]
def baseStart_811512 : Nat := 118140960795 + 811512 * 2 ^ 59
def prefixEnd_811512 : Nat := 4983230072969 + 3 ^ 40 * 811512 * 2
def baseEnd_811512 : Nat := 123465396412306426449757

theorem tailTrace_811512 : CollatzResearch.WordTrace tailWord_811512 prefixEnd_811512 123465396412306426449757 := by
  unfold tailWord_811512
  simp only [CollatzResearch.WordTrace]
  refine ⟨14799137118019047030290395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19732182824025396040387193 14799137118019047030290395)
  ·
    refine ⟨22198705677028570545435593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14799137118019047030290395 22198705677028570545435593)
    ·
      refine ⟨16649029257771427909076695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22198705677028570545435593 16649029257771427909076695)
      ·
        refine ⟨24973543886657141863615043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16649029257771427909076695 24973543886657141863615043)
        ·
          refine ⟨37460315829985712795422565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24973543886657141863615043 37460315829985712795422565)
          ·
            refine ⟨7023809218122321149141731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37460315829985712795422565 7023809218122321149141731)
            ·
              refine ⟨10535713827183481723712597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7023809218122321149141731 10535713827183481723712597)
              ·
                refine ⟨123465396412306426449757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10535713827183481723712597 123465396412306426449757)
                ·
                  rfl

theorem cell20_811512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 8].length) (baseStart_811512 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_811512 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_811512 prefixEnd_811512 := by exact prefixLift 811512
  have htrace : WordTrace (prefixWord ++ tailWord_811512) baseStart_811512 baseEnd_811512 := by
    simpa [prefixWord, tailWord_811512, baseEnd_811512] using wordTrace_append hprefix tailTrace_811512
  have hstable : (prefixWord ++ tailWord_811512).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811512).length < 2 ^ (prefixWord ++ tailWord_811512).sum := by decide
  have hdescent : baseEnd_811512 < baseStart_811512 := by decide
  rcases family_descends (prefixWord ++ tailWord_811512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811560 : List Nat := [2, 1, 5, 2, 1, 1, 1, 1, 6]
def baseStart_811560 : Nat := 118140960795 + 811560 * 2 ^ 59
def prefixEnd_811560 : Nat := 4983230072969 + 3 ^ 40 * 811560 * 2
def baseEnd_811560 : Nat := 370418097744844445749075

theorem tailTrace_811560 : CollatzResearch.WordTrace tailWord_811560 prefixEnd_811560 370418097744844445749075 := by
  unfold tailWord_811560
  simp only [CollatzResearch.WordTrace]
  refine ⟨14800012469932099129164067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19733349959909465505552089 14800012469932099129164067)
  ·
    refine ⟨22200018704898148693746101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14800012469932099129164067 22200018704898148693746101)
    ·
      refine ⟨2081251753584201440038697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22200018704898148693746101 2081251753584201440038697)
      ·
        refine ⟨1560938815188151080029023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2081251753584201440038697 1560938815188151080029023)
        ·
          refine ⟨2341408222782226620043535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1560938815188151080029023 2341408222782226620043535)
          ·
            refine ⟨3512112334173339930065303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2341408222782226620043535 3512112334173339930065303)
            ·
              refine ⟨5268168501260009895097955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3512112334173339930065303 5268168501260009895097955)
              ·
                refine ⟨7902252751890014842646933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5268168501260009895097955 7902252751890014842646933)
                ·
                  refine ⟨370418097744844445749075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7902252751890014842646933 370418097744844445749075)
                  ·
                    rfl

theorem cell20_811560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 6].length) (baseStart_811560 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_811560 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_811560 prefixEnd_811560 := by exact prefixLift 811560
  have htrace : WordTrace (prefixWord ++ tailWord_811560) baseStart_811560 baseEnd_811560 := by
    simpa [prefixWord, tailWord_811560, baseEnd_811560] using wordTrace_append hprefix tailTrace_811560
  have hstable : (prefixWord ++ tailWord_811560).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811560).length < 2 ^ (prefixWord ++ tailWord_811560).sum := by decide
  have hdescent : baseEnd_811560 < baseStart_811560 := by decide
  rcases family_descends (prefixWord ++ tailWord_811560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811577 : List Nat := [1, 2, 1, 5, 1, 1, 4, 3, 2]
def baseStart_811577 : Nat := 118140960795 + 811577 * 2 ^ 59
def prefixEnd_811577 : Nat := 4983230072969 + 3 ^ 40 * 811577 * 2
def baseEnd_811577 : Nat := 370425857008067942182339

theorem tailTrace_811577 : CollatzResearch.WordTrace tailWord_811577 prefixEnd_811577 370425857008067942182339 := by
  unfold tailWord_811577
  simp only [CollatzResearch.WordTrace]
  refine ⟨29600644980802610161696985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19733763320535073441131323 29600644980802610161696985)
  ·
    refine ⟨22200483735601957621272739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29600644980802610161696985 22200483735601957621272739)
    ·
      refine ⟨33300725603402936431909109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22200483735601957621272739 33300725603402936431909109)
      ·
        refine ⟨3121943025319025290491479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33300725603402936431909109 3121943025319025290491479)
        ·
          refine ⟨4682914537978537935737219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3121943025319025290491479 4682914537978537935737219)
          ·
            refine ⟨7024371806967806903605829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4682914537978537935737219 7024371806967806903605829)
            ·
              refine ⟨1317069713806463794426093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7024371806967806903605829 1317069713806463794426093)
              ·
                refine ⟨493901142677423922909785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1317069713806463794426093 493901142677423922909785)
                ·
                  refine ⟨370425857008067942182339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 493901142677423922909785 370425857008067942182339)
                  ·
                    rfl

theorem cell20_811577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 3, 2].length) (baseStart_811577 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_811577 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_811577 prefixEnd_811577 := by exact prefixLift 811577
  have htrace : WordTrace (prefixWord ++ tailWord_811577) baseStart_811577 baseEnd_811577 := by
    simpa [prefixWord, tailWord_811577, baseEnd_811577] using wordTrace_append hprefix tailTrace_811577
  have hstable : (prefixWord ++ tailWord_811577).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811577).length < 2 ^ (prefixWord ++ tailWord_811577).sum := by decide
  have hdescent : baseEnd_811577 < baseStart_811577 := by decide
  rcases family_descends (prefixWord ++ tailWord_811577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811591 : List Nat := [1, 1, 4, 1, 4, 1, 3, 2, 3]
def baseStart_811591 : Nat := 118140960795 + 811591 * 2 ^ 59
def prefixEnd_811591 : Nat := 4983230072969 + 3 ^ 40 * 811591 * 2
def baseEnd_811591 : Nat := 370432246989546115715615

theorem tailTrace_811591 : CollatzResearch.WordTrace tailWord_811591 prefixEnd_811591 370432246989546115715615 := by
  unfold tailWord_811591
  simp only [CollatzResearch.WordTrace]
  refine ⟨29601155602751890552706627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19734103735167927035137751 29601155602751890552706627)
  ·
    refine ⟨44401733404127835829059941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29601155602751890552706627 44401733404127835829059941)
    ·
      refine ⟨8325325013273969217948739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44401733404127835829059941 8325325013273969217948739)
      ·
        refine ⟨12487987519910953826923109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8325325013273969217948739 12487987519910953826923109)
        ·
          refine ⟨2341497659983303842548083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12487987519910953826923109 2341497659983303842548083)
          ·
            refine ⟨3512246489974955763822125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2341497659983303842548083 3512246489974955763822125)
            ·
              refine ⟨1317092433740608411433297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3512246489974955763822125 1317092433740608411433297)
              ·
                refine ⟨987819325305456308574973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1317092433740608411433297 987819325305456308574973)
                ·
                  refine ⟨370432246989546115715615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 987819325305456308574973 370432246989546115715615)
                  ·
                    rfl

theorem cell20_811591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 2, 3].length) (baseStart_811591 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_811591 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_811591 prefixEnd_811591 := by exact prefixLift 811591
  have htrace : WordTrace (prefixWord ++ tailWord_811591) baseStart_811591 baseEnd_811591 := by
    simpa [prefixWord, tailWord_811591, baseEnd_811591] using wordTrace_append hprefix tailTrace_811591
  have hstable : (prefixWord ++ tailWord_811591).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811591).length < 2 ^ (prefixWord ++ tailWord_811591).sum := by decide
  have hdescent : baseEnd_811591 < baseStart_811591 := by decide
  rcases family_descends (prefixWord ++ tailWord_811591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811614 : List Nat := [4, 4, 1, 2, 2, 1, 2, 4]
def baseStart_811614 : Nat := 118140960795 + 811614 * 2 ^ 59
def prefixEnd_811614 : Nat := 4983230072969 + 3 ^ 40 * 811614 * 2
def baseEnd_811614 : Nat := 123480914938753419316285

theorem tailTrace_811614 : CollatzResearch.WordTrace tailWord_811614 prefixEnd_811614 123480914938753419316285 := by
  unfold tailWord_811614
  simp only [CollatzResearch.WordTrace]
  refine ⟨3700249310208570685099237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19734662987779043653862597 3700249310208570685099237)
  ·
    refine ⟨693796745664107003456107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3700249310208570685099237 693796745664107003456107)
    ·
      refine ⟨1040695118496160505184161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 693796745664107003456107 1040695118496160505184161)
      ·
        refine ⟨780521338872120378888121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1040695118496160505184161 780521338872120378888121)
        ·
          refine ⟨585391004154090284166091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 780521338872120378888121 585391004154090284166091)
          ·
            refine ⟨878086506231135426249137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 585391004154090284166091 878086506231135426249137)
            ·
              refine ⟨658564879673351569686853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 878086506231135426249137 658564879673351569686853)
              ·
                refine ⟨123480914938753419316285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 658564879673351569686853 123480914938753419316285)
                ·
                  rfl

theorem cell20_811614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 2, 4].length) (baseStart_811614 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_811614 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_811614 prefixEnd_811614 := by exact prefixLift 811614
  have htrace : WordTrace (prefixWord ++ tailWord_811614) baseStart_811614 baseEnd_811614 := by
    simpa [prefixWord, tailWord_811614, baseEnd_811614] using wordTrace_append hprefix tailTrace_811614
  have hstable : (prefixWord ++ tailWord_811614).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811614).length < 2 ^ (prefixWord ++ tailWord_811614).sum := by decide
  have hdescent : baseEnd_811614 < baseStart_811614 := by decide
  rcases family_descends (prefixWord ++ tailWord_811614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811618 : List Nat := [3, 3, 2, 3, 1, 2, 2, 4]
def baseStart_811618 : Nat := 118140960795 + 811618 * 2 ^ 59
def prefixEnd_811618 : Nat := 4983230072969 + 3 ^ 40 * 811618 * 2
def baseEnd_811618 : Nat := 123481523508418007271835

theorem tailTrace_811618 : CollatzResearch.WordTrace tailWord_811618 prefixEnd_811618 123481523508418007271835 := by
  unfold tailWord_811618
  simp only [CollatzResearch.WordTrace]
  refine ⟨7400535093413518540984877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19734760249102716109293005 7400535093413518540984877)
  ·
    refine ⟨2775200660030069452869329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7400535093413518540984877 2775200660030069452869329)
    ·
      refine ⟨2081400495022552089651997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2775200660030069452869329 2081400495022552089651997)
      ·
        refine ⟨780525185633457033619499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2081400495022552089651997 780525185633457033619499)
        ·
          refine ⟨1170787778450185550429249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 780525185633457033619499 1170787778450185550429249)
          ·
            refine ⟨878090833837639162821937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1170787778450185550429249 878090833837639162821937)
            ·
              refine ⟨658568125378229372116453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 878090833837639162821937 658568125378229372116453)
              ·
                refine ⟨123481523508418007271835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 658568125378229372116453 123481523508418007271835)
                ·
                  rfl

theorem cell20_811618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 2, 4].length) (baseStart_811618 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_811618 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_811618 prefixEnd_811618 := by exact prefixLift 811618
  have htrace : WordTrace (prefixWord ++ tailWord_811618) baseStart_811618 baseEnd_811618 := by
    simpa [prefixWord, tailWord_811618, baseEnd_811618] using wordTrace_append hprefix tailTrace_811618
  have hstable : (prefixWord ++ tailWord_811618).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811618).length < 2 ^ (prefixWord ++ tailWord_811618).sum := by decide
  have hdescent : baseEnd_811618 < baseStart_811618 := by decide
  rcases family_descends (prefixWord ++ tailWord_811618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811619 : List Nat := [1, 1, 1, 5, 1, 2, 1, 4, 4]
def baseStart_811619 : Nat := 118140960795 + 811619 * 2 ^ 59
def prefixEnd_811619 : Nat := 4983230072969 + 3 ^ 40 * 811619 * 2
def baseEnd_811619 : Nat := 370445026952502462782167

theorem tailTrace_811619 : CollatzResearch.WordTrace tailWord_811619 prefixEnd_811619 370445026952502462782167 := by
  unfold tailWord_811619
  simp only [CollatzResearch.WordTrace]
  refine ⟨29602176846650451334725911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19734784564433634223150607 29602176846650451334725911)
  ·
    refine ⟨44403265269975677002088867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29602176846650451334725911 44403265269975677002088867)
    ·
      refine ⟨66604897904963515503133301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44403265269975677002088867 66604897904963515503133301)
      ·
        refine ⟨6244209178590329578418747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 66604897904963515503133301 6244209178590329578418747)
        ·
          refine ⟨9366313767885494367628121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6244209178590329578418747 9366313767885494367628121)
          ·
            refine ⟨7024735325914120775721091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9366313767885494367628121 7024735325914120775721091)
            ·
              refine ⟨10537102988871181163581637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7024735325914120775721091 10537102988871181163581637)
              ·
                refine ⟨1975706810413346468171557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10537102988871181163581637 1975706810413346468171557)
                ·
                  refine ⟨370445026952502462782167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1975706810413346468171557 370445026952502462782167)
                  ·
                    rfl

theorem cell20_811619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 4, 4].length) (baseStart_811619 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_811619 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_811619 prefixEnd_811619 := by exact prefixLift 811619
  have htrace : WordTrace (prefixWord ++ tailWord_811619) baseStart_811619 baseEnd_811619 := by
    simpa [prefixWord, tailWord_811619, baseEnd_811619] using wordTrace_append hprefix tailTrace_811619
  have hstable : (prefixWord ++ tailWord_811619).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811619).length < 2 ^ (prefixWord ++ tailWord_811619).sum := by decide
  have hdescent : baseEnd_811619 < baseStart_811619 := by decide
  rcases family_descends (prefixWord ++ tailWord_811619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811632 : List Nat := [2, 1, 1, 1, 7, 2, 1, 3, 2]
def baseStart_811632 : Nat := 118140960795 + 811632 * 2 ^ 59
def prefixEnd_811632 : Nat := 4983230072969 + 3 ^ 40 * 811632 * 2
def baseEnd_811632 : Nat := 370450960506732195348781

theorem tailTrace_811632 : CollatzResearch.WordTrace tailWord_811632 prefixEnd_811632 370450960506732195348781 := by
  unfold tailWord_811632
  simp only [CollatzResearch.WordTrace]
  refine ⟨14801325497801677277474575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19735100663735569703299433 14801325497801677277474575)
  ·
    refine ⟨22201988246702515916211863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14801325497801677277474575 22201988246702515916211863)
    ·
      refine ⟨33302982370053773874317795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22201988246702515916211863 33302982370053773874317795)
      ·
        refine ⟨49954473555080660811476693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33302982370053773874317795 49954473555080660811476693)
        ·
          refine ⟨1170807973947202987768985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 49954473555080660811476693 1170807973947202987768985)
          ·
            refine ⟨878105980460402240826739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1170807973947202987768985 878105980460402240826739)
            ·
              refine ⟨1317158970690603361240109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 878105980460402240826739 1317158970690603361240109)
              ·
                refine ⟨493934614008976260465041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1317158970690603361240109 493934614008976260465041)
                ·
                  refine ⟨370450960506732195348781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 493934614008976260465041 370450960506732195348781)
                  ·
                    rfl

theorem cell20_811632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 3, 2].length) (baseStart_811632 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_811632 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_811632 prefixEnd_811632 := by exact prefixLift 811632
  have htrace : WordTrace (prefixWord ++ tailWord_811632) baseStart_811632 baseEnd_811632 := by
    simpa [prefixWord, tailWord_811632, baseEnd_811632] using wordTrace_append hprefix tailTrace_811632
  have hstable : (prefixWord ++ tailWord_811632).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811632).length < 2 ^ (prefixWord ++ tailWord_811632).sum := by decide
  have hdescent : baseEnd_811632 < baseStart_811632 := by decide
  rcases family_descends (prefixWord ++ tailWord_811632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811812 : List Nat := [2, 3, 1, 3, 4, 1, 6]
def baseStart_811812 : Nat := 118140960795 + 811812 * 2 ^ 59
def prefixEnd_811812 : Nat := 4983230072969 + 3 ^ 40 * 811812 * 2
def baseEnd_811812 : Nat := 41170346379050174372005

theorem tailTrace_811812 : CollatzResearch.WordTrace tailWord_811812 prefixEnd_811812 41170346379050174372005 := by
  unfold tailWord_811812
  simp only [CollatzResearch.WordTrace]
  refine ⟨14804608067475622648250845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19739477423300830197667793 14804608067475622648250845)
  ·
    refine ⟨5551728025303358493094067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14804608067475622648250845 5551728025303358493094067)
    ·
      refine ⟨8327592037955037739641101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5551728025303358493094067 8327592037955037739641101)
      ·
        refine ⟨3122847014233139152365413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8327592037955037739641101 3122847014233139152365413)
        ·
          refine ⟨585533815168713591068515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3122847014233139152365413 585533815168713591068515)
          ·
            refine ⟨878300722753070386602773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 585533815168713591068515 878300722753070386602773)
            ·
              refine ⟨41170346379050174372005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 878300722753070386602773 41170346379050174372005)
              ·
                rfl

theorem cell20_811812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 6].length) (baseStart_811812 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_811812 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_811812 prefixEnd_811812 := by exact prefixLift 811812
  have htrace : WordTrace (prefixWord ++ tailWord_811812) baseStart_811812 baseEnd_811812 := by
    simpa [prefixWord, tailWord_811812, baseEnd_811812] using wordTrace_append hprefix tailTrace_811812
  have hstable : (prefixWord ++ tailWord_811812).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811812).length < 2 ^ (prefixWord ++ tailWord_811812).sum := by decide
  have hdescent : baseEnd_811812 < baseStart_811812 := by decide
  rcases family_descends (prefixWord ++ tailWord_811812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811874 : List Nat := [3, 3, 2, 1, 3, 1, 2, 2, 3]
def baseStart_811874 : Nat := 118140960795 + 811874 * 2 ^ 59
def prefixEnd_811874 : Nat := 4983230072969 + 3 ^ 40 * 811874 * 2
def baseEnd_811874 : Nat := 370561415900854909281125

theorem tailTrace_811874 : CollatzResearch.WordTrace tailWord_811874 prefixEnd_811874 370561415900854909281125 := by
  unfold tailWord_811874
  simp only [CollatzResearch.WordTrace]
  refine ⟨7402869365181657471314669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19740984973817753256839117 7402869365181657471314669)
  ·
    refine ⟨2776076011943121551743001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7402869365181657471314669 2776076011943121551743001)
    ·
      refine ⟨2082057008957341163807251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2776076011943121551743001 2082057008957341163807251)
      ·
        refine ⟨3123085513436011745710877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2082057008957341163807251 3123085513436011745710877)
        ·
          refine ⟨1171157067538504404641579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3123085513436011745710877 1171157067538504404641579)
          ·
            refine ⟨1756735601307756606962369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1171157067538504404641579 1756735601307756606962369)
            ·
              refine ⟨1317551700980817455221777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1756735601307756606962369 1317551700980817455221777)
              ·
                refine ⟨988163775735613091416333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1317551700980817455221777 988163775735613091416333)
                ·
                  refine ⟨370561415900854909281125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 988163775735613091416333 370561415900854909281125)
                  ·
                    rfl

theorem cell20_811874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_811874 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_811874 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_811874 prefixEnd_811874 := by exact prefixLift 811874
  have htrace : WordTrace (prefixWord ++ tailWord_811874) baseStart_811874 baseEnd_811874 := by
    simpa [prefixWord, tailWord_811874, baseEnd_811874] using wordTrace_append hprefix tailTrace_811874
  have hstable : (prefixWord ++ tailWord_811874).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811874).length < 2 ^ (prefixWord ++ tailWord_811874).sum := by decide
  have hdescent : baseEnd_811874 < baseStart_811874 := by decide
  rcases family_descends (prefixWord ++ tailWord_811874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811885 : List Nat := [1, 5, 1, 1, 1, 1, 1, 5, 4]
def baseStart_811885 : Nat := 118140960795 + 811885 * 2 ^ 59
def prefixEnd_811885 : Nat := 4983230072969 + 3 ^ 40 * 811885 * 2
def baseEnd_811885 : Nat := 370566436600587759914413

theorem tailTrace_811885 : CollatzResearch.WordTrace tailWord_811885 prefixEnd_811885 370566436600587759914413 := by
  unfold tailWord_811885
  simp only [CollatzResearch.WordTrace]
  refine ⟨29611878663686778763909109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19741252442457852509272739 29611878663686778763909109)
  ·
    refine ⟨2776113624720635509116479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29611878663686778763909109 2776113624720635509116479)
    ·
      refine ⟨4164170437080953263674719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2776113624720635509116479 4164170437080953263674719)
      ·
        refine ⟨6246255655621429895512079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4164170437080953263674719 6246255655621429895512079)
        ·
          refine ⟨9369383483432144843268119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6246255655621429895512079 9369383483432144843268119)
          ·
            refine ⟨14054075225148217264902179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9369383483432144843268119 14054075225148217264902179)
            ·
              refine ⟨21081112837722325897353269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14054075225148217264902179 21081112837722325897353269)
              ·
                refine ⟨1976354328536468052876869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21081112837722325897353269 1976354328536468052876869)
                ·
                  refine ⟨370566436600587759914413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1976354328536468052876869 370566436600587759914413)
                  ·
                    rfl

theorem cell20_811885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_811885 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_811885 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_811885 prefixEnd_811885 := by exact prefixLift 811885
  have htrace : WordTrace (prefixWord ++ tailWord_811885) baseStart_811885 baseEnd_811885 := by
    simpa [prefixWord, tailWord_811885, baseEnd_811885] using wordTrace_append hprefix tailTrace_811885
  have hstable : (prefixWord ++ tailWord_811885).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811885).length < 2 ^ (prefixWord ++ tailWord_811885).sum := by decide
  have hdescent : baseEnd_811885 < baseStart_811885 := by decide
  rcases family_descends (prefixWord ++ tailWord_811885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811909 : List Nat := [1, 3, 1, 1, 3, 4, 3, 4]
def baseStart_811909 : Nat := 118140960795 + 811909 * 2 ^ 59
def prefixEnd_811909 : Nat := 4983230072969 + 3 ^ 40 * 811909 * 2
def baseEnd_811909 : Nat := 123525796951516781038105

theorem tailTrace_811909 : CollatzResearch.WordTrace tailWord_811909 prefixEnd_811909 123525796951516781038105 := by
  unfold tailWord_811909
  simp only [CollatzResearch.WordTrace]
  refine ⟨29612754015599830862782781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19741836010399887241855187 29612754015599830862782781)
  ·
    refine ⟨11104782755849936573543543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29612754015599830862782781 11104782755849936573543543)
    ·
      refine ⟨16657174133774904860315315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11104782755849936573543543 16657174133774904860315315)
      ·
        refine ⟨24985761200662357290472973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16657174133774904860315315 24985761200662357290472973)
        ·
          refine ⟨9369660450248383983927365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24985761200662357290472973 9369660450248383983927365)
          ·
            refine ⟨1756811334421571996986381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9369660450248383983927365 1756811334421571996986381)
            ·
              refine ⟨658804250408089498869893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1756811334421571996986381 658804250408089498869893)
              ·
                refine ⟨123525796951516781038105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 658804250408089498869893 123525796951516781038105)
                ·
                  rfl

theorem cell20_811909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 3, 4].length) (baseStart_811909 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_811909 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_811909 prefixEnd_811909 := by exact prefixLift 811909
  have htrace : WordTrace (prefixWord ++ tailWord_811909) baseStart_811909 baseEnd_811909 := by
    simpa [prefixWord, tailWord_811909, baseEnd_811909] using wordTrace_append hprefix tailTrace_811909
  have hstable : (prefixWord ++ tailWord_811909).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811909).length < 2 ^ (prefixWord ++ tailWord_811909).sum := by decide
  have hdescent : baseEnd_811909 < baseStart_811909 := by decide
  rcases family_descends (prefixWord ++ tailWord_811909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811940 : List Nat := [2, 3, 1, 2, 1, 2, 1, 6, 2]
def baseStart_811940 : Nat := 118140960795 + 811940 * 2 ^ 59
def prefixEnd_811940 : Nat := 4983230072969 + 3 ^ 40 * 811940 * 2
def baseEnd_811940 : Nat := 370591540099252013080855

theorem tailTrace_811940 : CollatzResearch.WordTrace tailWord_811940 prefixEnd_811940 370591540099252013080855 := by
  unfold tailWord_811940
  simp only [CollatzResearch.WordTrace]
  refine ⟨14806942339243761578580637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19742589785658348771440849 14806942339243761578580637)
  ·
    refine ⟨5552603377216410591967739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14806942339243761578580637 5552603377216410591967739)
    ·
      refine ⟨8328905065824615887951609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5552603377216410591967739 8328905065824615887951609)
      ·
        refine ⟨6246678799368461915963707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8328905065824615887951609 6246678799368461915963707)
        ·
          refine ⟨9370018199052692873945561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6246678799368461915963707 9370018199052692873945561)
          ·
            refine ⟨7027513649289519655459171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9370018199052692873945561 7027513649289519655459171)
            ·
              refine ⟨10541270473934279483188757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7027513649289519655459171 10541270473934279483188757)
              ·
                refine ⟨494122053465669350774473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10541270473934279483188757 494122053465669350774473)
                ·
                  refine ⟨370591540099252013080855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 494122053465669350774473 370591540099252013080855)
                  ·
                    rfl

theorem cell20_811940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 6, 2].length) (baseStart_811940 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_811940 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_811940 prefixEnd_811940 := by exact prefixLift 811940
  have htrace : WordTrace (prefixWord ++ tailWord_811940) baseStart_811940 baseEnd_811940 := by
    simpa [prefixWord, tailWord_811940, baseEnd_811940] using wordTrace_append hprefix tailTrace_811940
  have hstable : (prefixWord ++ tailWord_811940).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811940).length < 2 ^ (prefixWord ++ tailWord_811940).sum := by decide
  have hdescent : baseEnd_811940 < baseStart_811940 := by decide
  rcases family_descends (prefixWord ++ tailWord_811940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811961 : List Nat := [1, 2, 1, 4, 2, 2, 2, 2, 4]
def baseStart_811961 : Nat := 118140960795 + 811961 * 2 ^ 59
def prefixEnd_811961 : Nat := 4983230072969 + 3 ^ 40 * 811961 * 2
def baseEnd_811961 : Nat := 370601125071469273380769

theorem tailTrace_811961 : CollatzResearch.WordTrace tailWord_811961 prefixEnd_811961 370601125071469273380769 := by
  unfold tailWord_811961
  simp only [CollatzResearch.WordTrace]
  refine ⟨29614650611411443743675737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19743100407607629162450491 29614650611411443743675737)
  ·
    refine ⟨22210987958558582807756803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29614650611411443743675737 22210987958558582807756803)
    ·
      refine ⟨33316481937837874211635205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22210987958558582807756803 33316481937837874211635205)
      ·
        refine ⟨6246840363344601414681601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33316481937837874211635205 6246840363344601414681601)
        ·
          refine ⟨4685130272508451061011201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6246840363344601414681601 4685130272508451061011201)
          ·
            refine ⟨3513847704381338295758401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4685130272508451061011201 3513847704381338295758401)
            ·
              refine ⟨2635385778286003721818801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3513847704381338295758401 2635385778286003721818801)
              ·
                refine ⟨1976539333714502791364101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2635385778286003721818801 1976539333714502791364101)
                ·
                  refine ⟨370601125071469273380769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1976539333714502791364101 370601125071469273380769)
                  ·
                    rfl

theorem cell20_811961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 2, 4].length) (baseStart_811961 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_811961 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_811961 prefixEnd_811961 := by exact prefixLift 811961
  have htrace : WordTrace (prefixWord ++ tailWord_811961) baseStart_811961 baseEnd_811961 := by
    simpa [prefixWord, tailWord_811961, baseEnd_811961] using wordTrace_append hprefix tailTrace_811961
  have hstable : (prefixWord ++ tailWord_811961).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811961).length < 2 ^ (prefixWord ++ tailWord_811961).sum := by decide
  have hdescent : baseEnd_811961 < baseStart_811961 := by decide
  rcases family_descends (prefixWord ++ tailWord_811961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811968 : List Nat := [2, 1, 1, 2, 3, 4, 1, 6]
def baseStart_811968 : Nat := 118140960795 + 811968 * 2 ^ 59
def prefixEnd_811968 : Nat := 4983230072969 + 3 ^ 40 * 811968 * 2
def baseEnd_811968 : Nat := 123534773354069453382469

theorem tailTrace_811968 : CollatzResearch.WordTrace tailWord_811968 prefixEnd_811968 123534773354069453382469 := by
  unfold tailWord_811968
  simp only [CollatzResearch.WordTrace]
  refine ⟨14807452961193041969590279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19743270614924055959453705 14807452961193041969590279)
  ·
    refine ⟨22211179441789562954385419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14807452961193041969590279 22211179441789562954385419)
    ·
      refine ⟨33316769162684344431578129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22211179441789562954385419 33316769162684344431578129)
      ·
        refine ⟨24987576872013258323683597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33316769162684344431578129 24987576872013258323683597)
        ·
          refine ⟨9370341327004971871381349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24987576872013258323683597 9370341327004971871381349)
          ·
            refine ⟨1756938998813432225884003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9370341327004971871381349 1756938998813432225884003)
            ·
              refine ⟨2635408498220148338826005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1756938998813432225884003 2635408498220148338826005)
              ·
                refine ⟨123534773354069453382469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2635408498220148338826005 123534773354069453382469)
                ·
                  rfl

theorem cell20_811968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 6].length) (baseStart_811968 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_811968 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_811968 prefixEnd_811968 := by exact prefixLift 811968
  have htrace : WordTrace (prefixWord ++ tailWord_811968) baseStart_811968 baseEnd_811968 := by
    simpa [prefixWord, tailWord_811968, baseEnd_811968] using wordTrace_append hprefix tailTrace_811968
  have hstable : (prefixWord ++ tailWord_811968).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811968).length < 2 ^ (prefixWord ++ tailWord_811968).sum := by decide
  have hdescent : baseEnd_811968 < baseStart_811968 := by decide
  rcases family_descends (prefixWord ++ tailWord_811968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811975 : List Nat := [1, 1, 4, 1, 1, 2, 3, 2, 5]
def baseStart_811975 : Nat := 118140960795 + 811975 * 2 ^ 59
def prefixEnd_811975 : Nat := 4983230072969 + 3 ^ 40 * 811975 * 2
def baseEnd_811975 : Nat := 370607515052947446914045

theorem tailTrace_811975 : CollatzResearch.WordTrace tailWord_811975 prefixEnd_811975 370607515052947446914045 := by
  unfold tailWord_811975
  simp only [CollatzResearch.WordTrace]
  refine ⟨29615161233360724134685379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19743440822240482756456919 29615161233360724134685379)
  ·
    refine ⟨44422741850041086202028069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29615161233360724134685379 44422741850041086202028069)
    ·
      refine ⟨8329264096882703662880263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44422741850041086202028069 8329264096882703662880263)
      ·
        refine ⟨12493896145324055494320395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8329264096882703662880263 12493896145324055494320395)
        ·
          refine ⟨18740844217986083241480593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12493896145324055494320395 18740844217986083241480593)
          ·
            refine ⟨14055633163489562431110445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18740844217986083241480593 14055633163489562431110445)
            ·
              refine ⟨5270862436308585911666417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14055633163489562431110445 5270862436308585911666417)
              ·
                refine ⟨3953146827231439433749813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5270862436308585911666417 3953146827231439433749813)
                ·
                  refine ⟨370607515052947446914045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3953146827231439433749813 370607515052947446914045)
                  ·
                    rfl

theorem cell20_811975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 2, 5].length) (baseStart_811975 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_811975 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_811975 prefixEnd_811975 := by exact prefixLift 811975
  have htrace : WordTrace (prefixWord ++ tailWord_811975) baseStart_811975 baseEnd_811975 := by
    simpa [prefixWord, tailWord_811975, baseEnd_811975] using wordTrace_append hprefix tailTrace_811975
  have hstable : (prefixWord ++ tailWord_811975).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811975).length < 2 ^ (prefixWord ++ tailWord_811975).sum := by decide
  have hdescent : baseEnd_811975 < baseStart_811975 := by decide
  rcases family_descends (prefixWord ++ tailWord_811975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812002 : List Nat := [3, 3, 3, 1, 1, 2, 2, 5]
def baseStart_812002 : Nat := 118140960795 + 812002 * 2 ^ 59
def prefixEnd_812002 : Nat := 4983230072969 + 3 ^ 40 * 812002 * 2
def baseEnd_812002 : Nat := 123539946196218451004645

theorem tailTrace_812002 : CollatzResearch.WordTrace tailWord_812002 prefixEnd_812002 123539946196218451004645 := by
  unfold tailWord_812002
  simp only [CollatzResearch.WordTrace]
  refine ⟨7404036501065726936479565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19744097336175271830612173 7404036501065726936479565)
  ·
    refine ⟨2776513687899647601179837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7404036501065726936479565 2776513687899647601179837)
    ·
      refine ⟨1041192632962367850442439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2776513687899647601179837 1041192632962367850442439)
      ·
        refine ⟨1561788949443551775663659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1041192632962367850442439 1561788949443551775663659)
        ·
          refine ⟨2342683424165327663495489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1561788949443551775663659 2342683424165327663495489)
          ·
            refine ⟨1757012568123995747621617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2342683424165327663495489 1757012568123995747621617)
            ·
              refine ⟨1317759426092996810716213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1757012568123995747621617 1317759426092996810716213)
              ·
                refine ⟨123539946196218451004645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1317759426092996810716213 123539946196218451004645)
                ·
                  rfl

theorem cell20_812002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 5].length) (baseStart_812002 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_812002 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_812002 prefixEnd_812002 := by exact prefixLift 812002
  have htrace : WordTrace (prefixWord ++ tailWord_812002) baseStart_812002 baseEnd_812002 := by
    simpa [prefixWord, tailWord_812002, baseEnd_812002] using wordTrace_append hprefix tailTrace_812002
  have hstable : (prefixWord ++ tailWord_812002).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812002).length < 2 ^ (prefixWord ++ tailWord_812002).sum := by decide
  have hdescent : baseEnd_812002 < baseStart_812002 := by decide
  rcases family_descends (prefixWord ++ tailWord_812002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812005 : List Nat := [1, 3, 1, 6, 1, 2, 2, 1, 3]
def baseStart_812005 : Nat := 118140960795 + 812005 * 2 ^ 59
def prefixEnd_812005 : Nat := 4983230072969 + 3 ^ 40 * 812005 * 2
def baseEnd_812005 : Nat := 370621207870400675913923

theorem tailTrace_812005 : CollatzResearch.WordTrace tailWord_812005 prefixEnd_812005 370621207870400675913923 := by
  unfold tailWord_812005
  simp only [CollatzResearch.WordTrace]
  refine ⟨29616255423252039258277469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19744170282168026172184979 29616255423252039258277469)
  ·
    refine ⟨11106095783719514721854051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29616255423252039258277469 11106095783719514721854051)
    ·
      refine ⟨16659143675579272082781077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11106095783719514721854051 16659143675579272082781077)
      ·
        refine ⟨780897359792778378880363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 16659143675579272082781077 780897359792778378880363)
        ·
          refine ⟨1171346039689167568320545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 780897359792778378880363 1171346039689167568320545)
          ·
            refine ⟨878509529766875676240409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1171346039689167568320545 878509529766875676240409)
            ·
              refine ⟨658882147325156757180307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 878509529766875676240409 658882147325156757180307)
              ·
                refine ⟨988323220987735135770461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 658882147325156757180307 988323220987735135770461)
                ·
                  refine ⟨370621207870400675913923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 988323220987735135770461 370621207870400675913923)
                  ·
                    rfl

theorem cell20_812005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 2, 1, 3].length) (baseStart_812005 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_812005 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_812005 prefixEnd_812005 := by exact prefixLift 812005
  have htrace : WordTrace (prefixWord ++ tailWord_812005) baseStart_812005 baseEnd_812005 := by
    simpa [prefixWord, tailWord_812005, baseEnd_812005] using wordTrace_append hprefix tailTrace_812005
  have hstable : (prefixWord ++ tailWord_812005).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812005).length < 2 ^ (prefixWord ++ tailWord_812005).sum := by decide
  have hdescent : baseEnd_812005 < baseStart_812005 := by decide
  rcases family_descends (prefixWord ++ tailWord_812005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812092 : List Nat := [2, 2, 2, 2, 2, 2, 1, 5, 2]
def baseStart_812092 : Nat := 118140960795 + 812092 * 2 ^ 59
def prefixEnd_812092 : Nat := 4983230072969 + 3 ^ 40 * 812092 * 2
def baseEnd_812092 : Nat := 370660917041015040013567

theorem tailTrace_812092 : CollatzResearch.WordTrace tailWord_812092 prefixEnd_812092 370660917041015040013567 := by
  unfold tailWord_812092
  simp only [CollatzResearch.WordTrace]
  refine ⟨14809714286968426558347265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19746285715957902077796353 14809714286968426558347265)
  ·
    refine ⟨11107285715226319918760449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14809714286968426558347265 11107285715226319918760449)
    ·
      refine ⟨8330464286419739939070337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11107285715226319918760449 8330464286419739939070337)
      ·
        refine ⟨6247848214814804954302753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8330464286419739939070337 6247848214814804954302753)
        ·
          refine ⟨4685886161111103715727065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6247848214814804954302753 4685886161111103715727065)
          ·
            refine ⟨3514414620833327786795299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4685886161111103715727065 3514414620833327786795299)
            ·
              refine ⟨5271621931249991680192949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3514414620833327786795299 5271621931249991680192949)
              ·
                refine ⟨494214556054686720018089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5271621931249991680192949 494214556054686720018089)
                ·
                  refine ⟨370660917041015040013567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 494214556054686720018089 370660917041015040013567)
                  ·
                    rfl

theorem cell20_812092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 5, 2].length) (baseStart_812092 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_812092 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_812092 prefixEnd_812092 := by exact prefixLift 812092
  have htrace : WordTrace (prefixWord ++ tailWord_812092) baseStart_812092 baseEnd_812092 := by
    simpa [prefixWord, tailWord_812092, baseEnd_812092] using wordTrace_append hprefix tailTrace_812092
  have hstable : (prefixWord ++ tailWord_812092).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812092).length < 2 ^ (prefixWord ++ tailWord_812092).sum := by decide
  have hdescent : baseEnd_812092 < baseStart_812092 := by decide
  rcases family_descends (prefixWord ++ tailWord_812092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812096 : List Nat := [2, 1, 1, 2, 2, 3, 1, 2, 6]
def baseStart_812096 : Nat := 118140960795 + 812096 * 2 ^ 59
def prefixEnd_812096 : Nat := 4983230072969 + 3 ^ 40 * 812096 * 2
def baseEnd_812096 : Nat := 370662742750008803880217

theorem tailTrace_812096 : CollatzResearch.WordTrace tailWord_812096 prefixEnd_812096 370662742750008803880217 := by
  unfold tailWord_812096
  simp only [CollatzResearch.WordTrace]
  refine ⟨14809787232961180899920071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19746382977281574533226761 14809787232961180899920071)
  ·
    refine ⟨22214680849441771349880107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14809787232961180899920071 22214680849441771349880107)
    ·
      refine ⟨33322021274162657024820161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22214680849441771349880107 33322021274162657024820161)
      ·
        refine ⟨24991515955621992768615121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33322021274162657024820161 24991515955621992768615121)
        ·
          refine ⟨18743636966716494576461341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24991515955621992768615121 18743636966716494576461341)
          ·
            refine ⟨7028863862518685466173003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18743636966716494576461341 7028863862518685466173003)
            ·
              refine ⟨10543295793778028199259505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7028863862518685466173003 10543295793778028199259505)
              ·
                refine ⟨7907471845333521149444629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10543295793778028199259505 7907471845333521149444629)
                ·
                  refine ⟨370662742750008803880217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7907471845333521149444629 370662742750008803880217)
                  ·
                    rfl

theorem cell20_812096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 6].length) (baseStart_812096 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_812096 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_812096 prefixEnd_812096 := by exact prefixLift 812096
  have htrace : WordTrace (prefixWord ++ tailWord_812096) baseStart_812096 baseEnd_812096 := by
    simpa [prefixWord, tailWord_812096, baseEnd_812096] using wordTrace_append hprefix tailTrace_812096
  have hstable : (prefixWord ++ tailWord_812096).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812096).length < 2 ^ (prefixWord ++ tailWord_812096).sum := by decide
  have hdescent : baseEnd_812096 < baseStart_812096 := by decide
  rcases family_descends (prefixWord ++ tailWord_812096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812102 : List Nat := [6, 1, 1, 1, 1, 2, 3, 2, 3]
def baseStart_812102 : Nat := 118140960795 + 812102 * 2 ^ 59
def prefixEnd_812102 : Nat := 4983230072969 + 3 ^ 40 * 812102 * 2
def baseEnd_812102 : Nat := 370665481313499449680193

theorem tailTrace_812102 : CollatzResearch.WordTrace tailWord_812102 prefixEnd_812102 370665481313499449680193 := by
  unfold tailWord_812102
  simp only [CollatzResearch.WordTrace]
  refine ⟨925618540746894525767455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 19746528869267083216372373 925618540746894525767455)
  ·
    refine ⟨1388427811120341788651183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 925618540746894525767455 1388427811120341788651183)
    ·
      refine ⟨2082641716680512682976775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1388427811120341788651183 2082641716680512682976775)
      ·
        refine ⟨3123962575020769024465163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2082641716680512682976775 3123962575020769024465163)
        ·
          refine ⟨4685943862531153536697745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3123962575020769024465163 4685943862531153536697745)
          ·
            refine ⟨3514457896898365152523309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4685943862531153536697745 3514457896898365152523309)
            ·
              refine ⟨1317921711336886932196241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3514457896898365152523309 1317921711336886932196241)
              ·
                refine ⟨988441283502665199147181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1317921711336886932196241 988441283502665199147181)
                ·
                  refine ⟨370665481313499449680193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 988441283502665199147181 370665481313499449680193)
                  ·
                    rfl

theorem cell20_812102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_812102 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_812102 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_812102 prefixEnd_812102 := by exact prefixLift 812102
  have htrace : WordTrace (prefixWord ++ tailWord_812102) baseStart_812102 baseEnd_812102 := by
    simpa [prefixWord, tailWord_812102, baseEnd_812102] using wordTrace_append hprefix tailTrace_812102
  have hstable : (prefixWord ++ tailWord_812102).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812102).length < 2 ^ (prefixWord ++ tailWord_812102).sum := by decide
  have hdescent : baseEnd_812102 < baseStart_812102 := by decide
  rcases family_descends (prefixWord ++ tailWord_812102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812106 : List Nat := [3, 1, 2, 1, 1, 2, 5, 2, 3]
def baseStart_812106 : Nat := 118140960795 + 812106 * 2 ^ 59
def prefixEnd_812106 : Nat := 4983230072969 + 3 ^ 40 * 812106 * 2
def baseEnd_812106 : Nat := 370667307022493213546843

theorem tailTrace_812106 : CollatzResearch.WordTrace tailWord_812106 prefixEnd_812106 370667307022493213546843 := by
  unfold tailWord_812106
  simp only [CollatzResearch.WordTrace]
  refine ⟨7404984798971533376926043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19746626130590755671802781 7404984798971533376926043)
  ·
    refine ⟨11107477198457300065389065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7404984798971533376926043 11107477198457300065389065)
    ·
      refine ⟨8330607898842975049041799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11107477198457300065389065 8330607898842975049041799)
      ·
        refine ⟨12495911848264462573562699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8330607898842975049041799 12495911848264462573562699)
        ·
          refine ⟨18743867772396693860344049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12495911848264462573562699 18743867772396693860344049)
          ·
            refine ⟨14057900829297520395258037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18743867772396693860344049 14057900829297520395258037)
            ·
              refine ⟨1317928202746642537055441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14057900829297520395258037 1317928202746642537055441)
              ·
                refine ⟨988446152059981902791581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1317928202746642537055441 988446152059981902791581)
                ·
                  refine ⟨370667307022493213546843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 988446152059981902791581 370667307022493213546843)
                  ·
                    rfl

theorem cell20_812106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 2, 3].length) (baseStart_812106 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_812106 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_812106 prefixEnd_812106 := by exact prefixLift 812106
  have htrace : WordTrace (prefixWord ++ tailWord_812106) baseStart_812106 baseEnd_812106 := by
    simpa [prefixWord, tailWord_812106, baseEnd_812106] using wordTrace_append hprefix tailTrace_812106
  have hstable : (prefixWord ++ tailWord_812106).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812106).length < 2 ^ (prefixWord ++ tailWord_812106).sum := by decide
  have hdescent : baseEnd_812106 < baseStart_812106 := by decide
  rcases family_descends (prefixWord ++ tailWord_812106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812109 : List Nat := [1, 6, 1, 1, 1, 2, 2, 4, 2]
def baseStart_812109 : Nat := 118140960795 + 812109 * 2 ^ 59
def prefixEnd_812109 : Nat := 4983230072969 + 3 ^ 40 * 812109 * 2
def baseEnd_812109 : Nat := 370668676304238536446831

theorem tailTrace_812109 : CollatzResearch.WordTrace tailWord_812109 prefixEnd_812109 370668676304238536446831 := by
  unfold tailWord_812109
  simp only [CollatzResearch.WordTrace]
  refine ⟨29620048614875265020063381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19746699076583510013375587 29620048614875265020063381)
  ·
    refine ⟨1388439778822278047815471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 29620048614875265020063381 1388439778822278047815471)
    ·
      refine ⟨2082659668233417071723207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1388439778822278047815471 2082659668233417071723207)
      ·
        refine ⟨3123989502350125607584811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2082659668233417071723207 3123989502350125607584811)
        ·
          refine ⟨4685984253525188411377217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3123989502350125607584811 4685984253525188411377217)
          ·
            refine ⟨3514488190143891308532913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4685984253525188411377217 3514488190143891308532913)
            ·
              refine ⟨2635866142607918481399685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3514488190143891308532913 2635866142607918481399685)
              ·
                refine ⟨494224901738984715262441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2635866142607918481399685 494224901738984715262441)
                ·
                  refine ⟨370668676304238536446831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 494224901738984715262441 370668676304238536446831)
                  ·
                    rfl

theorem cell20_812109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_812109 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_812109 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_812109 prefixEnd_812109 := by exact prefixLift 812109
  have htrace : WordTrace (prefixWord ++ tailWord_812109) baseStart_812109 baseEnd_812109 := by
    simpa [prefixWord, tailWord_812109, baseEnd_812109] using wordTrace_append hprefix tailTrace_812109
  have hstable : (prefixWord ++ tailWord_812109).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812109).length < 2 ^ (prefixWord ++ tailWord_812109).sum := by decide
  have hdescent : baseEnd_812109 < baseStart_812109 := by decide
  rcases family_descends (prefixWord ++ tailWord_812109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812130 : List Nat := [3, 3, 2, 2, 1, 1, 2, 2, 4]
def baseStart_812130 : Nat := 118140960795 + 812130 * 2 ^ 59
def prefixEnd_812130 : Nat := 4983230072969 + 3 ^ 40 * 812130 * 2
def baseEnd_812130 : Nat := 370678261276455796746745

theorem tailTrace_812130 : CollatzResearch.WordTrace tailWord_812130 prefixEnd_812130 370678261276455796746745 := by
  unfold tailWord_812130
  simp only [CollatzResearch.WordTrace]
  refine ⟨7405203636949796401644461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19747209698532790404385229 7405203636949796401644461)
  ·
    refine ⟨2776951363856173650616673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7405203636949796401644461 2776951363856173650616673)
    ·
      refine ⟨2082713522892130237962505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2776951363856173650616673 2082713522892130237962505)
      ·
        refine ⟨1562035142169097678471879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2082713522892130237962505 1562035142169097678471879)
        ·
          refine ⟨2343052713253646517707819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1562035142169097678471879 2343052713253646517707819)
          ·
            refine ⟨3514579069880469776561729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2343052713253646517707819 3514579069880469776561729)
            ·
              refine ⟨2635934302410352332421297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3514579069880469776561729 2635934302410352332421297)
              ·
                refine ⟨1976950726807764249315973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2635934302410352332421297 1976950726807764249315973)
                ·
                  refine ⟨370678261276455796746745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1976950726807764249315973 370678261276455796746745)
                  ·
                    rfl

theorem cell20_812130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_812130 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_812130 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_812130 prefixEnd_812130 := by exact prefixLift 812130
  have htrace : WordTrace (prefixWord ++ tailWord_812130) baseStart_812130 baseEnd_812130 := by
    simpa [prefixWord, tailWord_812130, baseEnd_812130] using wordTrace_append hprefix tailTrace_812130
  have hstable : (prefixWord ++ tailWord_812130).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812130).length < 2 ^ (prefixWord ++ tailWord_812130).sum := by decide
  have hdescent : baseEnd_812130 < baseStart_812130 := by decide
  rcases family_descends (prefixWord ++ tailWord_812130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812137 : List Nat := [1, 2, 1, 1, 1, 8, 2, 4]
def baseStart_812137 : Nat := 118140960795 + 812137 * 2 ^ 59
def prefixEnd_812137 : Nat := 4983230072969 + 3 ^ 40 * 812137 * 2
def baseEnd_812137 : Nat := 123560485422398294504461

theorem tailTrace_812137 : CollatzResearch.WordTrace tailWord_812137 prefixEnd_812137 123560485422398294504461 := by
  unfold tailWord_812137
  simp only [CollatzResearch.WordTrace]
  refine ⟨29621069858773825802082665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19747379905849217201388443 29621069858773825802082665)
  ·
    refine ⟨22215802394080369351561999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29621069858773825802082665 22215802394080369351561999)
    ·
      refine ⟨33323703591120554027342999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22215802394080369351561999 33323703591120554027342999)
      ·
        refine ⟨49985555386680831041014499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33323703591120554027342999 49985555386680831041014499)
        ·
          refine ⟨74978333080021246561521749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49985555386680831041014499 74978333080021246561521749)
          ·
            refine ⟨878652340781498983142833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 74978333080021246561521749 878652340781498983142833)
            ·
              refine ⟨658989255586124237357125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 878652340781498983142833 658989255586124237357125)
              ·
                refine ⟨123560485422398294504461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 658989255586124237357125 123560485422398294504461)
                ·
                  rfl

theorem cell20_812137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 2, 4].length) (baseStart_812137 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_812137 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_812137 prefixEnd_812137 := by exact prefixLift 812137
  have htrace : WordTrace (prefixWord ++ tailWord_812137) baseStart_812137 baseEnd_812137 := by
    simpa [prefixWord, tailWord_812137, baseEnd_812137] using wordTrace_append hprefix tailTrace_812137
  have hstable : (prefixWord ++ tailWord_812137).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812137).length < 2 ^ (prefixWord ++ tailWord_812137).sum := by decide
  have hdescent : baseEnd_812137 < baseStart_812137 := by decide
  rcases family_descends (prefixWord ++ tailWord_812137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812178 : List Nat := [3, 2, 3, 1, 1, 4, 2, 1, 3]
def baseStart_812178 : Nat := 118140960795 + 812178 * 2 ^ 59
def prefixEnd_812178 : Nat := 4983230072969 + 3 ^ 40 * 812178 * 2
def baseEnd_812178 : Nat := 370700169784380963146549

theorem tailTrace_812178 : CollatzResearch.WordTrace tailWord_812178 prefixEnd_812178 370700169784380963146549 := by
  unfold tailWord_812178
  simp only [CollatzResearch.WordTrace]
  refine ⟨7405641312906322451081297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19748376834416859869550125 7405641312906322451081297)
  ·
    refine ⟨5554230984679741838310973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7405641312906322451081297 5554230984679741838310973)
    ·
      refine ⟨2082836619254903189366615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5554230984679741838310973 2082836619254903189366615)
      ·
        refine ⟨3124254928882354784049923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2082836619254903189366615 3124254928882354784049923)
        ·
          refine ⟨4686382393323532176074885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3124254928882354784049923 4686382393323532176074885)
          ·
            refine ⟨878696698748162283014041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4686382393323532176074885 878696698748162283014041)
            ·
              refine ⟨659022524061121712260531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 878696698748162283014041 659022524061121712260531)
              ·
                refine ⟨988533786091682568390797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 659022524061121712260531 988533786091682568390797)
                ·
                  refine ⟨370700169784380963146549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 988533786091682568390797 370700169784380963146549)
                  ·
                    rfl

theorem cell20_812178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 2, 1, 3].length) (baseStart_812178 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_812178 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_812178 prefixEnd_812178 := by exact prefixLift 812178
  have htrace : WordTrace (prefixWord ++ tailWord_812178) baseStart_812178 baseEnd_812178 := by
    simpa [prefixWord, tailWord_812178, baseEnd_812178] using wordTrace_append hprefix tailTrace_812178
  have hstable : (prefixWord ++ tailWord_812178).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812178).length < 2 ^ (prefixWord ++ tailWord_812178).sum := by decide
  have hdescent : baseEnd_812178 < baseStart_812178 := by decide
  rcases family_descends (prefixWord ++ tailWord_812178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812179 : List Nat := [1, 1, 1, 2, 1, 2, 5, 7]
def baseStart_812179 : Nat := 118140960795 + 812179 * 2 ^ 59
def prefixEnd_812179 : Nat := 4983230072969 + 3 ^ 40 * 812179 * 2
def baseEnd_812179 : Nat := 123566875403876468037737

theorem tailTrace_812179 : CollatzResearch.WordTrace tailWord_812179 prefixEnd_812179 123566875403876468037737 := by
  unfold tailWord_812179
  simp only [CollatzResearch.WordTrace]
  refine ⟨29622601724621666975111591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19748401149747777983407727 29622601724621666975111591)
  ·
    refine ⟨44433902586932500462667387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29622601724621666975111591 44433902586932500462667387)
    ·
      refine ⟨66650853880398750694001081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44433902586932500462667387 66650853880398750694001081)
      ·
        refine ⟨49988140410299063020500811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66650853880398750694001081 49988140410299063020500811)
        ·
          refine ⟨74982210615448594530751217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49988140410299063020500811 74982210615448594530751217)
          ·
            refine ⟨56236657961586445898063413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74982210615448594530751217 56236657961586445898063413)
            ·
              refine ⟨5272186683898729302943445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56236657961586445898063413 5272186683898729302943445)
              ·
                refine ⟨123566875403876468037737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5272186683898729302943445 123566875403876468037737)
                ·
                  rfl

theorem cell20_812179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 7].length) (baseStart_812179 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_812179 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_812179 prefixEnd_812179 := by exact prefixLift 812179
  have htrace : WordTrace (prefixWord ++ tailWord_812179) baseStart_812179 baseEnd_812179 := by
    simpa [prefixWord, tailWord_812179, baseEnd_812179] using wordTrace_append hprefix tailTrace_812179
  have hstable : (prefixWord ++ tailWord_812179).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812179).length < 2 ^ (prefixWord ++ tailWord_812179).sum := by decide
  have hdescent : baseEnd_812179 < baseStart_812179 := by decide
  rcases family_descends (prefixWord ++ tailWord_812179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812196 : List Nat := [2, 3, 1, 2, 3, 1, 2, 6]
def baseStart_812196 : Nat := 118140960795 + 812196 * 2 ^ 59
def prefixEnd_812196 : Nat := 4983230072969 + 3 ^ 40 * 812196 * 2
def baseEnd_812196 : Nat := 123569461824950966848825

theorem tailTrace_812196 : CollatzResearch.WordTrace tailWord_812196 prefixEnd_812196 123569461824950966848825 := by
  unfold tailWord_812196
  simp only [CollatzResearch.WordTrace]
  refine ⟨14811610882780039439240221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19748814510373385918986961 14811610882780039439240221)
  ·
    refine ⟨5554354081042514789715083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14811610882780039439240221 5554354081042514789715083)
    ·
      refine ⟨8331531121563772184572625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5554354081042514789715083 8331531121563772184572625)
      ·
        refine ⟨6248648341172829138429469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8331531121563772184572625 6248648341172829138429469)
        ·
          refine ⟨2343243127939810926911051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6248648341172829138429469 2343243127939810926911051)
          ·
            refine ⟨3514864691909716390366577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2343243127939810926911051 3514864691909716390366577)
            ·
              refine ⟨2636148518932287292774933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3514864691909716390366577 2636148518932287292774933)
              ·
                refine ⟨123569461824950966848825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2636148518932287292774933 123569461824950966848825)
                ·
                  rfl

theorem cell20_812196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 6].length) (baseStart_812196 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_812196 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_812196 prefixEnd_812196 := by exact prefixLift 812196
  have htrace : WordTrace (prefixWord ++ tailWord_812196) baseStart_812196 baseEnd_812196 := by
    simpa [prefixWord, tailWord_812196, baseEnd_812196] using wordTrace_append hprefix tailTrace_812196
  have hstable : (prefixWord ++ tailWord_812196).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812196).length < 2 ^ (prefixWord ++ tailWord_812196).sum := by decide
  have hdescent : baseEnd_812196 < baseStart_812196 := by decide
  rcases family_descends (prefixWord ++ tailWord_812196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812217 : List Nat := [1, 2, 1, 4, 1, 11]
def baseStart_812217 : Nat := 118140960795 + 812217 * 2 ^ 59
def prefixEnd_812217 : Nat := 4983230072969 + 3 ^ 40 * 812217 * 2
def baseEnd_812217 : Nat := 13730295201743339290607

theorem tailTrace_812217 : CollatzResearch.WordTrace tailWord_812217 prefixEnd_812217 13730295201743339290607 := by
  unfold tailWord_812217
  simp only [CollatzResearch.WordTrace]
  refine ⟨29623987698483999464994905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19749325132322666309996603 29623987698483999464994905)
  ·
    refine ⟨22217990773862999598746179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29623987698483999464994905 22217990773862999598746179)
    ·
      refine ⟨33326986160794499398119269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22217990773862999598746179 33326986160794499398119269)
      ·
        refine ⟨6248809905148968637147363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33326986160794499398119269 6248809905148968637147363)
        ·
          refine ⟨9373214857723452955721045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6248809905148968637147363 9373214857723452955721045)
          ·
            refine ⟨13730295201743339290607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 9373214857723452955721045 13730295201743339290607)
            ·
              rfl

theorem cell20_812217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 11].length) (baseStart_812217 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_812217 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_812217 prefixEnd_812217 := by exact prefixLift 812217
  have htrace : WordTrace (prefixWord ++ tailWord_812217) baseStart_812217 baseEnd_812217 := by
    simpa [prefixWord, tailWord_812217, baseEnd_812217] using wordTrace_append hprefix tailTrace_812217
  have hstable : (prefixWord ++ tailWord_812217).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812217).length < 2 ^ (prefixWord ++ tailWord_812217).sum := by decide
  have hdescent : baseEnd_812217 < baseStart_812217 := by decide
  rcases family_descends (prefixWord ++ tailWord_812217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812220 : List Nat := [2, 2, 2, 3, 2, 1, 1, 4, 3]
def baseStart_812220 : Nat := 118140960795 + 812220 * 2 ^ 59
def prefixEnd_812220 : Nat := 4983230072969 + 3 ^ 40 * 812220 * 2
def baseEnd_812220 : Nat := 370719339728815483746377

theorem tailTrace_812220 : CollatzResearch.WordTrace tailWord_812220 prefixEnd_812220 370719339728815483746377 := by
  unfold tailWord_812220
  simp only [CollatzResearch.WordTrace]
  refine ⟨14812048558736565488677057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19749398078315420651569409 14812048558736565488677057)
  ·
    refine ⟨11109036419052424116507793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14812048558736565488677057 11109036419052424116507793)
    ·
      refine ⟨8331777314289318087380845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11109036419052424116507793 8331777314289318087380845)
      ·
        refine ⟨3124416492858494282767817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8331777314289318087380845 3124416492858494282767817)
        ·
          refine ⟨2343312369643870712075863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3124416492858494282767817 2343312369643870712075863)
          ·
            refine ⟨3514968554465806068113795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2343312369643870712075863 3514968554465806068113795)
            ·
              refine ⟨5272452831698709102170693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3514968554465806068113795 5272452831698709102170693)
              ·
                refine ⟨988584905943507956657005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5272452831698709102170693 988584905943507956657005)
                ·
                  refine ⟨370719339728815483746377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 988584905943507956657005 370719339728815483746377)
                  ·
                    rfl

theorem cell20_812220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 4, 3].length) (baseStart_812220 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_812220 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_812220 prefixEnd_812220 := by exact prefixLift 812220
  have htrace : WordTrace (prefixWord ++ tailWord_812220) baseStart_812220 baseEnd_812220 := by
    simpa [prefixWord, tailWord_812220, baseEnd_812220] using wordTrace_append hprefix tailTrace_812220
  have hstable : (prefixWord ++ tailWord_812220).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812220).length < 2 ^ (prefixWord ++ tailWord_812220).sum := by decide
  have hdescent : baseEnd_812220 < baseStart_812220 := by decide
  rcases family_descends (prefixWord ++ tailWord_812220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812226 : List Nat := [3, 5, 1, 1, 3, 1, 1, 5]
def baseStart_812226 : Nat := 118140960795 + 812226 * 2 ^ 59
def prefixEnd_812226 : Nat := 4983230072969 + 3 ^ 40 * 812226 * 2
def baseEnd_812226 : Nat := 123574026097435376515451

theorem tailTrace_812226 : CollatzResearch.WordTrace tailWord_812226 prefixEnd_812226 123574026097435376515451 := by
  unfold tailWord_812226
  simp only [CollatzResearch.WordTrace]
  refine ⟨7406078988862848500518133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19749543970300929334715021 7406078988862848500518133)
  ·
    refine ⟨694319905205892046923575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7406078988862848500518133 694319905205892046923575)
    ·
      refine ⟨1041479857808838070385363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 694319905205892046923575 1041479857808838070385363)
      ·
        refine ⟨1562219786713257105578045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1041479857808838070385363 1562219786713257105578045)
        ·
          refine ⟨585832420017471414591767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1562219786713257105578045 585832420017471414591767)
          ·
            refine ⟨878748630026207121887651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 585832420017471414591767 878748630026207121887651)
            ·
              refine ⟨1318122945039310682831477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 878748630026207121887651 1318122945039310682831477)
              ·
                refine ⟨123574026097435376515451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1318122945039310682831477 123574026097435376515451)
                ·
                  rfl

theorem cell20_812226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 5].length) (baseStart_812226 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_812226 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_812226 prefixEnd_812226 := by exact prefixLift 812226
  have htrace : WordTrace (prefixWord ++ tailWord_812226) baseStart_812226 baseEnd_812226 := by
    simpa [prefixWord, tailWord_812226, baseEnd_812226] using wordTrace_append hprefix tailTrace_812226
  have hstable : (prefixWord ++ tailWord_812226).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812226).length < 2 ^ (prefixWord ++ tailWord_812226).sum := by decide
  have hdescent : baseEnd_812226 < baseStart_812226 := by decide
  rcases family_descends (prefixWord ++ tailWord_812226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812234 : List Nat := [3, 1, 2, 1, 3, 2, 3, 5]
def baseStart_812234 : Nat := 118140960795 + 812234 * 2 ^ 59
def prefixEnd_812234 : Nat := 4983230072969 + 3 ^ 40 * 812234 * 2
def baseEnd_812234 : Nat := 123575243236764552426551

theorem tailTrace_812234 : CollatzResearch.WordTrace tailWord_812234 prefixEnd_812234 123575243236764552426551 := by
  unfold tailWord_812234
  simp only [CollatzResearch.WordTrace]
  refine ⟨7406151934855602842090939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19749738492948274245575837 7406151934855602842090939)
  ·
    refine ⟨11109227902283404263136409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7406151934855602842090939 11109227902283404263136409)
    ·
      refine ⟨8331920926712553197352307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11109227902283404263136409 8331920926712553197352307)
      ·
        refine ⟨12497881390068829796028461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8331920926712553197352307 12497881390068829796028461)
        ·
          refine ⟨4686705521275811173510673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12497881390068829796028461 4686705521275811173510673)
          ·
            refine ⟨3515029140956858380133005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4686705521275811173510673 3515029140956858380133005)
            ·
              refine ⟨1318135927858821892549877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3515029140956858380133005 1318135927858821892549877)
              ·
                refine ⟨123575243236764552426551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1318135927858821892549877 123575243236764552426551)
                ·
                  rfl

theorem cell20_812234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 5].length) (baseStart_812234 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_812234 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_812234 prefixEnd_812234 := by exact prefixLift 812234
  have htrace : WordTrace (prefixWord ++ tailWord_812234) baseStart_812234 baseEnd_812234 := by
    simpa [prefixWord, tailWord_812234, baseEnd_812234] using wordTrace_append hprefix tailTrace_812234
  have hstable : (prefixWord ++ tailWord_812234).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812234).length < 2 ^ (prefixWord ++ tailWord_812234).sum := by decide
  have hdescent : baseEnd_812234 < baseStart_812234 := by decide
  rcases family_descends (prefixWord ++ tailWord_812234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812255 : List Nat := [1, 1, 2, 3, 2, 1, 2, 8]
def baseStart_812255 : Nat := 118140960795 + 812255 * 2 ^ 59
def prefixEnd_812255 : Nat := 4983230072969 + 3 ^ 40 * 812255 * 2
def baseEnd_812255 : Nat := 123578438227503639193189

theorem tailTrace_812255 : CollatzResearch.WordTrace tailWord_812255 prefixEnd_812255 123578438227503639193189 := by
  unfold tailWord_812255
  simp only [CollatzResearch.WordTrace]
  refine ⟨29625373672346331954878219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19750249114897554636585479 29625373672346331954878219)
  ·
    refine ⟨44438060508519497932317329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29625373672346331954878219 44438060508519497932317329)
    ·
      refine ⟨33328545381389623449237997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44438060508519497932317329 33328545381389623449237997)
      ·
        refine ⟨12498204518021108793464249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33328545381389623449237997 12498204518021108793464249)
        ·
          refine ⟨9373653388515831595098187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12498204518021108793464249 9373653388515831595098187)
          ·
            refine ⟨14060480082773747392647281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9373653388515831595098187 14060480082773747392647281)
            ·
              refine ⟨10545360062080310544485461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14060480082773747392647281 10545360062080310544485461)
              ·
                refine ⟨123578438227503639193189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10545360062080310544485461 123578438227503639193189)
                ·
                  rfl

theorem cell20_812255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 8].length) (baseStart_812255 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_812255 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_812255 prefixEnd_812255 := by exact prefixLift 812255
  have htrace : WordTrace (prefixWord ++ tailWord_812255) baseStart_812255 baseEnd_812255 := by
    simpa [prefixWord, tailWord_812255, baseEnd_812255] using wordTrace_append hprefix tailTrace_812255
  have hstable : (prefixWord ++ tailWord_812255).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812255).length < 2 ^ (prefixWord ++ tailWord_812255).sum := by decide
  have hdescent : baseEnd_812255 < baseStart_812255 := by decide
  rcases family_descends (prefixWord ++ tailWord_812255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812261 : List Nat := [1, 3, 1, 4, 3, 1, 2, 3, 2]
def baseStart_812261 : Nat := 118140960795 + 812261 * 2 ^ 59
def prefixEnd_812261 : Nat := 4983230072969 + 3 ^ 40 * 812261 * 2
def baseEnd_812261 : Nat := 370738053246001563379543

theorem tailTrace_812261 : CollatzResearch.WordTrace tailWord_812261 prefixEnd_812261 370738053246001563379543 := by
  unfold tailWord_812261
  simp only [CollatzResearch.WordTrace]
  refine ⟨29625592510324594979596637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19750395006883063319731091 29625592510324594979596637)
  ·
    refine ⟨11109597191371723117348739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29625592510324594979596637 11109597191371723117348739)
    ·
      refine ⟨16664395787057584676023109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11109597191371723117348739 16664395787057584676023109)
      ·
        refine ⟨3124574210073297126754333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16664395787057584676023109 3124574210073297126754333)
        ·
          refine ⟨1171715328777486422532875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3124574210073297126754333 1171715328777486422532875)
          ·
            refine ⟨1757572993166229633799313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1171715328777486422532875 1757572993166229633799313)
            ·
              refine ⟨1318179744874672225349485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1757572993166229633799313 1318179744874672225349485)
              ·
                refine ⟨494317404328002084506057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1318179744874672225349485 494317404328002084506057)
                ·
                  refine ⟨370738053246001563379543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 494317404328002084506057 370738053246001563379543)
                  ·
                    rfl

theorem cell20_812261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 3, 2].length) (baseStart_812261 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_812261 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_812261 prefixEnd_812261 := by exact prefixLift 812261
  have htrace : WordTrace (prefixWord ++ tailWord_812261) baseStart_812261 baseEnd_812261 := by
    simpa [prefixWord, tailWord_812261, baseEnd_812261] using wordTrace_append hprefix tailTrace_812261
  have hstable : (prefixWord ++ tailWord_812261).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812261).length < 2 ^ (prefixWord ++ tailWord_812261).sum := by decide
  have hdescent : baseEnd_812261 < baseStart_812261 := by decide
  rcases family_descends (prefixWord ++ tailWord_812261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812293 : List Nat := [1, 3, 1, 1, 2, 1, 4, 7]
def baseStart_812293 : Nat := 118140960795 + 812293 * 2 ^ 59
def prefixEnd_812293 : Nat := 4983230072969 + 3 ^ 40 * 812293 * 2
def baseEnd_812293 : Nat := 123584219639317224770915

theorem tailTrace_812293 : CollatzResearch.WordTrace tailWord_812293 prefixEnd_812293 123584219639317224770915 := by
  unfold tailWord_812293
  simp only [CollatzResearch.WordTrace]
  refine ⟨29626759646208664444761533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19751173097472442963174355 29626759646208664444761533)
  ·
    refine ⟨11110034867328249166785575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29626759646208664444761533 11110034867328249166785575)
    ·
      refine ⟨16665052300992373750178363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11110034867328249166785575 16665052300992373750178363)
      ·
        refine ⟨24997578451488560625267545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16665052300992373750178363 24997578451488560625267545)
        ·
          refine ⟨18748183838616420468950659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24997578451488560625267545 18748183838616420468950659)
          ·
            refine ⟨28122275757924630703425989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18748183838616420468950659 28122275757924630703425989)
            ·
              refine ⟨5272926704610868256892373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28122275757924630703425989 5272926704610868256892373)
              ·
                refine ⟨123584219639317224770915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5272926704610868256892373 123584219639317224770915)
                ·
                  rfl

theorem cell20_812293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 7].length) (baseStart_812293 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_812293 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_812293 prefixEnd_812293 := by exact prefixLift 812293
  have htrace : WordTrace (prefixWord ++ tailWord_812293) baseStart_812293 baseEnd_812293 := by
    simpa [prefixWord, tailWord_812293, baseEnd_812293] using wordTrace_append hprefix tailTrace_812293
  have hstable : (prefixWord ++ tailWord_812293).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812293).length < 2 ^ (prefixWord ++ tailWord_812293).sum := by decide
  have hdescent : baseEnd_812293 < baseStart_812293 := by decide
  rcases family_descends (prefixWord ++ tailWord_812293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812306 : List Nat := [3, 2, 4, 2, 1, 1, 1, 6]
def baseStart_812306 : Nat := 118140960795 + 812306 * 2 ^ 59
def prefixEnd_812306 : Nat := 4983230072969 + 3 ^ 40 * 812306 * 2
def baseEnd_812306 : Nat := 123586197490727135626453

theorem tailTrace_812306 : CollatzResearch.WordTrace tailWord_812306 prefixEnd_812306 123586197490727135626453 := by
  unfold tailWord_812306
  simp only [CollatzResearch.WordTrace]
  refine ⟨7406808448790391916246193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19751489196774378443323181 7406808448790391916246193)
  ·
    refine ⟨5555106336592793937184645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7406808448790391916246193 5555106336592793937184645)
    ·
      refine ⟨1041582438111148863222121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5555106336592793937184645 1041582438111148863222121)
      ·
        refine ⟨781186828583361647416591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1041582438111148863222121 781186828583361647416591)
        ·
          refine ⟨1171780242875042471124887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 781186828583361647416591 1171780242875042471124887)
          ·
            refine ⟨1757670364312563706687331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1171780242875042471124887 1757670364312563706687331)
            ·
              refine ⟨2636505546468845560030997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1757670364312563706687331 2636505546468845560030997)
              ·
                refine ⟨123586197490727135626453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2636505546468845560030997 123586197490727135626453)
                ·
                  rfl

theorem cell20_812306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 6].length) (baseStart_812306 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_812306 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_812306 prefixEnd_812306 := by exact prefixLift 812306
  have htrace : WordTrace (prefixWord ++ tailWord_812306) baseStart_812306 baseEnd_812306 := by
    simpa [prefixWord, tailWord_812306, baseEnd_812306] using wordTrace_append hprefix tailTrace_812306
  have hstable : (prefixWord ++ tailWord_812306).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812306).length < 2 ^ (prefixWord ++ tailWord_812306).sum := by decide
  have hdescent : baseEnd_812306 < baseStart_812306 := by decide
  rcases family_descends (prefixWord ++ tailWord_812306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812337 : List Nat := [1, 2, 2, 3, 3, 2, 3, 2, 2]
def baseStart_812337 : Nat := 118140960795 + 812337 * 2 ^ 59
def prefixEnd_812337 : Nat := 4983230072969 + 3 ^ 40 * 812337 * 2
def baseEnd_812337 : Nat := 370772741716883076845899

theorem tailTrace_812337 : CollatzResearch.WordTrace tailWord_812337 prefixEnd_812337 370772741716883076845899 := by
  unfold tailWord_812337
  simp only [CollatzResearch.WordTrace]
  refine ⟨29628364458049259959363265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19752242972032839972908843 29628364458049259959363265)
  ·
    refine ⟨22221273343536944969522449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29628364458049259959363265 22221273343536944969522449)
    ·
      refine ⟨16665955007652708727141837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22221273343536944969522449 16665955007652708727141837)
      ·
        refine ⟨6249733127869765772678189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16665955007652708727141837 6249733127869765772678189)
        ·
          refine ⟨2343649922951162164754321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6249733127869765772678189 2343649922951162164754321)
          ·
            refine ⟨1757737442213371623565741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2343649922951162164754321 1757737442213371623565741)
            ·
              refine ⟨659151540830014358837153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1757737442213371623565741 659151540830014358837153)
              ·
                refine ⟨494363655622510769127865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 659151540830014358837153 494363655622510769127865)
                ·
                  refine ⟨370772741716883076845899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 494363655622510769127865 370772741716883076845899)
                  ·
                    rfl

theorem cell20_812337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 3, 2, 2].length) (baseStart_812337 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_812337 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_812337 prefixEnd_812337 := by exact prefixLift 812337
  have htrace : WordTrace (prefixWord ++ tailWord_812337) baseStart_812337 baseEnd_812337 := by
    simpa [prefixWord, tailWord_812337, baseEnd_812337] using wordTrace_append hprefix tailTrace_812337
  have hstable : (prefixWord ++ tailWord_812337).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812337).length < 2 ^ (prefixWord ++ tailWord_812337).sum := by decide
  have hdescent : baseEnd_812337 < baseStart_812337 := by decide
  rcases family_descends (prefixWord ++ tailWord_812337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812341 : List Nat := [1, 3, 3, 1, 2, 2, 3, 1, 4]
def baseStart_812341 : Nat := 118140960795 + 812341 * 2 ^ 59
def prefixEnd_812341 : Nat := 4983230072969 + 3 ^ 40 * 812341 * 2
def baseEnd_812341 : Nat := 370774567425876840712549

theorem tailTrace_812341 : CollatzResearch.WordTrace tailWord_812341 prefixEnd_812341 370774567425876840712549 := by
  unfold tailWord_812341
  simp only [CollatzResearch.WordTrace]
  refine ⟨29628510350034768642508877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19752340233356512428339251 29628510350034768642508877)
  ·
    refine ⟨11110691381263038240940829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29628510350034768642508877 11110691381263038240940829)
    ·
      refine ⟨4166509267973639340352811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11110691381263038240940829 4166509267973639340352811)
      ·
        refine ⟨6249763901960459010529217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4166509267973639340352811 6249763901960459010529217)
        ·
          refine ⟨4687322926470344257896913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6249763901960459010529217 4687322926470344257896913)
          ·
            refine ⟨3515492194852758193422685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4687322926470344257896913 3515492194852758193422685)
            ·
              refine ⟨1318309573069784322533507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3515492194852758193422685 1318309573069784322533507)
              ·
                refine ⟨1977464359604676483800261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1318309573069784322533507 1977464359604676483800261)
                ·
                  refine ⟨370774567425876840712549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1977464359604676483800261 370774567425876840712549)
                  ·
                    rfl

theorem cell20_812341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 1, 4].length) (baseStart_812341 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_812341 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_812341 prefixEnd_812341 := by exact prefixLift 812341
  have htrace : WordTrace (prefixWord ++ tailWord_812341) baseStart_812341 baseEnd_812341 := by
    simpa [prefixWord, tailWord_812341, baseEnd_812341] using wordTrace_append hprefix tailTrace_812341
  have hstable : (prefixWord ++ tailWord_812341).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812341).length < 2 ^ (prefixWord ++ tailWord_812341).sum := by decide
  have hdescent : baseEnd_812341 < baseStart_812341 := by decide
  rcases family_descends (prefixWord ++ tailWord_812341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812348 : List Nat := [2, 2, 2, 2, 1, 4, 2, 5]
def baseStart_812348 : Nat := 118140960795 + 812348 * 2 ^ 59
def prefixEnd_812348 : Nat := 4983230072969 + 3 ^ 40 * 812348 * 2
def baseEnd_812348 : Nat := 123592587472205309159729

theorem tailTrace_812348 : CollatzResearch.WordTrace tailWord_812348 prefixEnd_812348 123592587472205309159729 := by
  unfold tailWord_812348
  simp only [CollatzResearch.WordTrace]
  refine ⟨14814382830504704419006849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19752510440672939225342465 14814382830504704419006849)
  ·
    refine ⟨11110787122878528314255137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14814382830504704419006849 11110787122878528314255137)
    ·
      refine ⟨8333090342158896235691353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11110787122878528314255137 8333090342158896235691353)
      ·
        refine ⟨6249817756619172176768515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8333090342158896235691353 6249817756619172176768515)
        ·
          refine ⟨9374726634928758265152773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6249817756619172176768515 9374726634928758265152773)
          ·
            refine ⟨1757761244049142174716145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9374726634928758265152773 1757761244049142174716145)
            ·
              refine ⟨1318320933036856631037109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1757761244049142174716145 1318320933036856631037109)
              ·
                refine ⟨123592587472205309159729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1318320933036856631037109 123592587472205309159729)
                ·
                  rfl

theorem cell20_812348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 5].length) (baseStart_812348 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_812348 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_812348 prefixEnd_812348 := by exact prefixLift 812348
  have htrace : WordTrace (prefixWord ++ tailWord_812348) baseStart_812348 baseEnd_812348 := by
    simpa [prefixWord, tailWord_812348, baseEnd_812348] using wordTrace_append hprefix tailTrace_812348
  have hstable : (prefixWord ++ tailWord_812348).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812348).length < 2 ^ (prefixWord ++ tailWord_812348).sum := by decide
  have hdescent : baseEnd_812348 < baseStart_812348 := by decide
  rcases family_descends (prefixWord ++ tailWord_812348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812351 : List Nat := [1, 1, 2, 2, 4, 4, 2, 1, 3]
def baseStart_812351 : Nat := 118140960795 + 812351 * 2 ^ 59
def prefixEnd_812351 : Nat := 4983230072969 + 3 ^ 40 * 812351 * 2
def baseEnd_812351 : Nat := 370779131698361250379175

theorem tailTrace_812351 : CollatzResearch.WordTrace tailWord_812351 prefixEnd_812351 370779131698361250379175 := by
  unfold tailWord_812351
  simp only [CollatzResearch.WordTrace]
  refine ⟨29628875079998540350372907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19752583386665693566915271 29628875079998540350372907)
  ·
    refine ⟨44443312619997810525559361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29628875079998540350372907 44443312619997810525559361)
    ·
      refine ⟨33332484464998357894169521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44443312619997810525559361 33332484464998357894169521)
      ·
        refine ⟨24999363348748768420627141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33332484464998357894169521 24999363348748768420627141)
        ·
          refine ⟨4687380627890394078867589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24999363348748768420627141 4687380627890394078867589)
          ·
            refine ⟨878883867729448889787673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4687380627890394078867589 878883867729448889787673)
            ·
              refine ⟨659162900797086667340755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 878883867729448889787673 659162900797086667340755)
              ·
                refine ⟨988744351195630001011133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 659162900797086667340755 988744351195630001011133)
                ·
                  refine ⟨370779131698361250379175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 988744351195630001011133 370779131698361250379175)
                  ·
                    rfl

theorem cell20_812351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 2, 1, 3].length) (baseStart_812351 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_812351 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_812351 prefixEnd_812351 := by exact prefixLift 812351
  have htrace : WordTrace (prefixWord ++ tailWord_812351) baseStart_812351 baseEnd_812351 := by
    simpa [prefixWord, tailWord_812351, baseEnd_812351] using wordTrace_append hprefix tailTrace_812351
  have hstable : (prefixWord ++ tailWord_812351).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812351).length < 2 ^ (prefixWord ++ tailWord_812351).sum := by decide
  have hdescent : baseEnd_812351 < baseStart_812351 := by decide
  rcases family_descends (prefixWord ++ tailWord_812351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812362 : List Nat := [3, 1, 2, 1, 1, 1, 1, 6, 4]
def baseStart_812362 : Nat := 118140960795 + 812362 * 2 ^ 59
def prefixEnd_812362 : Nat := 4983230072969 + 3 ^ 40 * 812362 * 2
def baseEnd_812362 : Nat := 370784152398094101012463

theorem tailTrace_812362 : CollatzResearch.WordTrace tailWord_812362 prefixEnd_812362 370784152398094101012463 := by
  unfold tailWord_812362
  simp only [CollatzResearch.WordTrace]
  refine ⟨7407319070739672307255835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19752850855305792819348893 7407319070739672307255835)
  ·
    refine ⟨11110978606109508460883753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7407319070739672307255835 11110978606109508460883753)
    ·
      refine ⟨8333233954582131345662815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11110978606109508460883753 8333233954582131345662815)
      ·
        refine ⟨12499850931873197018494223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8333233954582131345662815 12499850931873197018494223)
        ·
          refine ⟨18749776397809795527741335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12499850931873197018494223 18749776397809795527741335)
          ·
            refine ⟨28124664596714693291612003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18749776397809795527741335 28124664596714693291612003)
            ·
              refine ⟨42186996895072039937418005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28124664596714693291612003 42186996895072039937418005)
              ·
                refine ⟨1977515479456501872066469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 42186996895072039937418005 1977515479456501872066469)
                ·
                  refine ⟨370784152398094101012463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1977515479456501872066469 370784152398094101012463)
                  ·
                    rfl

theorem cell20_812362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 6, 4].length) (baseStart_812362 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_812362 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_812362 prefixEnd_812362 := by exact prefixLift 812362
  have htrace : WordTrace (prefixWord ++ tailWord_812362) baseStart_812362 baseEnd_812362 := by
    simpa [prefixWord, tailWord_812362, baseEnd_812362] using wordTrace_append hprefix tailTrace_812362
  have hstable : (prefixWord ++ tailWord_812362).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812362).length < 2 ^ (prefixWord ++ tailWord_812362).sum := by decide
  have hdescent : baseEnd_812362 < baseStart_812362 := by decide
  rcases family_descends (prefixWord ++ tailWord_812362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812369 : List Nat := [1, 2, 2, 1, 4, 1, 1, 8]
def baseStart_812369 : Nat := 118140960795 + 812369 * 2 ^ 59
def prefixEnd_812369 : Nat := 4983230072969 + 3 ^ 40 * 812369 * 2
def baseEnd_812369 : Nat := 123595782462944395926367

theorem tailTrace_812369 : CollatzResearch.WordTrace tailWord_812369 prefixEnd_812369 123595782462944395926367 := by
  unfold tailWord_812369
  simp only [CollatzResearch.WordTrace]
  refine ⟨29629531593933329424528161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19753021062622219616352107 29629531593933329424528161)
  ·
    refine ⟨22222148695449997068396121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29629531593933329424528161 22222148695449997068396121)
    ·
      refine ⟨16666611521587497801297091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22222148695449997068396121 16666611521587497801297091)
      ·
        refine ⟨24999917282381246701945637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16666611521587497801297091 24999917282381246701945637)
        ·
          refine ⟨4687484490446483756614807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24999917282381246701945637 4687484490446483756614807)
          ·
            refine ⟨7031226735669725634922211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4687484490446483756614807 7031226735669725634922211)
            ·
              refine ⟨10546840103504588452383317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7031226735669725634922211 10546840103504588452383317)
              ·
                refine ⟨123595782462944395926367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10546840103504588452383317 123595782462944395926367)
                ·
                  rfl

theorem cell20_812369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 8].length) (baseStart_812369 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_812369 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_812369 prefixEnd_812369 := by exact prefixLift 812369
  have htrace : WordTrace (prefixWord ++ tailWord_812369) baseStart_812369 baseEnd_812369 := by
    simpa [prefixWord, tailWord_812369, baseEnd_812369] using wordTrace_append hprefix tailTrace_812369
  have hstable : (prefixWord ++ tailWord_812369).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812369).length < 2 ^ (prefixWord ++ tailWord_812369).sum := by decide
  have hdescent : baseEnd_812369 < baseStart_812369 := by decide
  rcases family_descends (prefixWord ++ tailWord_812369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812392 : List Nat := [2, 1, 4, 2, 3, 2, 2, 2, 2]
def baseStart_812392 : Nat := 118140960795 + 812392 * 2 ^ 59
def prefixEnd_812392 : Nat := 4983230072969 + 3 ^ 40 * 812392 * 2
def baseEnd_812392 : Nat := 370797845215547330012341

theorem tailTrace_812392 : CollatzResearch.WordTrace tailWord_812392 prefixEnd_812392 370797845215547330012341 := by
  unfold tailWord_812392
  simp only [CollatzResearch.WordTrace]
  refine ⟨14815185236425002176307715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19753580315233336235076953 14815185236425002176307715)
  ·
    refine ⟨22222777854637503264461573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14815185236425002176307715 22222777854637503264461573)
    ·
      refine ⟨4166770847744531862086545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22222777854637503264461573 4166770847744531862086545)
      ·
        refine ⟨3125078135808398896564909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4166770847744531862086545 3125078135808398896564909)
        ·
          refine ⟨1171904300928149586211841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3125078135808398896564909 1171904300928149586211841)
          ·
            refine ⟨878928225696112189658881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1171904300928149586211841 878928225696112189658881)
            ·
              refine ⟨659196169272084142244161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 878928225696112189658881 659196169272084142244161)
              ·
                refine ⟨494397126954063106683121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 659196169272084142244161 494397126954063106683121)
                ·
                  refine ⟨370797845215547330012341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 494397126954063106683121 370797845215547330012341)
                  ·
                    rfl

theorem cell20_812392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 2, 2, 2].length) (baseStart_812392 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_812392 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_812392 prefixEnd_812392 := by exact prefixLift 812392
  have htrace : WordTrace (prefixWord ++ tailWord_812392) baseStart_812392 baseEnd_812392 := by
    simpa [prefixWord, tailWord_812392, baseEnd_812392] using wordTrace_append hprefix tailTrace_812392
  have hstable : (prefixWord ++ tailWord_812392).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812392).length < 2 ^ (prefixWord ++ tailWord_812392).sum := by decide
  have hdescent : baseEnd_812392 < baseStart_812392 := by decide
  rcases family_descends (prefixWord ++ tailWord_812392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812396 : List Nat := [2, 2, 1, 1, 5, 2, 1, 4, 2]
def baseStart_812396 : Nat := 118140960795 + 812396 * 2 ^ 59
def prefixEnd_812396 : Nat := 4983230072969 + 3 ^ 40 * 812396 * 2
def baseEnd_812396 : Nat := 370799670924541093878991

theorem tailTrace_812396 : CollatzResearch.WordTrace tailWord_812396 prefixEnd_812396 370799670924541093878991 := by
  unfold tailWord_812396
  simp only [CollatzResearch.WordTrace]
  refine ⟨14815258182417756517880521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19753677576557008690507361 14815258182417756517880521)
  ·
    refine ⟨11111443636813317388410391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14815258182417756517880521 11111443636813317388410391)
    ·
      refine ⟨16667165455219976082615587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11111443636813317388410391 16667165455219976082615587)
      ·
        refine ⟨25000748182829964123923381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16667165455219976082615587 25000748182829964123923381)
        ·
          refine ⟨2343820142140309136617817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25000748182829964123923381 2343820142140309136617817)
          ·
            refine ⟨1757865106605231852463363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2343820142140309136617817 1757865106605231852463363)
            ·
              refine ⟨2636797659907847778695045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1757865106605231852463363 2636797659907847778695045)
              ·
                refine ⟨494399561232721458505321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2636797659907847778695045 494399561232721458505321)
                ·
                  refine ⟨370799670924541093878991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 494399561232721458505321 370799670924541093878991)
                  ·
                    rfl

theorem cell20_812396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 4, 2].length) (baseStart_812396 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_812396 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_812396 prefixEnd_812396 := by exact prefixLift 812396
  have htrace : WordTrace (prefixWord ++ tailWord_812396) baseStart_812396 baseEnd_812396 := by
    simpa [prefixWord, tailWord_812396, baseEnd_812396] using wordTrace_append hprefix tailTrace_812396
  have hstable : (prefixWord ++ tailWord_812396).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812396).length < 2 ^ (prefixWord ++ tailWord_812396).sum := by decide
  have hdescent : baseEnd_812396 < baseStart_812396 := by decide
  rcases family_descends (prefixWord ++ tailWord_812396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812400 : List Nat := [2, 1, 1, 1, 4, 2, 2, 3, 4]
def baseStart_812400 : Nat := 118140960795 + 812400 * 2 ^ 59
def prefixEnd_812400 : Nat := 4983230072969 + 3 ^ 40 * 812400 * 2
def baseEnd_812400 : Nat := 370801496633534857745641

theorem tailTrace_812400 : CollatzResearch.WordTrace tailWord_812400 prefixEnd_812400 370801496633534857745641 := by
  unfold tailWord_812400
  simp only [CollatzResearch.WordTrace]
  refine ⟨14815331128410510859453327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19753774837880681145937769 14815331128410510859453327)
  ·
    refine ⟨22222996692615766289179991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14815331128410510859453327 22222996692615766289179991)
    ·
      refine ⟨33334495038923649433769987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22222996692615766289179991 33334495038923649433769987)
      ·
        refine ⟨50001742558385474150654981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33334495038923649433769987 50001742558385474150654981)
        ·
          refine ⟨9375326729697276403247809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50001742558385474150654981 9375326729697276403247809)
          ·
            refine ⟨7031495047272957302435857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9375326729697276403247809 7031495047272957302435857)
            ·
              refine ⟨5273621285454717976826893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7031495047272957302435857 5273621285454717976826893)
              ·
                refine ⟨1977607982045519241310085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5273621285454717976826893 1977607982045519241310085)
                ·
                  refine ⟨370801496633534857745641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1977607982045519241310085 370801496633534857745641)
                  ·
                    rfl

theorem cell20_812400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 3, 4].length) (baseStart_812400 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_812400 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_812400 prefixEnd_812400 := by exact prefixLift 812400
  have htrace : WordTrace (prefixWord ++ tailWord_812400) baseStart_812400 baseEnd_812400 := by
    simpa [prefixWord, tailWord_812400, baseEnd_812400] using wordTrace_append hprefix tailTrace_812400
  have hstable : (prefixWord ++ tailWord_812400).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812400).length < 2 ^ (prefixWord ++ tailWord_812400).sum := by decide
  have hdescent : baseEnd_812400 < baseStart_812400 := by decide
  rcases family_descends (prefixWord ++ tailWord_812400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812444 : List Nat := [2, 2, 3, 4, 1, 2, 1, 2, 3]
def baseStart_812444 : Nat := 118140960795 + 812444 * 2 ^ 59
def prefixEnd_812444 : Nat := 4983230072969 + 3 ^ 40 * 812444 * 2
def baseEnd_812444 : Nat := 370821579432466260278795

theorem tailTrace_812444 : CollatzResearch.WordTrace tailWord_812444 prefixEnd_812444 370821579432466260278795 := by
  unfold tailWord_812444
  simp only [CollatzResearch.WordTrace]
  refine ⟨14816133534330808616754193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19754844712441078155672257 14816133534330808616754193)
  ·
    refine ⟨11112100150748106462565645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14816133534330808616754193 11112100150748106462565645)
    ·
      refine ⟨4167037556530539923462117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11112100150748106462565645 4167037556530539923462117)
      ·
        refine ⟨781319541849476235649147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4167037556530539923462117 781319541849476235649147)
        ·
          refine ⟨1171979312774214353473721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 781319541849476235649147 1171979312774214353473721)
          ·
            refine ⟨878984484580660765105291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1171979312774214353473721 878984484580660765105291)
            ·
              refine ⟨1318476726870991147657937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 878984484580660765105291 1318476726870991147657937)
              ·
                refine ⟨988857545153243360743453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1318476726870991147657937 988857545153243360743453)
                ·
                  refine ⟨370821579432466260278795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 988857545153243360743453 370821579432466260278795)
                  ·
                    rfl

theorem cell20_812444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 2, 3].length) (baseStart_812444 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_812444 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_812444 prefixEnd_812444 := by exact prefixLift 812444
  have htrace : WordTrace (prefixWord ++ tailWord_812444) baseStart_812444 baseEnd_812444 := by
    simpa [prefixWord, tailWord_812444, baseEnd_812444] using wordTrace_append hprefix tailTrace_812444
  have hstable : (prefixWord ++ tailWord_812444).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812444).length < 2 ^ (prefixWord ++ tailWord_812444).sum := by decide
  have hdescent : baseEnd_812444 < baseStart_812444 := by decide
  rcases family_descends (prefixWord ++ tailWord_812444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812455 : List Nat := [1, 1, 6, 1, 1, 1, 4, 1, 4]
def baseStart_812455 : Nat := 118140960795 + 812455 * 2 ^ 59
def prefixEnd_812455 : Nat := 4983230072969 + 3 ^ 40 * 812455 * 2
def baseEnd_812455 : Nat := 370826600132199110912083

theorem tailTrace_812455 : CollatzResearch.WordTrace tailWord_812455 prefixEnd_812455 370826600132199110912083 := by
  unfold tailWord_812455
  simp only [CollatzResearch.WordTrace]
  refine ⟨29632668271621766112158819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19755112181081177408105879 29632668271621766112158819)
  ·
    refine ⟨44449002407432649168238229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29632668271621766112158819 44449002407432649168238229)
    ·
      refine ⟨2083546987848405429761167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 44449002407432649168238229 2083546987848405429761167)
      ·
        refine ⟨3125320481772608144641751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2083546987848405429761167 3125320481772608144641751)
        ·
          refine ⟨4687980722658912216962627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3125320481772608144641751 4687980722658912216962627)
          ·
            refine ⟨7031971083988368325443941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4687980722658912216962627 7031971083988368325443941)
            ·
              refine ⟨1318494578247819061020739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7031971083988368325443941 1318494578247819061020739)
              ·
                refine ⟨1977741867371728591531109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1318494578247819061020739 1977741867371728591531109)
                ·
                  refine ⟨370826600132199110912083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1977741867371728591531109 370826600132199110912083)
                  ·
                    rfl

theorem cell20_812455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 1, 4].length) (baseStart_812455 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_812455 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_812455 prefixEnd_812455 := by exact prefixLift 812455
  have htrace : WordTrace (prefixWord ++ tailWord_812455) baseStart_812455 baseEnd_812455 := by
    simpa [prefixWord, tailWord_812455, baseEnd_812455] using wordTrace_append hprefix tailTrace_812455
  have hstable : (prefixWord ++ tailWord_812455).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812455).length < 2 ^ (prefixWord ++ tailWord_812455).sum := by decide
  have hdescent : baseEnd_812455 < baseStart_812455 := by decide
  rcases family_descends (prefixWord ++ tailWord_812455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812565 : List Nat := [1, 3, 2, 1, 3, 4, 2, 2, 2]
def baseStart_812565 : Nat := 118140960795 + 812565 * 2 ^ 59
def prefixEnd_812565 : Nat := 4983230072969 + 3 ^ 40 * 812565 * 2
def baseEnd_812565 : Nat := 370876807129527617244967

theorem tailTrace_812565 : CollatzResearch.WordTrace tailWord_812565 prefixEnd_812565 370876807129527617244967 := by
  unfold tailWord_812565
  simp only [CollatzResearch.WordTrace]
  refine ⟨29636680301223254898663149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19757786867482169932442099 29636680301223254898663149)
  ·
    refine ⟨11113755112958720586998681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29636680301223254898663149 11113755112958720586998681)
    ·
      refine ⟨8335316334719040440249011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11113755112958720586998681 8335316334719040440249011)
      ·
        refine ⟨12502974502078560660373517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8335316334719040440249011 12502974502078560660373517)
        ·
          refine ⟨4688615438279460247640069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12502974502078560660373517 4688615438279460247640069)
          ·
            refine ⟨879115394677398796432513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4688615438279460247640069 879115394677398796432513)
            ·
              refine ⟨659336546008049097324385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 879115394677398796432513 659336546008049097324385)
              ·
                refine ⟨494502409506036822993289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 659336546008049097324385 494502409506036822993289)
                ·
                  refine ⟨370876807129527617244967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 494502409506036822993289 370876807129527617244967)
                  ·
                    rfl

theorem cell20_812565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 2, 2, 2].length) (baseStart_812565 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_812565 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_812565 prefixEnd_812565 := by exact prefixLift 812565
  have htrace : WordTrace (prefixWord ++ tailWord_812565) baseStart_812565 baseEnd_812565 := by
    simpa [prefixWord, tailWord_812565, baseEnd_812565] using wordTrace_append hprefix tailTrace_812565
  have hstable : (prefixWord ++ tailWord_812565).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812565).length < 2 ^ (prefixWord ++ tailWord_812565).sum := by decide
  have hdescent : baseEnd_812565 < baseStart_812565 := by decide
  rcases family_descends (prefixWord ++ tailWord_812565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812576 : List Nat := [2, 1, 1, 6, 1, 1, 3, 5]
def baseStart_812576 : Nat := 118140960795 + 812576 * 2 ^ 59
def prefixEnd_812576 : Nat := 4983230072969 + 3 ^ 40 * 812576 * 2
def baseEnd_812576 : Nat := 123627275943086822626085

theorem tailTrace_812576 : CollatzResearch.WordTrace tailWord_812576 prefixEnd_812576 123627275943086822626085 := by
  unfold tailWord_812576
  simp only [CollatzResearch.WordTrace]
  refine ⟨14818540752091701888656791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19758054336122269184875721 14818540752091701888656791)
  ·
    refine ⟨22227811128137552832985187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14818540752091701888656791 22227811128137552832985187)
    ·
      refine ⟨33341716692206329249477781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22227811128137552832985187 33341716692206329249477781)
      ·
        refine ⟨1562892969947171683569271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 33341716692206329249477781 1562892969947171683569271)
        ·
          refine ⟨2344339454920757525353907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1562892969947171683569271 2344339454920757525353907)
          ·
            refine ⟨3516509182381136288030861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2344339454920757525353907 3516509182381136288030861)
            ·
              refine ⟨1318690943392926108011573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3516509182381136288030861 1318690943392926108011573)
              ·
                refine ⟨123627275943086822626085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1318690943392926108011573 123627275943086822626085)
                ·
                  rfl

theorem cell20_812576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 5].length) (baseStart_812576 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_812576 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_812576 prefixEnd_812576 := by exact prefixLift 812576
  have htrace : WordTrace (prefixWord ++ tailWord_812576) baseStart_812576 baseEnd_812576 := by
    simpa [prefixWord, tailWord_812576, baseEnd_812576] using wordTrace_append hprefix tailTrace_812576
  have hstable : (prefixWord ++ tailWord_812576).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812576).length < 2 ^ (prefixWord ++ tailWord_812576).sum := by decide
  have hdescent : baseEnd_812576 < baseStart_812576 := by decide
  rcases family_descends (prefixWord ++ tailWord_812576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812607 : List Nat := [1, 1, 2, 2, 3, 3, 1, 5, 2]
def baseStart_812607 : Nat := 118140960795 + 812607 * 2 ^ 59
def prefixEnd_812607 : Nat := 4983230072969 + 3 ^ 40 * 812607 * 2
def baseEnd_812607 : Nat := 370895977073962137844795

theorem tailTrace_812607 : CollatzResearch.WordTrace tailWord_812607 prefixEnd_812607 370895977073962137844795 := by
  unfold tailWord_812607
  simp only [CollatzResearch.WordTrace]
  refine ⟨29638212167071096071692075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19758808111380730714461383 29638212167071096071692075)
  ·
    refine ⟨44457318250606644107538113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29638212167071096071692075 44457318250606644107538113)
    ·
      refine ⟨33342988687954983080653585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44457318250606644107538113 33342988687954983080653585)
      ·
        refine ⟨25007241515966237310490189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33342988687954983080653585 25007241515966237310490189)
        ·
          refine ⟨9377715568487338991433821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25007241515966237310490189 9377715568487338991433821)
          ·
            refine ⟨3516643338182752121787683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9377715568487338991433821 3516643338182752121787683)
            ·
              refine ⟨5274965007274128182681525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3516643338182752121787683 5274965007274128182681525)
              ·
                refine ⟨494527969431949517126393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5274965007274128182681525 494527969431949517126393)
                ·
                  refine ⟨370895977073962137844795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 494527969431949517126393 370895977073962137844795)
                  ·
                    rfl

theorem cell20_812607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 5, 2].length) (baseStart_812607 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_812607 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_812607 prefixEnd_812607 := by exact prefixLift 812607
  have htrace : WordTrace (prefixWord ++ tailWord_812607) baseStart_812607 baseEnd_812607 := by
    simpa [prefixWord, tailWord_812607, baseEnd_812607] using wordTrace_append hprefix tailTrace_812607
  have hstable : (prefixWord ++ tailWord_812607).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812607).length < 2 ^ (prefixWord ++ tailWord_812607).sum := by decide
  have hdescent : baseEnd_812607 < baseStart_812607 := by decide
  rcases family_descends (prefixWord ++ tailWord_812607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812673 : List Nat := [1, 2, 4, 2, 1, 2, 8]
def baseStart_812673 : Nat := 118140960795 + 812673 * 2 ^ 59
def prefixEnd_812673 : Nat := 4983230072969 + 3 ^ 40 * 812673 * 2
def baseEnd_812673 : Nat := 41214011252484360182725

theorem tailTrace_812673 : CollatzResearch.WordTrace tailWord_812673 prefixEnd_812673 41214011252484360182725 := by
  unfold tailWord_812673
  simp only [CollatzResearch.WordTrace]
  refine ⟨29640619384831989343594673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19760412923221326229063115 29640619384831989343594673)
  ·
    refine ⟨22230464538623992007696005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29640619384831989343594673 22230464538623992007696005)
    ·
      refine ⟨4168212100991998501443001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22230464538623992007696005 4168212100991998501443001)
      ·
        refine ⟨3126159075743998876082251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4168212100991998501443001 3126159075743998876082251)
        ·
          refine ⟨4689238613615998314123377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3126159075743998876082251 4689238613615998314123377)
          ·
            refine ⟨3516928960211998735592533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4689238613615998314123377 3516928960211998735592533)
            ·
              refine ⟨41214011252484360182725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3516928960211998735592533 41214011252484360182725)
              ·
                rfl

theorem cell20_812673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 8].length) (baseStart_812673 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_812673 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_812673 prefixEnd_812673 := by exact prefixLift 812673
  have htrace : WordTrace (prefixWord ++ tailWord_812673) baseStart_812673 baseEnd_812673 := by
    simpa [prefixWord, tailWord_812673, baseEnd_812673] using wordTrace_append hprefix tailTrace_812673
  have hstable : (prefixWord ++ tailWord_812673).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812673).length < 2 ^ (prefixWord ++ tailWord_812673).sum := by decide
  have hdescent : baseEnd_812673 < baseStart_812673 := by decide
  rcases family_descends (prefixWord ++ tailWord_812673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812735 : List Nat := [1, 1, 2, 2, 2, 3, 4, 2, 3]
def baseStart_812735 : Nat := 118140960795 + 812735 * 2 ^ 59
def prefixEnd_812735 : Nat := 4983230072969 + 3 ^ 40 * 812735 * 2
def baseEnd_812735 : Nat := 370954399761762581577605

theorem tailTrace_812735 : CollatzResearch.WordTrace tailWord_812735 prefixEnd_812735 370954399761762581577605 := by
  unfold tailWord_812735
  simp only [CollatzResearch.WordTrace]
  refine ⟨29642880710607373932351659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19761920473738249288234439 29642880710607373932351659)
  ·
    refine ⟨44464321065911060898527489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29642880710607373932351659 44464321065911060898527489)
    ·
      refine ⟨33348240799433295673895617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44464321065911060898527489 33348240799433295673895617)
      ·
        refine ⟨25011180599574971755421713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33348240799433295673895617 25011180599574971755421713)
        ·
          refine ⟨18758385449681228816566285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25011180599574971755421713 18758385449681228816566285)
          ·
            refine ⟨7034394543630460806212357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18758385449681228816566285 7034394543630460806212357)
            ·
              refine ⟨1318948976930711401164817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7034394543630460806212357 1318948976930711401164817)
              ·
                refine ⟨989211732698033550873613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1318948976930711401164817 989211732698033550873613)
                ·
                  refine ⟨370954399761762581577605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 989211732698033550873613 370954399761762581577605)
                  ·
                    rfl

theorem cell20_812735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 2, 3].length) (baseStart_812735 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_812735 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_812735 prefixEnd_812735 := by exact prefixLift 812735
  have htrace : WordTrace (prefixWord ++ tailWord_812735) baseStart_812735 baseEnd_812735 := by
    simpa [prefixWord, tailWord_812735, baseEnd_812735] using wordTrace_append hprefix tailTrace_812735
  have hstable : (prefixWord ++ tailWord_812735).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812735).length < 2 ^ (prefixWord ++ tailWord_812735).sum := by decide
  have hdescent : baseEnd_812735 < baseStart_812735 := by decide
  rcases family_descends (prefixWord ++ tailWord_812735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812776 : List Nat := [2, 1, 4, 1, 3, 2, 2, 3, 2]
def baseStart_812776 : Nat := 118140960795 + 812776 * 2 ^ 59
def prefixEnd_812776 : Nat := 4983230072969 + 3 ^ 40 * 812776 * 2
def baseEnd_812776 : Nat := 370973113278948661210771

theorem tailTrace_812776 : CollatzResearch.WordTrace tailWord_812776 prefixEnd_812776 370973113278948661210771 := by
  unfold tailWord_812776
  simp only [CollatzResearch.WordTrace]
  refine ⟨14822188051729418967297091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19762917402305891956396121 14822188051729418967297091)
  ·
    refine ⟨22233282077594128450945637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14822188051729418967297091 22233282077594128450945637)
    ·
      refine ⟨4168740389548899084552307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22233282077594128450945637 4168740389548899084552307)
      ·
        refine ⟨6253110584323348626828461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4168740389548899084552307 6253110584323348626828461)
        ·
          refine ⟨2344916469121255735060673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6253110584323348626828461 2344916469121255735060673)
          ·
            refine ⟨1758687351840941801295505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2344916469121255735060673 1758687351840941801295505)
            ·
              refine ⟨1319015513880706350971629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1758687351840941801295505 1319015513880706350971629)
              ·
                refine ⟨494630817705264881614361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1319015513880706350971629 494630817705264881614361)
                ·
                  refine ⟨370973113278948661210771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 494630817705264881614361 370973113278948661210771)
                  ·
                    rfl

theorem cell20_812776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 3, 2].length) (baseStart_812776 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_812776 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_812776 prefixEnd_812776 := by exact prefixLift 812776
  have htrace : WordTrace (prefixWord ++ tailWord_812776) baseStart_812776 baseEnd_812776 := by
    simpa [prefixWord, tailWord_812776, baseEnd_812776] using wordTrace_append hprefix tailTrace_812776
  have hstable : (prefixWord ++ tailWord_812776).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812776).length < 2 ^ (prefixWord ++ tailWord_812776).sum := by decide
  have hdescent : baseEnd_812776 < baseStart_812776 := by decide
  rcases family_descends (prefixWord ++ tailWord_812776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812790 : List Nat := [5, 1, 1, 1, 1, 3, 3, 2, 3]
def baseStart_812790 : Nat := 118140960795 + 812790 * 2 ^ 59
def prefixEnd_812790 : Nat := 4983230072969 + 3 ^ 40 * 812790 * 2
def baseEnd_812790 : Nat := 370979503260426834744047

theorem tailTrace_812790 : CollatzResearch.WordTrace tailWord_812790 prefixEnd_812790 370979503260426834744047 := by
  unfold tailWord_812790
  simp only [CollatzResearch.WordTrace]
  refine ⟨1852805420338007395350239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19763257816938745550402549 1852805420338007395350239)
  ·
    refine ⟨2779208130507011093025359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1852805420338007395350239 2779208130507011093025359)
    ·
      refine ⟨4168812195760516639538039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2779208130507011093025359 4168812195760516639538039)
      ·
        refine ⟨6253218293640774959307059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4168812195760516639538039 6253218293640774959307059)
        ·
          refine ⟨9379827440461162438960589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6253218293640774959307059 9379827440461162438960589)
          ·
            refine ⟨3517435290172935914610221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9379827440461162438960589 3517435290172935914610221)
            ·
              refine ⟨1319038233814850967978833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3517435290172935914610221 1319038233814850967978833)
              ·
                refine ⟨989278675361138225984125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1319038233814850967978833 989278675361138225984125)
                ·
                  refine ⟨370979503260426834744047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 989278675361138225984125 370979503260426834744047)
                  ·
                    rfl

theorem cell20_812790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_812790 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_812790 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_812790 prefixEnd_812790 := by exact prefixLift 812790
  have htrace : WordTrace (prefixWord ++ tailWord_812790) baseStart_812790 baseEnd_812790 := by
    simpa [prefixWord, tailWord_812790, baseEnd_812790] using wordTrace_append hprefix tailTrace_812790
  have hstable : (prefixWord ++ tailWord_812790).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812790).length < 2 ^ (prefixWord ++ tailWord_812790).sum := by decide
  have hdescent : baseEnd_812790 < baseStart_812790 := by decide
  rcases family_descends (prefixWord ++ tailWord_812790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812807 : List Nat := [1, 1, 4, 4, 2, 1, 3, 1, 3]
def baseStart_812807 : Nat := 118140960795 + 812807 * 2 ^ 59
def prefixEnd_812807 : Nat := 4983230072969 + 3 ^ 40 * 812807 * 2
def baseEnd_812807 : Nat := 370987262523650331177311

theorem tailTrace_812807 : CollatzResearch.WordTrace tailWord_812807 prefixEnd_812807 370987262523650331177311 := by
  unfold tailWord_812807
  simp only [CollatzResearch.WordTrace]
  refine ⟨29645506766346530228972675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19763671177564353485981783 29645506766346530228972675)
  ·
    refine ⟨44468260149519795343459013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29645506766346530228972675 44468260149519795343459013)
    ·
      refine ⟨8337798778034961626898565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44468260149519795343459013 8337798778034961626898565)
      ·
        refine ⟨1563337270881555305043481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8337798778034961626898565 1563337270881555305043481)
        ·
          refine ⟨1172502953161166478782611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1563337270881555305043481 1172502953161166478782611)
          ·
            refine ⟨1758754429741749718173917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1172502953161166478782611 1758754429741749718173917)
            ·
              refine ⟨659532911153156144315219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1758754429741749718173917 659532911153156144315219)
              ·
                refine ⟨989299366729734216472829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 659532911153156144315219 989299366729734216472829)
                ·
                  refine ⟨370987262523650331177311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 989299366729734216472829 370987262523650331177311)
                  ·
                    rfl

theorem cell20_812807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 3, 1, 3].length) (baseStart_812807 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_812807 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_812807 prefixEnd_812807 := by exact prefixLift 812807
  have htrace : WordTrace (prefixWord ++ tailWord_812807) baseStart_812807 baseEnd_812807 := by
    simpa [prefixWord, tailWord_812807, baseEnd_812807] using wordTrace_append hprefix tailTrace_812807
  have hstable : (prefixWord ++ tailWord_812807).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812807).length < 2 ^ (prefixWord ++ tailWord_812807).sum := by decide
  have hdescent : baseEnd_812807 < baseStart_812807 := by decide
  rcases family_descends (prefixWord ++ tailWord_812807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812813 : List Nat := [1, 7, 2, 1, 2, 1, 2, 4]
def baseStart_812813 : Nat := 118140960795 + 812813 * 2 ^ 59
def prefixEnd_812813 : Nat := 4983230072969 + 3 ^ 40 * 812813 * 2
def baseEnd_812813 : Nat := 123663333695713658992429

theorem tailTrace_812813 : CollatzResearch.WordTrace tailWord_812813 prefixEnd_812813 123663333695713658992429 := by
  unfold tailWord_812813
  simp only [CollatzResearch.WordTrace]
  refine ⟨29645725604324793253691093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19763817069549862169127395 29645725604324793253691093)
  ·
    refine ⟨694821693851362341883385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 29645725604324793253691093 694821693851362341883385)
    ·
      refine ⟨521116270388521756412539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 694821693851362341883385 521116270388521756412539)
      ·
        refine ⟨781674405582782634618809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 521116270388521756412539 781674405582782634618809)
        ·
          refine ⟨586255804187086975964107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 781674405582782634618809 586255804187086975964107)
          ·
            refine ⟨879383706280630463946161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 586255804187086975964107 879383706280630463946161)
            ·
              refine ⟨659537779710472847959621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 879383706280630463946161 659537779710472847959621)
              ·
                refine ⟨123663333695713658992429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 659537779710472847959621 123663333695713658992429)
                ·
                  rfl

theorem cell20_812813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 2, 4].length) (baseStart_812813 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_812813 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_812813 prefixEnd_812813 := by exact prefixLift 812813
  have htrace : WordTrace (prefixWord ++ tailWord_812813) baseStart_812813 baseEnd_812813 := by
    simpa [prefixWord, tailWord_812813, baseEnd_812813] using wordTrace_append hprefix tailTrace_812813
  have hstable : (prefixWord ++ tailWord_812813).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812813).length < 2 ^ (prefixWord ++ tailWord_812813).sum := by decide
  have hdescent : baseEnd_812813 < baseStart_812813 := by decide
  rcases family_descends (prefixWord ++ tailWord_812813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812832 : List Nat := [2, 1, 1, 5, 1, 1, 1, 1, 7]
def baseStart_812832 : Nat := 118140960795 + 812832 * 2 ^ 59
def prefixEnd_812832 : Nat := 4983230072969 + 3 ^ 40 * 812832 * 2
def baseEnd_812832 : Nat := 370998673204861355343875

theorem tailTrace_812832 : CollatzResearch.WordTrace tailWord_812832 prefixEnd_812832 370998673204861355343875 := by
  unfold tailWord_812832
  simp only [CollatzResearch.WordTrace]
  refine ⟨14823209295627979749316375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19764279060837306332421833 14823209295627979749316375)
  ·
    refine ⟨22234813943441969623974563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14823209295627979749316375 22234813943441969623974563)
    ·
      refine ⟨33352220915162954435961845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22234813943441969623974563 33352220915162954435961845)
      ·
        refine ⟨3126770710796526978371423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33352220915162954435961845 3126770710796526978371423)
        ·
          refine ⟨4690156066194790467557135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3126770710796526978371423 4690156066194790467557135)
          ·
            refine ⟨7035234099292185701335703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4690156066194790467557135 7035234099292185701335703)
            ·
              refine ⟨10552851148938278552003555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7035234099292185701335703 10552851148938278552003555)
              ·
                refine ⟨15829276723407417828005333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10552851148938278552003555 15829276723407417828005333)
                ·
                  refine ⟨370998673204861355343875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15829276723407417828005333 370998673204861355343875)
                  ·
                    rfl

theorem cell20_812832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 7].length) (baseStart_812832 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_812832 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_812832 prefixEnd_812832 := by exact prefixLift 812832
  have htrace : WordTrace (prefixWord ++ tailWord_812832) baseStart_812832 baseEnd_812832 := by
    simpa [prefixWord, tailWord_812832, baseEnd_812832] using wordTrace_append hprefix tailTrace_812832
  have hstable : (prefixWord ++ tailWord_812832).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812832).length < 2 ^ (prefixWord ++ tailWord_812832).sum := by decide
  have hdescent : baseEnd_812832 < baseStart_812832 := by decide
  rcases family_descends (prefixWord ++ tailWord_812832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812835 : List Nat := [1, 1, 1, 4, 2, 1, 5, 3, 2]
def baseStart_812835 : Nat := 118140960795 + 812835 * 2 ^ 59
def prefixEnd_812835 : Nat := 4983230072969 + 3 ^ 40 * 812835 * 2
def baseEnd_812835 : Nat := 371000042486606678243863

theorem tailTrace_812835 : CollatzResearch.WordTrace tailWord_812835 prefixEnd_812835 371000042486606678243863 := by
  unfold tailWord_812835
  simp only [CollatzResearch.WordTrace]
  refine ⟨29646528010245091010991959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19764352006830060673994639 29646528010245091010991959)
  ·
    refine ⟨44469792015367636516487939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29646528010245091010991959 44469792015367636516487939)
    ·
      refine ⟨66704688023051454774731909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44469792015367636516487939 66704688023051454774731909)
      ·
        refine ⟨12507129004322147770262233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66704688023051454774731909 12507129004322147770262233)
        ·
          refine ⟨9380346753241610827696675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12507129004322147770262233 9380346753241610827696675)
          ·
            refine ⟨14070520129862416241545013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9380346753241610827696675 14070520129862416241545013)
            ·
              refine ⟨1319111262174601522644845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14070520129862416241545013 1319111262174601522644845)
              ·
                refine ⟨494666723315475570991817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1319111262174601522644845 494666723315475570991817)
                ·
                  refine ⟨371000042486606678243863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 494666723315475570991817 371000042486606678243863)
                  ·
                    rfl

theorem cell20_812835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 3, 2].length) (baseStart_812835 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_812835 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_812835 prefixEnd_812835 := by exact prefixLift 812835
  have htrace : WordTrace (prefixWord ++ tailWord_812835) baseStart_812835 baseEnd_812835 := by
    simpa [prefixWord, tailWord_812835, baseEnd_812835] using wordTrace_append hprefix tailTrace_812835
  have hstable : (prefixWord ++ tailWord_812835).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812835).length < 2 ^ (prefixWord ++ tailWord_812835).sum := by decide
  have hdescent : baseEnd_812835 < baseStart_812835 := by decide
  rcases family_descends (prefixWord ++ tailWord_812835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812852 : List Nat := [2, 5, 1, 1, 2, 3, 1, 1, 4]
def baseStart_812852 : Nat := 118140960795 + 812852 * 2 ^ 59
def prefixEnd_812852 : Nat := 4983230072969 + 3 ^ 40 * 812852 * 2
def baseEnd_812852 : Nat := 371007801749830174677127

theorem tailTrace_812852 : CollatzResearch.WordTrace tailWord_812852 prefixEnd_812852 371007801749830174677127 := by
  unfold tailWord_812852
  simp only [CollatzResearch.WordTrace]
  refine ⟨14823574025591751457180405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19764765367455668609573873 14823574025591751457180405)
  ·
    refine ⟨1389710064899226699110663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14823574025591751457180405 1389710064899226699110663)
    ·
      refine ⟨2084565097348840048665995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1389710064899226699110663 2084565097348840048665995)
      ·
        refine ⟨3126847646023260072998993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2084565097348840048665995 3126847646023260072998993)
        ·
          refine ⟨2345135734517445054749245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3126847646023260072998993 2345135734517445054749245)
          ·
            refine ⟨879425900444041895530967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2345135734517445054749245 879425900444041895530967)
            ·
              refine ⟨1319138850666062843296451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 879425900444041895530967 1319138850666062843296451)
              ·
                refine ⟨1978708275999094264944677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1319138850666062843296451 1978708275999094264944677)
                ·
                  refine ⟨371007801749830174677127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1978708275999094264944677 371007801749830174677127)
                  ·
                    rfl

theorem cell20_812852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_812852 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_812852 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_812852 prefixEnd_812852 := by exact prefixLift 812852
  have htrace : WordTrace (prefixWord ++ tailWord_812852) baseStart_812852 baseEnd_812852 := by
    simpa [prefixWord, tailWord_812852, baseEnd_812852] using wordTrace_append hprefix tailTrace_812852
  have hstable : (prefixWord ++ tailWord_812852).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812852).length < 2 ^ (prefixWord ++ tailWord_812852).sum := by decide
  have hdescent : baseEnd_812852 < baseStart_812852 := by decide
  rcases family_descends (prefixWord ++ tailWord_812852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812856 : List Nat := [2, 1, 2, 1, 3, 3, 3, 1, 4]
def baseStart_812856 : Nat := 118140960795 + 812856 * 2 ^ 59
def prefixEnd_812856 : Nat := 4983230072969 + 3 ^ 40 * 812856 * 2
def baseEnd_812856 : Nat := 371009627458823938543777

theorem tailTrace_812856 : CollatzResearch.WordTrace tailWord_812856 prefixEnd_812856 371009627458823938543777 := by
  unfold tailWord_812856
  simp only [CollatzResearch.WordTrace]
  refine ⟨14823646971584505798753211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19764862628779341065004281 14823646971584505798753211)
  ·
    refine ⟨22235470457376758698129817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14823646971584505798753211 22235470457376758698129817)
    ·
      refine ⟨16676602843032569023597363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22235470457376758698129817 16676602843032569023597363)
      ·
        refine ⟨25014904264548853535396045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16676602843032569023597363 25014904264548853535396045)
        ·
          refine ⟨9380589099205820075773517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25014904264548853535396045 9380589099205820075773517)
          ·
            refine ⟨3517720912202182528415069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9380589099205820075773517 3517720912202182528415069)
            ·
              refine ⟨1319145342075818448155651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3517720912202182528415069 1319145342075818448155651)
              ·
                refine ⟨1978718013113727672233477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1319145342075818448155651 1978718013113727672233477)
                ·
                  refine ⟨371009627458823938543777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1978718013113727672233477 371009627458823938543777)
                  ·
                    rfl

theorem cell20_812856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 1, 4].length) (baseStart_812856 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_812856 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_812856 prefixEnd_812856 := by exact prefixLift 812856
  have htrace : WordTrace (prefixWord ++ tailWord_812856) baseStart_812856 baseEnd_812856 := by
    simpa [prefixWord, tailWord_812856, baseEnd_812856] using wordTrace_append hprefix tailTrace_812856
  have hstable : (prefixWord ++ tailWord_812856).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812856).length < 2 ^ (prefixWord ++ tailWord_812856).sum := by decide
  have hdescent : baseEnd_812856 < baseStart_812856 := by decide
  rcases family_descends (prefixWord ++ tailWord_812856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812915 : List Nat := [1, 1, 1, 2, 2, 1, 3, 5, 4]
def baseStart_812915 : Nat := 118140960795 + 812915 * 2 ^ 59
def prefixEnd_812915 : Nat := 4983230072969 + 3 ^ 40 * 812915 * 2
def baseEnd_812915 : Nat := 371036556666481955576869

theorem tailTrace_812915 : CollatzResearch.WordTrace tailWord_812915 prefixEnd_812915 371036556666481955576869 := by
  unfold tailWord_812915
  simp only [CollatzResearch.WordTrace]
  refine ⟨29649445849955264673904199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19766297233303509782602799 29649445849955264673904199)
  ·
    refine ⟨44474168774932897010856299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29649445849955264673904199 44474168774932897010856299)
    ·
      refine ⟨66711253162399345516284449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44474168774932897010856299 66711253162399345516284449)
      ·
        refine ⟨50033439871799509137213337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66711253162399345516284449 50033439871799509137213337)
        ·
          refine ⟨37525079903849631852910003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50033439871799509137213337 37525079903849631852910003)
          ·
            refine ⟨56287619855774447779365005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37525079903849631852910003 56287619855774447779365005)
            ·
              refine ⟨21107857445915417917261877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56287619855774447779365005 21107857445915417917261877)
              ·
                refine ⟨1978861635554570429743301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21107857445915417917261877 1978861635554570429743301)
                ·
                  refine ⟨371036556666481955576869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1978861635554570429743301 371036556666481955576869)
                  ·
                    rfl

theorem cell20_812915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 5, 4].length) (baseStart_812915 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_812915 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_812915 prefixEnd_812915 := by exact prefixLift 812915
  have htrace : WordTrace (prefixWord ++ tailWord_812915) baseStart_812915 baseEnd_812915 := by
    simpa [prefixWord, tailWord_812915, baseEnd_812915] using wordTrace_append hprefix tailTrace_812915
  have hstable : (prefixWord ++ tailWord_812915).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812915).length < 2 ^ (prefixWord ++ tailWord_812915).sum := by decide
  have hdescent : baseEnd_812915 < baseStart_812915 := by decide
  rcases family_descends (prefixWord ++ tailWord_812915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812949 : List Nat := [1, 3, 2, 1, 1, 3, 4, 3, 2]
def baseStart_812949 : Nat := 118140960795 + 812949 * 2 ^ 59
def prefixEnd_812949 : Nat := 4983230072969 + 3 ^ 40 * 812949 * 2
def baseEnd_812949 : Nat := 371052075192928948443397

theorem tailTrace_812949 : CollatzResearch.WordTrace tailWord_812949 prefixEnd_812949 371052075192928948443397 := by
  unfold tailWord_812949
  simp only [CollatzResearch.WordTrace]
  refine ⟨29650685931832088480641901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19767123954554725653761267 29650685931832088480641901)
  ·
    refine ⟨11119007224437033180240713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29650685931832088480641901 11119007224437033180240713)
    ·
      refine ⟨8339255418327774885180535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11119007224437033180240713 8339255418327774885180535)
      ·
        refine ⟨12508883127491662327770803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8339255418327774885180535 12508883127491662327770803)
        ·
          refine ⟨18763324691237493491656205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12508883127491662327770803 18763324691237493491656205)
          ·
            refine ⟨7036246759214060059371077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18763324691237493491656205 7036246759214060059371077)
            ·
              refine ⟨1319296267352636261132077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7036246759214060059371077 1319296267352636261132077)
              ·
                refine ⟨494736100257238597924529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1319296267352636261132077 494736100257238597924529)
                ·
                  refine ⟨371052075192928948443397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 494736100257238597924529 371052075192928948443397)
                  ·
                    rfl

theorem cell20_812949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 3, 2].length) (baseStart_812949 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_812949 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_812949 prefixEnd_812949 := by exact prefixLift 812949
  have htrace : WordTrace (prefixWord ++ tailWord_812949) baseStart_812949 baseEnd_812949 := by
    simpa [prefixWord, tailWord_812949, baseEnd_812949] using wordTrace_append hprefix tailTrace_812949
  have hstable : (prefixWord ++ tailWord_812949).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812949).length < 2 ^ (prefixWord ++ tailWord_812949).sum := by decide
  have hdescent : baseEnd_812949 < baseStart_812949 := by decide
  rcases family_descends (prefixWord ++ tailWord_812949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812959 : List Nat := [1, 1, 2, 5, 4, 1, 1, 2, 3]
def baseStart_812959 : Nat := 118140960795 + 812959 * 2 ^ 59
def prefixEnd_812959 : Nat := 4983230072969 + 3 ^ 40 * 812959 * 2
def baseEnd_812959 : Nat := 371056639465413358110023

theorem tailTrace_812959 : CollatzResearch.WordTrace tailWord_812959 prefixEnd_812959 371056639465413358110023 := by
  unfold tailWord_812959
  simp only [CollatzResearch.WordTrace]
  refine ⟨29651050661795860188505931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19767367107863906792337287 29651050661795860188505931)
  ·
    refine ⟨44476575992693790282758897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29651050661795860188505931 44476575992693790282758897)
    ·
      refine ⟨33357431994520342712069173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44476575992693790282758897 33357431994520342712069173)
      ·
        refine ⟨3127259249486282129256485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33357431994520342712069173 3127259249486282129256485)
        ·
          refine ⟨586361109278677899235591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3127259249486282129256485 586361109278677899235591)
          ·
            refine ⟨879541663918016848853387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 586361109278677899235591 879541663918016848853387)
            ·
              refine ⟨1319312495877025273280081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 879541663918016848853387 1319312495877025273280081)
              ·
                refine ⟨989484371907768954960061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1319312495877025273280081 989484371907768954960061)
                ·
                  refine ⟨371056639465413358110023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 989484371907768954960061 371056639465413358110023)
                  ·
                    rfl

theorem cell20_812959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 2, 3].length) (baseStart_812959 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_812959 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_812959 prefixEnd_812959 := by exact prefixLift 812959
  have htrace : WordTrace (prefixWord ++ tailWord_812959) baseStart_812959 baseEnd_812959 := by
    simpa [prefixWord, tailWord_812959, baseEnd_812959] using wordTrace_append hprefix tailTrace_812959
  have hstable : (prefixWord ++ tailWord_812959).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812959).length < 2 ^ (prefixWord ++ tailWord_812959).sum := by decide
  have hdescent : baseEnd_812959 < baseStart_812959 := by decide
  rcases family_descends (prefixWord ++ tailWord_812959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812991 : List Nat := [1, 1, 2, 2, 2, 1, 3, 4, 4]
def baseStart_812991 : Nat := 118140960795 + 812991 * 2 ^ 59
def prefixEnd_812991 : Nat := 4983230072969 + 3 ^ 40 * 812991 * 2
def baseEnd_812991 : Nat := 371071245137363469043225

theorem tailTrace_812991 : CollatzResearch.WordTrace tailWord_812991 prefixEnd_812991 371071245137363469043225 := by
  unfold tailWord_812991
  simp only [CollatzResearch.WordTrace]
  refine ⟨29652217797679929653670827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19768145198453286435780551 29652217797679929653670827)
  ·
    refine ⟨44478326696519894480506241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29652217797679929653670827 44478326696519894480506241)
    ·
      refine ⟨33358745022389920860379681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44478326696519894480506241 33358745022389920860379681)
      ·
        refine ⟨25019058766792440645284761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33358745022389920860379681 25019058766792440645284761)
        ·
          refine ⟨18764294075094330483963571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25019058766792440645284761 18764294075094330483963571)
          ·
            refine ⟨28146441112641495725945357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18764294075094330483963571 28146441112641495725945357)
            ·
              refine ⟨10554915417240560897229509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28146441112641495725945357 10554915417240560897229509)
              ·
                refine ⟨1979046640732605168230533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10554915417240560897229509 1979046640732605168230533)
                ·
                  refine ⟨371071245137363469043225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1979046640732605168230533 371071245137363469043225)
                  ·
                    rfl

theorem cell20_812991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 4, 4].length) (baseStart_812991 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_812991 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_812991 prefixEnd_812991 := by exact prefixLift 812991
  have htrace : WordTrace (prefixWord ++ tailWord_812991) baseStart_812991 baseEnd_812991 := by
    simpa [prefixWord, tailWord_812991, baseEnd_812991] using wordTrace_append hprefix tailTrace_812991
  have hstable : (prefixWord ++ tailWord_812991).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812991).length < 2 ^ (prefixWord ++ tailWord_812991).sum := by decide
  have hdescent : baseEnd_812991 < baseStart_812991 := by decide
  rcases family_descends (prefixWord ++ tailWord_812991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813004 : List Nat := [2, 2, 1, 4, 1, 4, 1, 3, 2]
def baseStart_813004 : Nat := 118140960795 + 813004 * 2 ^ 59
def prefixEnd_813004 : Nat := 4983230072969 + 3 ^ 40 * 813004 * 2
def baseEnd_813004 : Nat := 371077178691593201609839

theorem tailTrace_813004 : CollatzResearch.WordTrace tailWord_813004 prefixEnd_813004 371077178691593201609839 := by
  unfold tailWord_813004
  simp only [CollatzResearch.WordTrace]
  refine ⟨14826345973316416436947033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19768461297755221915929377 14826345973316416436947033)
  ·
    refine ⟨11119759479987312327710275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14826345973316416436947033 11119759479987312327710275)
    ·
      refine ⟨16679639219980968491565413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11119759479987312327710275 16679639219980968491565413)
      ·
        refine ⟨3127432353746431592168515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16679639219980968491565413 3127432353746431592168515)
        ·
          refine ⟨4691148530619647388252773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3127432353746431592168515 4691148530619647388252773)
          ·
            refine ⟨879590349491183885297395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4691148530619647388252773 879590349491183885297395)
            ·
              refine ⟨1319385524236775827946093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 879590349491183885297395 1319385524236775827946093)
              ·
                refine ⟨494769571588790935479785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1319385524236775827946093 494769571588790935479785)
                ·
                  refine ⟨371077178691593201609839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 494769571588790935479785 371077178691593201609839)
                  ·
                    rfl

theorem cell20_813004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 3, 2].length) (baseStart_813004 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_813004 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_813004 prefixEnd_813004 := by exact prefixLift 813004
  have htrace : WordTrace (prefixWord ++ tailWord_813004) baseStart_813004 baseEnd_813004 := by
    simpa [prefixWord, tailWord_813004, baseEnd_813004] using wordTrace_append hprefix tailTrace_813004
  have hstable : (prefixWord ++ tailWord_813004).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813004).length < 2 ^ (prefixWord ++ tailWord_813004).sum := by decide
  have hdescent : baseEnd_813004 < baseStart_813004 := by decide
  rcases family_descends (prefixWord ++ tailWord_813004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813021 : List Nat := [1, 4, 3, 1, 3, 1, 3, 2, 2]
def baseStart_813021 : Nat := 118140960795 + 813021 * 2 ^ 59
def prefixEnd_813021 : Nat := 4983230072969 + 3 ^ 40 * 813021 * 2
def baseEnd_813021 : Nat := 371084937954816698043103

theorem tailTrace_813021 : CollatzResearch.WordTrace tailWord_813021 prefixEnd_813021 371084937954816698043103 := by
  unfold tailWord_813021
  simp only [CollatzResearch.WordTrace]
  refine ⟨29653311987571244777262917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19768874658380829851508611 29653311987571244777262917)
  ·
    refine ⟨5559995997669608395736797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29653311987571244777262917 5559995997669608395736797)
    ·
      refine ⟨2084998499126103148401299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5559995997669608395736797 2084998499126103148401299)
      ·
        refine ⟨3127497748689154722601949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2084998499126103148401299 3127497748689154722601949)
        ·
          refine ⟨1172811655758433020975731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3127497748689154722601949 1172811655758433020975731)
          ·
            refine ⟨1759217483637649531463597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1172811655758433020975731 1759217483637649531463597)
            ·
              refine ⟨659706556364118574298849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1759217483637649531463597 659706556364118574298849)
              ·
                refine ⟨494779917273088930724137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 659706556364118574298849 494779917273088930724137)
                ·
                  refine ⟨371084937954816698043103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 494779917273088930724137 371084937954816698043103)
                  ·
                    rfl

theorem cell20_813021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 3, 2, 2].length) (baseStart_813021 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_813021 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_813021 prefixEnd_813021 := by exact prefixLift 813021
  have htrace : WordTrace (prefixWord ++ tailWord_813021) baseStart_813021 baseEnd_813021 := by
    simpa [prefixWord, tailWord_813021, baseEnd_813021] using wordTrace_append hprefix tailTrace_813021
  have hstable : (prefixWord ++ tailWord_813021).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813021).length < 2 ^ (prefixWord ++ tailWord_813021).sum := by decide
  have hdescent : baseEnd_813021 < baseStart_813021 := by decide
  rcases family_descends (prefixWord ++ tailWord_813021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813105 : List Nat := [1, 2, 2, 3, 1, 3, 1, 1, 6]
def baseStart_813105 : Nat := 118140960795 + 813105 * 2 ^ 59
def prefixEnd_813105 : Nat := 4983230072969 + 3 ^ 40 * 813105 * 2
def baseEnd_813105 : Nat := 371123277843685739242759

theorem tailTrace_813105 : CollatzResearch.WordTrace tailWord_813105 prefixEnd_813105 371123277843685739242759 := by
  unfold tailWord_813105
  simp only [CollatzResearch.WordTrace]
  refine ⟨29656375719266927123320769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19770917146177951415547179 29656375719266927123320769)
  ·
    refine ⟨22242281789450195342490577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29656375719266927123320769 22242281789450195342490577)
    ·
      refine ⟨16681711342087646506867933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22242281789450195342490577 16681711342087646506867933)
      ·
        refine ⟨6255641753282867440075475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16681711342087646506867933 6255641753282867440075475)
        ·
          refine ⟨9383462629924301160113213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6255641753282867440075475 9383462629924301160113213)
          ·
            refine ⟨3518798486221612935042455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9383462629924301160113213 3518798486221612935042455)
            ·
              refine ⟨5278197729332419402563683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3518798486221612935042455 5278197729332419402563683)
              ·
                refine ⟨7917296593998629103845525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5278197729332419402563683 7917296593998629103845525)
                ·
                  refine ⟨371123277843685739242759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7917296593998629103845525 371123277843685739242759)
                  ·
                    rfl

theorem cell20_813105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 6].length) (baseStart_813105 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_813105 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_813105 prefixEnd_813105 := by exact prefixLift 813105
  have htrace : WordTrace (prefixWord ++ tailWord_813105) baseStart_813105 baseEnd_813105 := by
    simpa [prefixWord, tailWord_813105, baseEnd_813105] using wordTrace_append hprefix tailTrace_813105
  have hstable : (prefixWord ++ tailWord_813105).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813105).length < 2 ^ (prefixWord ++ tailWord_813105).sum := by decide
  have hdescent : baseEnd_813105 < baseStart_813105 := by decide
  rcases family_descends (prefixWord ++ tailWord_813105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813143 : List Nat := [1, 1, 3, 2, 2, 1, 3, 3, 4]
def baseStart_813143 : Nat := 118140960795 + 813143 * 2 ^ 59
def prefixEnd_813143 : Nat := 4983230072969 + 3 ^ 40 * 813143 * 2
def baseEnd_813143 : Nat := 371140622079126495975937

theorem tailTrace_813143 : CollatzResearch.WordTrace tailWord_813143 prefixEnd_813143 371140622079126495975937 := by
  unfold tailWord_813143
  simp only [CollatzResearch.WordTrace]
  refine ⟨29657761693129259613204083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19771841128752839742136055 29657761693129259613204083)
  ·
    refine ⟨44486642539693889419806125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29657761693129259613204083 44486642539693889419806125)
    ·
      refine ⟨16682490952385208532427297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44486642539693889419806125 16682490952385208532427297)
      ·
        refine ⟨12511868214288906399320473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16682490952385208532427297 12511868214288906399320473)
        ·
          refine ⟨9383901160716679799490355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12511868214288906399320473 9383901160716679799490355)
          ·
            refine ⟨14075851741075019699235533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9383901160716679799490355 14075851741075019699235533)
            ·
              refine ⟨5278444402903132387213325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14075851741075019699235533 5278444402903132387213325)
              ·
                refine ⟨1979416651088674645204997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5278444402903132387213325 1979416651088674645204997)
                ·
                  refine ⟨371140622079126495975937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1979416651088674645204997 371140622079126495975937)
                  ·
                    rfl

theorem cell20_813143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 3, 4].length) (baseStart_813143 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_813143 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_813143 prefixEnd_813143 := by exact prefixLift 813143
  have htrace : WordTrace (prefixWord ++ tailWord_813143) baseStart_813143 baseEnd_813143 := by
    simpa [prefixWord, tailWord_813143, baseEnd_813143] using wordTrace_append hprefix tailTrace_813143
  have hstable : (prefixWord ++ tailWord_813143).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813143).length < 2 ^ (prefixWord ++ tailWord_813143).sum := by decide
  have hdescent : baseEnd_813143 < baseStart_813143 := by decide
  rcases family_descends (prefixWord ++ tailWord_813143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813149 : List Nat := [1, 4, 4, 1, 1, 2, 3, 1, 3]
def baseStart_813149 : Nat := 118140960795 + 813149 * 2 ^ 59
def prefixEnd_813149 : Nat := 4983230072969 + 3 ^ 40 * 813149 * 2
def baseEnd_813149 : Nat := 371143360642617141775913

theorem tailTrace_813149 : CollatzResearch.WordTrace tailWord_813149 prefixEnd_813149 371143360642617141775913 := by
  unfold tailWord_813149
  simp only [CollatzResearch.WordTrace]
  refine ⟨29657980531107522637922501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19771987020738348425281667 29657980531107522637922501)
  ·
    refine ⟨5560871349582660494610469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29657980531107522637922501 5560871349582660494610469)
    ·
      refine ⟨1042663378046748842739463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5560871349582660494610469 1042663378046748842739463)
      ·
        refine ⟨1563995067070123264109195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1042663378046748842739463 1563995067070123264109195)
        ·
          refine ⟨2345992600605184896163793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1563995067070123264109195 2345992600605184896163793)
          ·
            refine ⟨1759494450453888672122845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2345992600605184896163793 1759494450453888672122845)
            ·
              refine ⟨659810418920208252046067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1759494450453888672122845 659810418920208252046067)
              ·
                refine ⟨989715628380312378069101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 659810418920208252046067 989715628380312378069101)
                ·
                  refine ⟨371143360642617141775913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 989715628380312378069101 371143360642617141775913)
                  ·
                    rfl

theorem cell20_813149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 3, 1, 3].length) (baseStart_813149 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_813149 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_813149 prefixEnd_813149 := by exact prefixLift 813149
  have htrace : WordTrace (prefixWord ++ tailWord_813149) baseStart_813149 baseEnd_813149 := by
    simpa [prefixWord, tailWord_813149, baseEnd_813149] using wordTrace_append hprefix tailTrace_813149
  have hstable : (prefixWord ++ tailWord_813149).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813149).length < 2 ^ (prefixWord ++ tailWord_813149).sum := by decide
  have hdescent : baseEnd_813149 < baseStart_813149 := by decide
  rcases family_descends (prefixWord ++ tailWord_813149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813167 : List Nat := [1, 1, 2, 1, 3, 4, 4, 4]
def baseStart_813167 : Nat := 118140960795 + 813167 * 2 ^ 59
def prefixEnd_813167 : Nat := 4983230072969 + 3 ^ 40 * 813167 * 2
def baseEnd_813167 : Nat := 123717192111029693058613

theorem tailTrace_813167 : CollatzResearch.WordTrace tailWord_813167 prefixEnd_813167 123717192111029693058613 := by
  unfold tailWord_813167
  simp only [CollatzResearch.WordTrace]
  refine ⟨29658637045042311712077755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19772424696694874474718503 29658637045042311712077755)
  ·
    refine ⟨44487955567563467568116633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29658637045042311712077755 44487955567563467568116633)
    ·
      refine ⟨33365966675672600676087475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44487955567563467568116633 33365966675672600676087475)
      ·
        refine ⟨50048950013508901014131213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33365966675672600676087475 50048950013508901014131213)
        ·
          refine ⟨18768356255065837880299205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50048950013508901014131213 18768356255065837880299205)
          ·
            refine ⟨3519066797824844602556101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18768356255065837880299205 3519066797824844602556101)
            ·
              refine ⟨659825024592158362979269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3519066797824844602556101 659825024592158362979269)
              ·
                refine ⟨123717192111029693058613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 659825024592158362979269 123717192111029693058613)
                ·
                  rfl

theorem cell20_813167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 4, 4].length) (baseStart_813167 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_813167 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_813167 prefixEnd_813167 := by exact prefixLift 813167
  have htrace : WordTrace (prefixWord ++ tailWord_813167) baseStart_813167 baseEnd_813167 := by
    simpa [prefixWord, tailWord_813167, baseEnd_813167] using wordTrace_append hprefix tailTrace_813167
  have hstable : (prefixWord ++ tailWord_813167).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813167).length < 2 ^ (prefixWord ++ tailWord_813167).sum := by decide
  have hdescent : baseEnd_813167 < baseStart_813167 := by decide
  rcases family_descends (prefixWord ++ tailWord_813167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813177 : List Nat := [1, 2, 1, 3, 4, 1, 3, 3, 2]
def baseStart_813177 : Nat := 118140960795 + 813177 * 2 ^ 59
def prefixEnd_813177 : Nat := 4983230072969 + 3 ^ 40 * 813177 * 2
def baseEnd_813177 : Nat := 371156140605573488842465

theorem tailTrace_813177 : CollatzResearch.WordTrace tailWord_813177 prefixEnd_813177 371156140605573488842465 := by
  unfold tailWord_813177
  simp only [CollatzResearch.WordTrace]
  refine ⟨29659001775006083419941785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19772667850004055613294523 29659001775006083419941785)
  ·
    refine ⟨22244251331254562564956339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29659001775006083419941785 22244251331254562564956339)
    ·
      refine ⟨33366376996881843847434509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22244251331254562564956339 33366376996881843847434509)
      ·
        refine ⟨12512391373830691442787941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33366376996881843847434509 12512391373830691442787941)
        ·
          refine ⟨2346073382593254645522739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12512391373830691442787941 2346073382593254645522739)
          ·
            refine ⟨3519110073889881968284109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2346073382593254645522739 3519110073889881968284109)
            ·
              refine ⟨1319666277708705738106541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3519110073889881968284109 1319666277708705738106541)
              ·
                refine ⟨494874854140764651789953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1319666277708705738106541 494874854140764651789953)
                ·
                  refine ⟨371156140605573488842465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 494874854140764651789953 371156140605573488842465)
                  ·
                    rfl

theorem cell20_813177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 3, 2].length) (baseStart_813177 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_813177 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_813177 prefixEnd_813177 := by exact prefixLift 813177
  have htrace : WordTrace (prefixWord ++ tailWord_813177) baseStart_813177 baseEnd_813177 := by
    simpa [prefixWord, tailWord_813177, baseEnd_813177] using wordTrace_append hprefix tailTrace_813177
  have hstable : (prefixWord ++ tailWord_813177).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813177).length < 2 ^ (prefixWord ++ tailWord_813177).sum := by decide
  have hdescent : baseEnd_813177 < baseStart_813177 := by decide
  rcases family_descends (prefixWord ++ tailWord_813177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813194 : List Nat := [3, 1, 2, 3, 1, 3, 3, 2, 2]
def baseStart_813194 : Nat := 118140960795 + 813194 * 2 ^ 59
def prefixEnd_813194 : Nat := 4983230072969 + 3 ^ 40 * 813194 * 2
def baseEnd_813194 : Nat := 371163899868796985275729

theorem tailTrace_813194 : CollatzResearch.WordTrace tailWord_813194 prefixEnd_813194 371163899868796985275729 := by
  unfold tailWord_813194
  simp only [CollatzResearch.WordTrace]
  refine ⟨7414905453986123830827659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19773081210629663548873757 7414905453986123830827659)
  ·
    refine ⟨11122358180979185746241489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7414905453986123830827659 11122358180979185746241489)
    ·
      refine ⟨8341768635734389309681117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11122358180979185746241489 8341768635734389309681117)
      ·
        refine ⟨3128163238400395991130419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8341768635734389309681117 3128163238400395991130419)
        ·
          refine ⟨4692244857600593986695629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3128163238400395991130419 4692244857600593986695629)
          ·
            refine ⟨1759591821600222745010861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4692244857600593986695629 1759591821600222745010861)
            ·
              refine ⟨659846933100083529379073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1759591821600222745010861 659846933100083529379073)
              ·
                refine ⟨494885199825062647034305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 659846933100083529379073 494885199825062647034305)
                ·
                  refine ⟨371163899868796985275729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 494885199825062647034305 371163899868796985275729)
                  ·
                    rfl

theorem cell20_813194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 3, 2, 2].length) (baseStart_813194 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_813194 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_813194 prefixEnd_813194 := by exact prefixLift 813194
  have htrace : WordTrace (prefixWord ++ tailWord_813194) baseStart_813194 baseEnd_813194 := by
    simpa [prefixWord, tailWord_813194, baseEnd_813194] using wordTrace_append hprefix tailTrace_813194
  have hstable : (prefixWord ++ tailWord_813194).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813194).length < 2 ^ (prefixWord ++ tailWord_813194).sum := by decide
  have hdescent : baseEnd_813194 < baseStart_813194 := by decide
  rcases family_descends (prefixWord ++ tailWord_813194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813204 : List Nat := [2, 4, 2, 3, 1, 2, 2, 1, 3]
def baseStart_813204 : Nat := 118140960795 + 813204 * 2 ^ 59
def prefixEnd_813204 : Nat := 4983230072969 + 3 ^ 40 * 813204 * 2
def baseEnd_813204 : Nat := 371168464141281394942355

theorem tailTrace_813204 : CollatzResearch.WordTrace tailWord_813204 prefixEnd_813204 371168464141281394942355 := by
  unfold tailWord_813204
  simp only [CollatzResearch.WordTrace]
  refine ⟨14829993272954133515587333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19773324363938844687449777 14829993272954133515587333)
  ·
    refine ⟨2780623738678900034172625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14829993272954133515587333 2780623738678900034172625)
    ·
      refine ⟨2085467804009175025629469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2780623738678900034172625 2085467804009175025629469)
      ·
        refine ⟨782050426503440634611051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2085467804009175025629469 782050426503440634611051)
        ·
          refine ⟨1173075639755160951916577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 782050426503440634611051 1173075639755160951916577)
          ·
            refine ⟨879806729816370713937433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1173075639755160951916577 879806729816370713937433)
            ·
              refine ⟨659855047362278035453075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 879806729816370713937433 659855047362278035453075)
              ·
                refine ⟨989782571043417053179613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 659855047362278035453075 989782571043417053179613)
                ·
                  refine ⟨371168464141281394942355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 989782571043417053179613 371168464141281394942355)
                  ·
                    rfl

theorem cell20_813204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 2, 1, 3].length) (baseStart_813204 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_813204 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_813204 prefixEnd_813204 := by exact prefixLift 813204
  have htrace : WordTrace (prefixWord ++ tailWord_813204) baseStart_813204 baseEnd_813204 := by
    simpa [prefixWord, tailWord_813204, baseEnd_813204] using wordTrace_append hprefix tailTrace_813204
  have hstable : (prefixWord ++ tailWord_813204).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813204).length < 2 ^ (prefixWord ++ tailWord_813204).sum := by decide
  have hdescent : baseEnd_813204 < baseStart_813204 := by decide
  rcases family_descends (prefixWord ++ tailWord_813204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813246 : List Nat := [4, 2, 1, 1, 4, 1, 2, 2, 3]
def baseStart_813246 : Nat := 118140960795 + 813246 * 2 ^ 59
def prefixEnd_813246 : Nat := 4983230072969 + 3 ^ 40 * 813246 * 2
def baseEnd_813246 : Nat := 371187634085715915542183

theorem tailTrace_813246 : CollatzResearch.WordTrace tailWord_813246 prefixEnd_813246 371187634085715915542183 := by
  unfold tailWord_813246
  simp only [CollatzResearch.WordTrace]
  refine ⟨3707689801469513525525449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19774345607837405469469061 3707689801469513525525449)
  ·
    refine ⟨2780767351102135144144087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3707689801469513525525449 2780767351102135144144087)
    ·
      refine ⟨4171151026653202716216131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2780767351102135144144087 4171151026653202716216131)
      ·
        refine ⟨6256726539979804074324197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4171151026653202716216131 6256726539979804074324197)
        ·
          refine ⟨1173136226246213263935787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6256726539979804074324197 1173136226246213263935787)
          ·
            refine ⟨1759704339369319895903681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1173136226246213263935787 1759704339369319895903681)
            ·
              refine ⟨1319778254526989921927761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1759704339369319895903681 1319778254526989921927761)
              ·
                refine ⟨989833690895242441445821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1319778254526989921927761 989833690895242441445821)
                ·
                  refine ⟨371187634085715915542183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 989833690895242441445821 371187634085715915542183)
                  ·
                    rfl

theorem cell20_813246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_813246 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_813246 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_813246 prefixEnd_813246 := by exact prefixLift 813246
  have htrace : WordTrace (prefixWord ++ tailWord_813246) baseStart_813246 baseEnd_813246 := by
    simpa [prefixWord, tailWord_813246, baseEnd_813246] using wordTrace_append hprefix tailTrace_813246
  have hstable : (prefixWord ++ tailWord_813246).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813246).length < 2 ^ (prefixWord ++ tailWord_813246).sum := by decide
  have hdescent : baseEnd_813246 < baseStart_813246 := by decide
  rcases family_descends (prefixWord ++ tailWord_813246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813253 : List Nat := [1, 3, 1, 1, 1, 1, 8, 2, 2]
def baseStart_813253 : Nat := 118140960795 + 813253 * 2 ^ 59
def prefixEnd_813253 : Nat := 4983230072969 + 3 ^ 40 * 813253 * 2
def baseEnd_813253 : Nat := 371190829076455002308821

theorem tailTrace_813253 : CollatzResearch.WordTrace tailWord_813253 prefixEnd_813253 371190829076455002308821 := by
  unfold tailWord_813253
  simp only [CollatzResearch.WordTrace]
  refine ⟨29661773722730748399708413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19774515815153832266472275 29661773722730748399708413)
  ·
    refine ⟨11123165146024030649890655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29661773722730748399708413 11123165146024030649890655)
    ·
      refine ⟨16684747719036045974835983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11123165146024030649890655 16684747719036045974835983)
      ·
        refine ⟨25027121578554068962253975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16684747719036045974835983 25027121578554068962253975)
        ·
          refine ⟨37540682367831103443380963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25027121578554068962253975 37540682367831103443380963)
          ·
            refine ⟨56311023551746655165071445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37540682367831103443380963 56311023551746655165071445)
            ·
              refine ⟨659894807247031115215681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 56311023551746655165071445 659894807247031115215681)
              ·
                refine ⟨494921105435273336411761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 659894807247031115215681 494921105435273336411761)
                ·
                  refine ⟨371190829076455002308821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 494921105435273336411761 371190829076455002308821)
                  ·
                    rfl

theorem cell20_813253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 8, 2, 2].length) (baseStart_813253 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_813253 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_813253 prefixEnd_813253 := by exact prefixLift 813253
  have htrace : WordTrace (prefixWord ++ tailWord_813253) baseStart_813253 baseEnd_813253 := by
    simpa [prefixWord, tailWord_813253, baseEnd_813253] using wordTrace_append hprefix tailTrace_813253
  have hstable : (prefixWord ++ tailWord_813253).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813253).length < 2 ^ (prefixWord ++ tailWord_813253).sum := by decide
  have hdescent : baseEnd_813253 < baseStart_813253 := by decide
  rcases family_descends (prefixWord ++ tailWord_813253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813271 : List Nat := [1, 1, 3, 2, 1, 2, 1, 2, 7]
def baseStart_813271 : Nat := 118140960795 + 813271 * 2 ^ 59
def prefixEnd_813271 : Nat := 4983230072969 + 3 ^ 40 * 813271 * 2
def baseEnd_813271 : Nat := 371199044766926939708747

theorem tailTrace_813271 : CollatzResearch.WordTrace tailWord_813271 prefixEnd_813271 371199044766926939708747 := by
  unfold tailWord_813271
  simp only [CollatzResearch.WordTrace]
  refine ⟨29662430236665537473863667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19774953491110358315909111 29662430236665537473863667)
  ·
    refine ⟨44493645354998306210795501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29662430236665537473863667 44493645354998306210795501)
    ·
      refine ⟨16685117008124364829048313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44493645354998306210795501 16685117008124364829048313)
      ·
        refine ⟨12513837756093273621786235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16685117008124364829048313 12513837756093273621786235)
        ·
          refine ⟨18770756634139910432679353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12513837756093273621786235 18770756634139910432679353)
          ·
            refine ⟨14078067475604932824509515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18770756634139910432679353 14078067475604932824509515)
            ·
              refine ⟨21117101213407399236764273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14078067475604932824509515 21117101213407399236764273)
              ·
                refine ⟨15837825910055549427573205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21117101213407399236764273 15837825910055549427573205)
                ·
                  refine ⟨371199044766926939708747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15837825910055549427573205 371199044766926939708747)
                  ·
                    rfl

theorem cell20_813271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 7].length) (baseStart_813271 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_813271 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_813271 prefixEnd_813271 := by exact prefixLift 813271
  have htrace : WordTrace (prefixWord ++ tailWord_813271) baseStart_813271 baseEnd_813271 := by
    simpa [prefixWord, tailWord_813271, baseEnd_813271] using wordTrace_append hprefix tailTrace_813271
  have hstable : (prefixWord ++ tailWord_813271).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813271).length < 2 ^ (prefixWord ++ tailWord_813271).sum := by decide
  have hdescent : baseEnd_813271 < baseStart_813271 := by decide
  rcases family_descends (prefixWord ++ tailWord_813271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813281 : List Nat := [1, 2, 3, 1, 3, 1, 5, 4]
def baseStart_813281 : Nat := 118140960795 + 813281 * 2 ^ 59
def prefixEnd_813281 : Nat := 4983230072969 + 3 ^ 40 * 813281 * 2
def baseEnd_813281 : Nat := 123734536346470449791791

theorem tailTrace_813281 : CollatzResearch.WordTrace tailWord_813281 prefixEnd_813281 123734536346470449791791 := by
  unfold tailWord_813281
  simp only [CollatzResearch.WordTrace]
  refine ⟨29662794966629309181727697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19775196644419539454485131 29662794966629309181727697)
  ·
    refine ⟨22247096224971981886295773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29662794966629309181727697 22247096224971981886295773)
    ·
      refine ⟨8342661084364493207360915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22247096224971981886295773 8342661084364493207360915)
      ·
        refine ⟨12513991626546739811041373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8342661084364493207360915 12513991626546739811041373)
        ·
          refine ⟨4692746859955027429140515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12513991626546739811041373 4692746859955027429140515)
          ·
            refine ⟨7039120289932541143710773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4692746859955027429140515 7039120289932541143710773)
            ·
              refine ⟨659917527181175732222885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7039120289932541143710773 659917527181175732222885)
              ·
                refine ⟨123734536346470449791791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 659917527181175732222885 123734536346470449791791)
                ·
                  rfl

theorem cell20_813281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 5, 4].length) (baseStart_813281 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_813281 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_813281 prefixEnd_813281 := by exact prefixLift 813281
  have htrace : WordTrace (prefixWord ++ tailWord_813281) baseStart_813281 baseEnd_813281 := by
    simpa [prefixWord, tailWord_813281, baseEnd_813281] using wordTrace_append hprefix tailTrace_813281
  have hstable : (prefixWord ++ tailWord_813281).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813281).length < 2 ^ (prefixWord ++ tailWord_813281).sum := by decide
  have hdescent : baseEnd_813281 < baseStart_813281 := by decide
  rcases family_descends (prefixWord ++ tailWord_813281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813312 : List Nat := [2, 1, 1, 2, 1, 1, 6, 4, 2]
def baseStart_813312 : Nat := 118140960795 + 813312 * 2 ^ 59
def prefixEnd_813312 : Nat := 4983230072969 + 3 ^ 40 * 813312 * 2
def baseEnd_813312 : Nat := 371217758284113019341913

theorem tailTrace_813312 : CollatzResearch.WordTrace tailWord_813312 prefixEnd_813312 371217758284113019341913 := by
  unfold tailWord_813312
  simp only [CollatzResearch.WordTrace]
  refine ⟨14831962814758500738053095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19775950419678000984070793 14831962814758500738053095)
  ·
    refine ⟨22247944222137751107079643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14831962814758500738053095 22247944222137751107079643)
    ·
      refine ⟨33371916333206626660619465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22247944222137751107079643 33371916333206626660619465)
      ·
        refine ⟨25028937249904969995464599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33371916333206626660619465 25028937249904969995464599)
        ·
          refine ⟨37543405874857454993196899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25028937249904969995464599 37543405874857454993196899)
          ·
            refine ⟨56315108812286182489795349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37543405874857454993196899 56315108812286182489795349)
            ·
              refine ⟨2639770725575914804209157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 56315108812286182489795349 2639770725575914804209157)
              ·
                refine ⟨494957011045484025789217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2639770725575914804209157 494957011045484025789217)
                ·
                  refine ⟨371217758284113019341913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 494957011045484025789217 371217758284113019341913)
                  ·
                    rfl

theorem cell20_813312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 4, 2].length) (baseStart_813312 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_813312 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_813312 prefixEnd_813312 := by exact prefixLift 813312
  have htrace : WordTrace (prefixWord ++ tailWord_813312) baseStart_813312 baseEnd_813312 := by
    simpa [prefixWord, tailWord_813312, baseEnd_813312] using wordTrace_append hprefix tailTrace_813312
  have hstable : (prefixWord ++ tailWord_813312).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813312).length < 2 ^ (prefixWord ++ tailWord_813312).sum := by decide
  have hdescent : baseEnd_813312 < baseStart_813312 := by decide
  rcases family_descends (prefixWord ++ tailWord_813312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813333 : List Nat := [1, 3, 2, 1, 2, 1, 4, 2, 4]
def baseStart_813333 : Nat := 118140960795 + 813333 * 2 ^ 59
def prefixEnd_813333 : Nat := 4983230072969 + 3 ^ 40 * 813333 * 2
def baseEnd_813333 : Nat := 371227343256330279641827

theorem tailTrace_813333 : CollatzResearch.WordTrace tailWord_813333 prefixEnd_813333 371227343256330279641827 := by
  unfold tailWord_813333
  simp only [CollatzResearch.WordTrace]
  refine ⟨29664691562440922062620653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19776461041627281375080435 29664691562440922062620653)
  ·
    refine ⟨11124259335915345773482745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29664691562440922062620653 11124259335915345773482745)
    ·
      refine ⟨8343194501936509330112059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11124259335915345773482745 8343194501936509330112059)
      ·
        refine ⟨12514791752904763995168089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8343194501936509330112059 12514791752904763995168089)
        ·
          refine ⟨9386093814678572996376067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12514791752904763995168089 9386093814678572996376067)
          ·
            refine ⟨14079140722017859494564101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9386093814678572996376067 14079140722017859494564101)
            ·
              refine ⟨2639838885378348655230769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14079140722017859494564101 2639838885378348655230769)
              ·
                refine ⟨1979879164033761491423077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2639838885378348655230769 1979879164033761491423077)
                ·
                  refine ⟨371227343256330279641827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1979879164033761491423077 371227343256330279641827)
                  ·
                    rfl

theorem cell20_813333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 2, 4].length) (baseStart_813333 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_813333 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_813333 prefixEnd_813333 := by exact prefixLift 813333
  have htrace : WordTrace (prefixWord ++ tailWord_813333) baseStart_813333 baseEnd_813333 := by
    simpa [prefixWord, tailWord_813333, baseEnd_813333] using wordTrace_append hprefix tailTrace_813333
  have hstable : (prefixWord ++ tailWord_813333).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813333).length < 2 ^ (prefixWord ++ tailWord_813333).sum := by decide
  have hdescent : baseEnd_813333 < baseStart_813333 := by decide
  rcases family_descends (prefixWord ++ tailWord_813333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813346 : List Nat := [3, 3, 1, 1, 3, 3, 1, 3, 2]
def baseStart_813346 : Nat := 118140960795 + 813346 * 2 ^ 59
def prefixEnd_813346 : Nat := 4983230072969 + 3 ^ 40 * 813346 * 2
def baseEnd_813346 : Nat := 371233276810560012208441

theorem tailTrace_813346 : CollatzResearch.WordTrace tailWord_813346 prefixEnd_813346 371233276810560012208441 := by
  unfold tailWord_813346
  simp only [CollatzResearch.WordTrace]
  refine ⟨7416291427848456320710973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19776777140929216855229261 7416291427848456320710973)
  ·
    refine ⟨2781109285443171120266615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7416291427848456320710973 2781109285443171120266615)
    ·
      refine ⟨4171663928164756680399923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2781109285443171120266615 4171663928164756680399923)
      ·
        refine ⟨6257495892247135020599885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4171663928164756680399923 6257495892247135020599885)
        ·
          refine ⟨2346560959592675632724957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6257495892247135020599885 2346560959592675632724957)
          ·
            refine ⟨879960359847253362271859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2346560959592675632724957 879960359847253362271859)
            ·
              refine ⟨1319940539770880043407789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 879960359847253362271859 1319940539770880043407789)
              ·
                refine ⟨494977702414080016277921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1319940539770880043407789 494977702414080016277921)
                ·
                  refine ⟨371233276810560012208441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 494977702414080016277921 371233276810560012208441)
                  ·
                    rfl

theorem cell20_813346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 3, 2].length) (baseStart_813346 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_813346 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_813346 prefixEnd_813346 := by exact prefixLift 813346
  have htrace : WordTrace (prefixWord ++ tailWord_813346) baseStart_813346 baseEnd_813346 := by
    simpa [prefixWord, tailWord_813346, baseEnd_813346] using wordTrace_append hprefix tailTrace_813346
  have hstable : (prefixWord ++ tailWord_813346).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813346).length < 2 ^ (prefixWord ++ tailWord_813346).sum := by decide
  have hdescent : baseEnd_813346 < baseStart_813346 := by decide
  rcases family_descends (prefixWord ++ tailWord_813346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813347 : List Nat := [1, 1, 1, 4, 2, 2, 1, 1, 7]
def baseStart_813347 : Nat := 118140960795 + 813347 * 2 ^ 59
def prefixEnd_813347 : Nat := 4983230072969 + 3 ^ 40 * 813347 * 2
def baseEnd_813347 : Nat := 371233733237808453175103

theorem tailTrace_813347 : CollatzResearch.WordTrace tailWord_813347 prefixEnd_813347 371233733237808453175103 := by
  unfold tailWord_813347
  simp only [CollatzResearch.WordTrace]
  refine ⟨29665202184390202453630295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19776801456260134969086863 29665202184390202453630295)
  ·
    refine ⟨44497803276585303680445443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29665202184390202453630295 44497803276585303680445443)
    ·
      refine ⟨66746704914877955520668165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44497803276585303680445443 66746704914877955520668165)
      ·
        refine ⟨12515007171539616660125281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66746704914877955520668165 12515007171539616660125281)
        ·
          refine ⟨9386255378654712495093961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12515007171539616660125281 9386255378654712495093961)
          ·
            refine ⟨7039691533991034371320471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9386255378654712495093961 7039691533991034371320471)
            ·
              refine ⟨10559537300986551556980707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7039691533991034371320471 10559537300986551556980707)
              ·
                refine ⟨15839305951479827335471061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10559537300986551556980707 15839305951479827335471061)
                ·
                  refine ⟨371233733237808453175103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15839305951479827335471061 371233733237808453175103)
                  ·
                    rfl

theorem cell20_813347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 7].length) (baseStart_813347 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_813347 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_813347 prefixEnd_813347 := by exact prefixLift 813347
  have htrace : WordTrace (prefixWord ++ tailWord_813347) baseStart_813347 baseEnd_813347 := by
    simpa [prefixWord, tailWord_813347, baseEnd_813347] using wordTrace_append hprefix tailTrace_813347
  have hstable : (prefixWord ++ tailWord_813347).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813347).length < 2 ^ (prefixWord ++ tailWord_813347).sum := by decide
  have hdescent : baseEnd_813347 < baseStart_813347 := by decide
  rcases family_descends (prefixWord ++ tailWord_813347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813377 : List Nat := [1, 2, 5, 2, 2, 2, 2, 1, 3]
def baseStart_813377 : Nat := 118140960795 + 813377 * 2 ^ 59
def prefixEnd_813377 : Nat := 4983230072969 + 3 ^ 40 * 813377 * 2
def baseEnd_813377 : Nat := 371247426055261682174981

theorem tailTrace_813377 : CollatzResearch.WordTrace tailWord_813377 prefixEnd_813377 371247426055261682174981 := by
  unfold tailWord_813377
  simp only [CollatzResearch.WordTrace]
  refine ⟨29666296374281517577222385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19777530916187678384814923 29666296374281517577222385)
  ·
    refine ⟨22249722280711138182916789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29666296374281517577222385 22249722280711138182916789)
    ·
      refine ⟨2085911463816669204648449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22249722280711138182916789 2085911463816669204648449)
      ·
        refine ⟨1564433597862501903486337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2085911463816669204648449 1564433597862501903486337)
        ·
          refine ⟨1173325198396876427614753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1564433597862501903486337 1173325198396876427614753)
          ·
            refine ⟨879993898797657320711065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1173325198396876427614753 879993898797657320711065)
            ·
              refine ⟨659995424098242990533299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 879993898797657320711065 659995424098242990533299)
              ·
                refine ⟨989993136147364485799949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 659995424098242990533299 989993136147364485799949)
                ·
                  refine ⟨371247426055261682174981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 989993136147364485799949 371247426055261682174981)
                  ·
                    rfl

theorem cell20_813377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 2, 1, 3].length) (baseStart_813377 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_813377 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_813377 prefixEnd_813377 := by exact prefixLift 813377
  have htrace : WordTrace (prefixWord ++ tailWord_813377) baseStart_813377 baseEnd_813377 := by
    simpa [prefixWord, tailWord_813377, baseEnd_813377] using wordTrace_append hprefix tailTrace_813377
  have hstable : (prefixWord ++ tailWord_813377).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813377).length < 2 ^ (prefixWord ++ tailWord_813377).sum := by decide
  have hdescent : baseEnd_813377 < baseStart_813377 := by decide
  rcases family_descends (prefixWord ++ tailWord_813377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813416 : List Nat := [2, 1, 4, 2, 2, 9]
def baseStart_813416 : Nat := 118140960795 + 813416 * 2 ^ 59
def prefixEnd_813416 : Nat := 4983230072969 + 3 ^ 40 * 813416 * 2
def baseEnd_813416 : Nat := 13750563952516699254623

theorem tailTrace_813416 : CollatzResearch.WordTrace tailWord_813416 prefixEnd_813416 13750563952516699254623 := by
  unfold tailWord_813416
  simp only [CollatzResearch.WordTrace]
  refine ⟨14833859410570113618946051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19778479214093484825261401 14833859410570113618946051)
  ·
    refine ⟨22250789115855170428419077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14833859410570113618946051 22250789115855170428419077)
    ·
      refine ⟨4172022959222844455328577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22250789115855170428419077 4172022959222844455328577)
      ·
        refine ⟨3129017219417133341496433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4172022959222844455328577 3129017219417133341496433)
        ·
          refine ⟨2346762914562850006122325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3129017219417133341496433 2346762914562850006122325)
          ·
            refine ⟨13750563952516699254623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2346762914562850006122325 13750563952516699254623)
            ·
              rfl

theorem cell20_813416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 9].length) (baseStart_813416 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_813416 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_813416 prefixEnd_813416 := by exact prefixLift 813416
  have htrace : WordTrace (prefixWord ++ tailWord_813416) baseStart_813416 baseEnd_813416 := by
    simpa [prefixWord, tailWord_813416, baseEnd_813416] using wordTrace_append hprefix tailTrace_813416
  have hstable : (prefixWord ++ tailWord_813416).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813416).length < 2 ^ (prefixWord ++ tailWord_813416).sum := by decide
  have hdescent : baseEnd_813416 < baseStart_813416 := by decide
  rcases family_descends (prefixWord ++ tailWord_813416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813447 : List Nat := [1, 1, 4, 2, 2, 1, 3, 2, 4]
def baseStart_813447 : Nat := 118140960795 + 813447 * 2 ^ 59
def prefixEnd_813447 : Nat := 4983230072969 + 3 ^ 40 * 813447 * 2
def baseEnd_813447 : Nat := 371279375962652549841361

theorem tailTrace_813447 : CollatzResearch.WordTrace tailWord_813447 prefixEnd_813447 371279375962652549841361 := by
  unfold tailWord_813447
  simp only [CollatzResearch.WordTrace]
  refine ⟨29668849484027919532270595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19779232989351946354847063 29668849484027919532270595)
  ·
    refine ⟨44503274226041879298405893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29668849484027919532270595 44503274226041879298405893)
    ·
      refine ⟨8344363917382852368451105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44503274226041879298405893 8344363917382852368451105)
      ·
        refine ⟨6258272938037139276338329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8344363917382852368451105 6258272938037139276338329)
        ·
          refine ⟨4693704703527854457253747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6258272938037139276338329 4693704703527854457253747)
          ·
            refine ⟨7040557055291781685880621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4693704703527854457253747 7040557055291781685880621)
            ·
              refine ⟨2640208895734418132205233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7040557055291781685880621 2640208895734418132205233)
              ·
                refine ⟨1980156671800813599153925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2640208895734418132205233 1980156671800813599153925)
                ·
                  refine ⟨371279375962652549841361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1980156671800813599153925 371279375962652549841361)
                  ·
                    rfl

theorem cell20_813447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 2, 4].length) (baseStart_813447 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_813447 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_813447 prefixEnd_813447 := by exact prefixLift 813447
  have htrace : WordTrace (prefixWord ++ tailWord_813447) baseStart_813447 baseEnd_813447 := by
    simpa [prefixWord, tailWord_813447, baseEnd_813447] using wordTrace_append hprefix tailTrace_813447
  have hstable : (prefixWord ++ tailWord_813447).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813447).length < 2 ^ (prefixWord ++ tailWord_813447).sum := by decide
  have hdescent : baseEnd_813447 < baseStart_813447 := by decide
  rcases family_descends (prefixWord ++ tailWord_813447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813460 : List Nat := [2, 4, 2, 1, 3, 1, 2, 3, 2]
def baseStart_813460 : Nat := 118140960795 + 813460 * 2 ^ 59
def prefixEnd_813460 : Nat := 4983230072969 + 3 ^ 40 * 813460 * 2
def baseEnd_813460 : Nat := 371285309516882282407975

theorem tailTrace_813460 : CollatzResearch.WordTrace tailWord_813460 prefixEnd_813460 371285309516882282407975 := by
  unfold tailWord_813460
  simp only [CollatzResearch.WordTrace]
  refine ⟨14834661816490411376246917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19779549088653881834995889 14834661816490411376246917)
  ·
    refine ⟨2781499090591952133046297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14834661816490411376246917 2781499090591952133046297)
    ·
      refine ⟨2086124317943964099784723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2781499090591952133046297 2086124317943964099784723)
      ·
        refine ⟨3129186476915946149677085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2086124317943964099784723 3129186476915946149677085)
        ·
          refine ⟨1173444928843479806128907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3129186476915946149677085 1173444928843479806128907)
          ·
            refine ⟨1760167393265219709193361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1173444928843479806128907 1760167393265219709193361)
            ·
              refine ⟨1320125544948914781895021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1760167393265219709193361 1320125544948914781895021)
              ·
                refine ⟨495047079355843043210633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1320125544948914781895021 495047079355843043210633)
                ·
                  refine ⟨371285309516882282407975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 495047079355843043210633 371285309516882282407975)
                  ·
                    rfl

theorem cell20_813460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 3, 2].length) (baseStart_813460 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_813460 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_813460 prefixEnd_813460 := by exact prefixLift 813460
  have htrace : WordTrace (prefixWord ++ tailWord_813460) baseStart_813460 baseEnd_813460 := by
    simpa [prefixWord, tailWord_813460, baseEnd_813460] using wordTrace_append hprefix tailTrace_813460
  have hstable : (prefixWord ++ tailWord_813460).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813460).length < 2 ^ (prefixWord ++ tailWord_813460).sum := by decide
  have hdescent : baseEnd_813460 < baseStart_813460 := by decide
  rcases family_descends (prefixWord ++ tailWord_813460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813461 : List Nat := [1, 3, 2, 1, 1, 2, 1, 4, 5]
def baseStart_813461 : Nat := 118140960795 + 813461 * 2 ^ 59
def prefixEnd_813461 : Nat := 4983230072969 + 3 ^ 40 * 813461 * 2
def baseEnd_813461 : Nat := 371285765944130723374637

theorem tailTrace_813461 : CollatzResearch.WordTrace tailWord_813461 prefixEnd_813461 371285765944130723374637 := by
  unfold tailWord_813461
  simp only [CollatzResearch.WordTrace]
  refine ⟨29669360105977199923280237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19779573403984799948853491 29669360105977199923280237)
  ·
    refine ⟨11126010039741449971230089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29669360105977199923280237 11126010039741449971230089)
    ·
      refine ⟨8344507529806087478422567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11126010039741449971230089 8344507529806087478422567)
      ·
        refine ⟨12516761294709131217633851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8344507529806087478422567 12516761294709131217633851)
        ·
          refine ⟨18775141942063696826450777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12516761294709131217633851 18775141942063696826450777)
          ·
            refine ⟨14081356456547772619838083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18775141942063696826450777 14081356456547772619838083)
            ·
              refine ⟨21122034684821658929757125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14081356456547772619838083 21122034684821658929757125)
              ·
                refine ⟨3960381503404061049329461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21122034684821658929757125 3960381503404061049329461)
                ·
                  refine ⟨371285765944130723374637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3960381503404061049329461 371285765944130723374637)
                  ·
                    rfl

theorem cell20_813461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 4, 5].length) (baseStart_813461 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_813461 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_813461 prefixEnd_813461 := by exact prefixLift 813461
  have htrace : WordTrace (prefixWord ++ tailWord_813461) baseStart_813461 baseEnd_813461 := by
    simpa [prefixWord, tailWord_813461, baseEnd_813461] using wordTrace_append hprefix tailTrace_813461
  have hstable : (prefixWord ++ tailWord_813461).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813461).length < 2 ^ (prefixWord ++ tailWord_813461).sum := by decide
  have hdescent : baseEnd_813461 < baseStart_813461 := by decide
  rcases family_descends (prefixWord ++ tailWord_813461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813495 : List Nat := [1, 1, 3, 1, 3, 4, 3, 1, 3]
def baseStart_813495 : Nat := 118140960795 + 813495 * 2 ^ 59
def prefixEnd_813495 : Nat := 4983230072969 + 3 ^ 40 * 813495 * 2
def baseEnd_813495 : Nat := 371301284470577716241165

theorem tailTrace_813495 : CollatzResearch.WordTrace tailWord_813495 prefixEnd_813495 371301284470577716241165 := by
  unfold tailWord_813495
  simp only [CollatzResearch.WordTrace]
  refine ⟨29670600187854023730017939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19780400125236015820011959 29670600187854023730017939)
  ·
    refine ⟨44505900281781035595026909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29670600187854023730017939 44505900281781035595026909)
    ·
      refine ⟨16689712605667888348135091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44505900281781035595026909 16689712605667888348135091)
      ·
        refine ⟨25034568908501832522202637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16689712605667888348135091 25034568908501832522202637)
        ·
          refine ⟨9387963340688187195825989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25034568908501832522202637 9387963340688187195825989)
          ·
            refine ⟨1760243126379035099217373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9387963340688187195825989 1760243126379035099217373)
            ·
              refine ⟨660091172392138162206515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1760243126379035099217373 660091172392138162206515)
              ·
                refine ⟨990136758588207243309773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 660091172392138162206515 990136758588207243309773)
                ·
                  refine ⟨371301284470577716241165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 990136758588207243309773 371301284470577716241165)
                  ·
                    rfl

theorem cell20_813495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 3, 1, 3].length) (baseStart_813495 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_813495 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_813495 prefixEnd_813495 := by exact prefixLift 813495
  have htrace : WordTrace (prefixWord ++ tailWord_813495) baseStart_813495 baseEnd_813495 := by
    simpa [prefixWord, tailWord_813495, baseEnd_813495] using wordTrace_append hprefix tailTrace_813495
  have hstable : (prefixWord ++ tailWord_813495).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813495).length < 2 ^ (prefixWord ++ tailWord_813495).sum := by decide
  have hdescent : baseEnd_813495 < baseStart_813495 := by decide
  rcases family_descends (prefixWord ++ tailWord_813495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813505 : List Nat := [1, 2, 7, 1, 1, 1, 1, 6]
def baseStart_813505 : Nat := 118140960795 + 813505 * 2 ^ 59
def prefixEnd_813505 : Nat := 4983230072969 + 3 ^ 40 * 813505 * 2
def baseEnd_813505 : Nat := 123768616247687375302597

theorem tailTrace_813505 : CollatzResearch.WordTrace tailWord_813505 prefixEnd_813505 123768616247687375302597 := by
  unfold tailWord_813505
  simp only [CollatzResearch.WordTrace]
  refine ⟨29670964917817795437881969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19780643278545196958587979 29670964917817795437881969)
  ·
    refine ⟨22253223688363346578411477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29670964917817795437881969 22253223688363346578411477)
    ·
      refine ⟨521559930196015935431519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 22253223688363346578411477 521559930196015935431519)
      ·
        refine ⟨782339895294023903147279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 521559930196015935431519 782339895294023903147279)
        ·
          refine ⟨1173509842941035854720919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 782339895294023903147279 1173509842941035854720919)
          ·
            refine ⟨1760264764411553782081379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1173509842941035854720919 1760264764411553782081379)
            ·
              refine ⟨2640397146617330673122069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1760264764411553782081379 2640397146617330673122069)
              ·
                refine ⟨123768616247687375302597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2640397146617330673122069 123768616247687375302597)
                ·
                  rfl

theorem cell20_813505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 6].length) (baseStart_813505 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_813505 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_813505 prefixEnd_813505 := by exact prefixLift 813505
  have htrace : WordTrace (prefixWord ++ tailWord_813505) baseStart_813505 baseEnd_813505 := by
    simpa [prefixWord, tailWord_813505, baseEnd_813505] using wordTrace_append hprefix tailTrace_813505
  have hstable : (prefixWord ++ tailWord_813505).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813505).length < 2 ^ (prefixWord ++ tailWord_813505).sum := by decide
  have hdescent : baseEnd_813505 < baseStart_813505 := by decide
  rcases family_descends (prefixWord ++ tailWord_813505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813537 : List Nat := [1, 2, 3, 1, 2, 2, 1, 3, 5]
def baseStart_813537 : Nat := 118140960795 + 813537 * 2 ^ 59
def prefixEnd_813537 : Nat := 4983230072969 + 3 ^ 40 * 813537 * 2
def baseEnd_813537 : Nat := 371320454415012236840993

theorem tailTrace_813537 : CollatzResearch.WordTrace tailWord_813537 prefixEnd_813537 371320454415012236840993 := by
  unfold tailWord_813537
  simp only [CollatzResearch.WordTrace]
  refine ⟨29672132053701864903046865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19781421369134576602031243 29672132053701864903046865)
  ·
    refine ⟨22254099040276398677285149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29672132053701864903046865 22254099040276398677285149)
    ·
      refine ⟨8345287140103649503981931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22254099040276398677285149 8345287140103649503981931)
      ·
        refine ⟨12517930710155474255972897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8345287140103649503981931 12517930710155474255972897)
        ·
          refine ⟨9388448032616605691979673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12517930710155474255972897 9388448032616605691979673)
          ·
            refine ⟨7041336024462454268984755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9388448032616605691979673 7041336024462454268984755)
            ·
              refine ⟨10562004036693681403477133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7041336024462454268984755 10562004036693681403477133)
              ·
                refine ⟨3960751513760130526303925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10562004036693681403477133 3960751513760130526303925)
                ·
                  refine ⟨371320454415012236840993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3960751513760130526303925 371320454415012236840993)
                  ·
                    rfl

theorem cell20_813537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 3, 5].length) (baseStart_813537 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_813537 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_813537 prefixEnd_813537 := by exact prefixLift 813537
  have htrace : WordTrace (prefixWord ++ tailWord_813537) baseStart_813537 baseEnd_813537 := by
    simpa [prefixWord, tailWord_813537, baseEnd_813537] using wordTrace_append hprefix tailTrace_813537
  have hstable : (prefixWord ++ tailWord_813537).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813537).length < 2 ^ (prefixWord ++ tailWord_813537).sum := by decide
  have hdescent : baseEnd_813537 < baseStart_813537 := by decide
  rcases family_descends (prefixWord ++ tailWord_813537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813550 : List Nat := [4, 1, 2, 1, 2, 4, 2, 1, 3]
def baseStart_813550 : Nat := 118140960795 + 813550 * 2 ^ 59
def prefixEnd_813550 : Nat := 4983230072969 + 3 ^ 40 * 813550 * 2
def baseEnd_813550 : Nat := 371326387969241969407607

theorem tailTrace_813550 : CollatzResearch.WordTrace tailWord_813550 prefixEnd_813550 371326387969241969407607 := by
  unfold tailWord_813550
  simp only [CollatzResearch.WordTrace]
  refine ⟨3709075775331846015408763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19781737468436512082180069 3709075775331846015408763)
  ·
    refine ⟨5563613662997769023113145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3709075775331846015408763 5563613662997769023113145)
    ·
      refine ⟨4172710247248326767334859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5563613662997769023113145 4172710247248326767334859)
      ·
        refine ⟨6259065370872490151002289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4172710247248326767334859 6259065370872490151002289)
        ·
          refine ⟨4694299028154367613251717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6259065370872490151002289 4694299028154367613251717)
          ·
            refine ⟨880181067778943927484697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4694299028154367613251717 880181067778943927484697)
            ·
              refine ⟨660135800834207945613523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 880181067778943927484697 660135800834207945613523)
              ·
                refine ⟨990203701251311918420285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 660135800834207945613523 990203701251311918420285)
                ·
                  refine ⟨371326387969241969407607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 990203701251311918420285 371326387969241969407607)
                  ·
                    rfl

theorem cell20_813550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 2, 1, 3].length) (baseStart_813550 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_813550 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_813550 prefixEnd_813550 := by exact prefixLift 813550
  have htrace : WordTrace (prefixWord ++ tailWord_813550) baseStart_813550 baseEnd_813550 := by
    simpa [prefixWord, tailWord_813550, baseEnd_813550] using wordTrace_append hprefix tailTrace_813550
  have hstable : (prefixWord ++ tailWord_813550).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813550).length < 2 ^ (prefixWord ++ tailWord_813550).sum := by decide
  have hdescent : baseEnd_813550 < baseStart_813550 := by decide
  rcases family_descends (prefixWord ++ tailWord_813550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813578 : List Nat := [3, 1, 2, 2, 2, 1, 2, 5, 2]
def baseStart_813578 : Nat := 118140960795 + 813578 * 2 ^ 59
def prefixEnd_813578 : Nat := 4983230072969 + 3 ^ 40 * 813578 * 2
def baseEnd_813578 : Nat := 371339167932198316474159

theorem tailTrace_813578 : CollatzResearch.WordTrace tailWord_813578 prefixEnd_813578 371339167932198316474159 := by
  unfold tailWord_813578
  simp only [CollatzResearch.WordTrace]
  refine ⟨7418406861638332226322347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19782418297702219270192925 7418406861638332226322347)
  ·
    refine ⟨11127610292457498339483521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7418406861638332226322347 11127610292457498339483521)
    ·
      refine ⟨8345707719343123754612641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11127610292457498339483521 8345707719343123754612641)
      ·
        refine ⟨6259280789507342815959481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8345707719343123754612641 6259280789507342815959481)
        ·
          refine ⟨4694460592130507111969611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6259280789507342815959481 4694460592130507111969611)
          ·
            refine ⟨7041690888195760667954417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4694460592130507111969611 7041690888195760667954417)
            ·
              refine ⟨5281268166146820500965813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7041690888195760667954417 5281268166146820500965813)
              ·
                refine ⟨495118890576264421965545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5281268166146820500965813 495118890576264421965545)
                ·
                  refine ⟨371339167932198316474159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 495118890576264421965545 371339167932198316474159)
                  ·
                    rfl

theorem cell20_813578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 5, 2].length) (baseStart_813578 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_813578 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_813578 prefixEnd_813578 := by exact prefixLift 813578
  have htrace : WordTrace (prefixWord ++ tailWord_813578) baseStart_813578 baseEnd_813578 := by
    simpa [prefixWord, tailWord_813578, baseEnd_813578] using wordTrace_append hprefix tailTrace_813578
  have hstable : (prefixWord ++ tailWord_813578).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813578).length < 2 ^ (prefixWord ++ tailWord_813578).sum := by decide
  have hdescent : baseEnd_813578 < baseStart_813578 := by decide
  rcases family_descends (prefixWord ++ tailWord_813578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813588 : List Nat := [2, 4, 3, 1, 1, 2, 2, 2, 3]
def baseStart_813588 : Nat := 118140960795 + 813588 * 2 ^ 59
def prefixEnd_813588 : Nat := 4983230072969 + 3 ^ 40 * 813588 * 2
def baseEnd_813588 : Nat := 371343732204682726140785

theorem tailTrace_813588 : CollatzResearch.WordTrace tailWord_813588 prefixEnd_813588 371343732204682726140785 := by
  unfold tailWord_813588
  simp only [CollatzResearch.WordTrace]
  refine ⟨14836996088258550306576709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19782661451011400408768945 14836996088258550306576709)
  ·
    refine ⟨2781936766548478182483133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14836996088258550306576709 2781936766548478182483133)
    ·
      refine ⟨1043226287455679318431175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2781936766548478182483133 1043226287455679318431175)
      ·
        refine ⟨1564839431183518977646763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1043226287455679318431175 1564839431183518977646763)
        ·
          refine ⟨2347259146775278466470145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1564839431183518977646763 2347259146775278466470145)
          ·
            refine ⟨1760444360081458849852609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2347259146775278466470145 1760444360081458849852609)
            ·
              refine ⟨1320333270061094137389457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1760444360081458849852609 1320333270061094137389457)
              ·
                refine ⟨990249952545820603042093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1320333270061094137389457 990249952545820603042093)
                ·
                  refine ⟨371343732204682726140785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 990249952545820603042093 371343732204682726140785)
                  ·
                    rfl

theorem cell20_813588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_813588 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_813588 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_813588 prefixEnd_813588 := by exact prefixLift 813588
  have htrace : WordTrace (prefixWord ++ tailWord_813588) baseStart_813588 baseEnd_813588 := by
    simpa [prefixWord, tailWord_813588, baseEnd_813588] using wordTrace_append hprefix tailTrace_813588
  have hstable : (prefixWord ++ tailWord_813588).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813588).length < 2 ^ (prefixWord ++ tailWord_813588).sum := by decide
  have hdescent : baseEnd_813588 < baseStart_813588 := by decide
  rcases family_descends (prefixWord ++ tailWord_813588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813591 : List Nat := [1, 1, 3, 6, 1, 2, 2, 2, 2]
def baseStart_813591 : Nat := 118140960795 + 813591 * 2 ^ 59
def prefixEnd_813591 : Nat := 4983230072969 + 3 ^ 40 * 813591 * 2
def baseEnd_813591 : Nat := 371345101486428049040773

theorem tailTrace_813591 : CollatzResearch.WordTrace tailWord_813591 prefixEnd_813591 371345101486428049040773 := by
  unfold tailWord_813591
  simp only [CollatzResearch.WordTrace]
  refine ⟨29674101595506232125512627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19782734397004154750341751 29674101595506232125512627)
  ·
    refine ⟨44511152393259348188268941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29674101595506232125512627 44511152393259348188268941)
    ·
      refine ⟨16691682147472255570600853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44511152393259348188268941 16691682147472255570600853)
      ·
        refine ⟨782422600662761979871915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 16691682147472255570600853 782422600662761979871915)
        ·
          refine ⟨1173633900994142969807873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 782422600662761979871915 1173633900994142969807873)
          ·
            refine ⟨880225425745607227355905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1173633900994142969807873 880225425745607227355905)
            ·
              refine ⟨660169069309205420516929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 880225425745607227355905 660169069309205420516929)
              ·
                refine ⟨495126801981904065387697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 660169069309205420516929 495126801981904065387697)
                ·
                  refine ⟨371345101486428049040773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 495126801981904065387697 371345101486428049040773)
                  ·
                    rfl

theorem cell20_813591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 2, 2, 2].length) (baseStart_813591 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_813591 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_813591 prefixEnd_813591 := by exact prefixLift 813591
  have htrace : WordTrace (prefixWord ++ tailWord_813591) baseStart_813591 baseEnd_813591 := by
    simpa [prefixWord, tailWord_813591, baseEnd_813591] using wordTrace_append hprefix tailTrace_813591
  have hstable : (prefixWord ++ tailWord_813591).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813591).length < 2 ^ (prefixWord ++ tailWord_813591).sum := by decide
  have hdescent : baseEnd_813591 < baseStart_813591 := by decide
  rcases family_descends (prefixWord ++ tailWord_813591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813592 : List Nat := [2, 1, 2, 3, 3, 1, 1, 4, 3]
def baseStart_813592 : Nat := 118140960795 + 813592 * 2 ^ 59
def prefixEnd_813592 : Nat := 4983230072969 + 3 ^ 40 * 813592 * 2
def baseEnd_813592 : Nat := 371345557913676490007435

theorem tailTrace_813592 : CollatzResearch.WordTrace tailWord_813592 prefixEnd_813592 371345557913676490007435 := by
  unfold tailWord_813592
  simp only [CollatzResearch.WordTrace]
  refine ⟨14837069034251304648149515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19782758712335072864199353 14837069034251304648149515)
  ·
    refine ⟨22255603551376956972224273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14837069034251304648149515 22255603551376956972224273)
    ·
      refine ⟨16691702663532717729168205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22255603551376956972224273 16691702663532717729168205)
      ·
        refine ⟨6259388498824769148438077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16691702663532717729168205 6259388498824769148438077)
        ·
          refine ⟨2347270687059288430664279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6259388498824769148438077 2347270687059288430664279)
          ·
            refine ⟨3520906030588932645996419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2347270687059288430664279 3520906030588932645996419)
            ·
              refine ⟨5281359045883398968994629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3520906030588932645996419 5281359045883398968994629)
              ·
                refine ⟨990254821103137306686493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5281359045883398968994629 990254821103137306686493)
                ·
                  refine ⟨371345557913676490007435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 990254821103137306686493 371345557913676490007435)
                  ·
                    rfl

theorem cell20_813592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 4, 3].length) (baseStart_813592 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_813592 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_813592 prefixEnd_813592 := by exact prefixLift 813592
  have htrace : WordTrace (prefixWord ++ tailWord_813592) baseStart_813592 baseEnd_813592 := by
    simpa [prefixWord, tailWord_813592, baseEnd_813592] using wordTrace_append hprefix tailTrace_813592
  have hstable : (prefixWord ++ tailWord_813592).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813592).length < 2 ^ (prefixWord ++ tailWord_813592).sum := by decide
  have hdescent : baseEnd_813592 < baseStart_813592 := by decide
  rcases family_descends (prefixWord ++ tailWord_813592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813633 : List Nat := [1, 2, 5, 1, 1, 3, 2, 3, 2]
def baseStart_813633 : Nat := 118140960795 + 813633 * 2 ^ 59
def prefixEnd_813633 : Nat := 4983230072969 + 3 ^ 40 * 813633 * 2
def baseEnd_813633 : Nat := 371364271430862569640601

theorem tailTrace_813633 : CollatzResearch.WordTrace tailWord_813633 prefixEnd_813633 371364271430862569640601 := by
  unfold tailWord_813633
  simp only [CollatzResearch.WordTrace]
  refine ⟨29675633461354073298541553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19783755640902715532361035 29675633461354073298541553)
  ·
    refine ⟨22256725096015554973906165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29675633461354073298541553 22256725096015554973906165)
    ·
      refine ⟨2086567977751458278803703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22256725096015554973906165 2086567977751458278803703)
      ·
        refine ⟨3129851966627187418205555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2086567977751458278803703 3129851966627187418205555)
        ·
          refine ⟨4694777949940781127308333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3129851966627187418205555 4694777949940781127308333)
          ·
            refine ⟨1760541731227792922740625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4694777949940781127308333 1760541731227792922740625)
            ·
              refine ⟨1320406298420844692055469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1760541731227792922740625 1320406298420844692055469)
              ·
                refine ⟨495152361907816759520801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1320406298420844692055469 495152361907816759520801)
                ·
                  refine ⟨371364271430862569640601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 495152361907816759520801 371364271430862569640601)
                  ·
                    rfl

theorem cell20_813633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 3, 2].length) (baseStart_813633 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_813633 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_813633 prefixEnd_813633 := by exact prefixLift 813633
  have htrace : WordTrace (prefixWord ++ tailWord_813633) baseStart_813633 baseEnd_813633 := by
    simpa [prefixWord, tailWord_813633, baseEnd_813633] using wordTrace_append hprefix tailTrace_813633
  have hstable : (prefixWord ++ tailWord_813633).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813633).length < 2 ^ (prefixWord ++ tailWord_813633).sum := by decide
  have hdescent : baseEnd_813633 < baseStart_813633 := by decide
  rcases family_descends (prefixWord ++ tailWord_813633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813678 : List Nat := [4, 1, 2, 2, 2, 3, 2, 4]
def baseStart_813678 : Nat := 118140960795 + 813678 * 2 ^ 59
def prefixEnd_813678 : Nat := 4983230072969 + 3 ^ 40 * 813678 * 2
def baseEnd_813678 : Nat := 123794936885680804380139

theorem tailTrace_813678 : CollatzResearch.WordTrace tailWord_813678 prefixEnd_813678 123794936885680804380139 := by
  unfold tailWord_813678
  simp only [CollatzResearch.WordTrace]
  refine ⟨3709659343273880747991211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19784849830794030655953125 3709659343273880747991211)
  ·
    refine ⟨5564489014910821121986817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3709659343273880747991211 5564489014910821121986817)
    ·
      refine ⟨4173366761183115841490113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5564489014910821121986817 4173366761183115841490113)
      ·
        refine ⟨3130025070887336881117585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4173366761183115841490113 3130025070887336881117585)
        ·
          refine ⟨2347518803165502660838189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3130025070887336881117585 2347518803165502660838189)
          ·
            refine ⟨880319551187063497814321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2347518803165502660838189 880319551187063497814321)
            ·
              refine ⟨660239663390297623360741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 880319551187063497814321 660239663390297623360741)
              ·
                refine ⟨123794936885680804380139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 660239663390297623360741 123794936885680804380139)
                ·
                  rfl

theorem cell20_813678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 2, 4].length) (baseStart_813678 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_813678 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_813678 prefixEnd_813678 := by exact prefixLift 813678
  have htrace : WordTrace (prefixWord ++ tailWord_813678) baseStart_813678 baseEnd_813678 := by
    simpa [prefixWord, tailWord_813678, baseEnd_813678] using wordTrace_append hprefix tailTrace_813678
  have hstable : (prefixWord ++ tailWord_813678).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813678).length < 2 ^ (prefixWord ++ tailWord_813678).sum := by decide
  have hdescent : baseEnd_813678 < baseStart_813678 := by decide
  rcases family_descends (prefixWord ++ tailWord_813678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813689 : List Nat := [1, 2, 1, 3, 3, 2, 1, 2, 5]
def baseStart_813689 : Nat := 118140960795 + 813689 * 2 ^ 59
def prefixEnd_813689 : Nat := 4983230072969 + 3 ^ 40 * 813689 * 2
def baseEnd_813689 : Nat := 371389831356775263773705

theorem tailTrace_813689 : CollatzResearch.WordTrace tailWord_813689 prefixEnd_813689 371389831356775263773705 := by
  unfold tailWord_813689
  simp only [CollatzResearch.WordTrace]
  refine ⟨29677675949151194862580121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19785117299434129908386747 29677675949151194862580121)
  ·
    refine ⟨22258256961863396146935091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29677675949151194862580121 22258256961863396146935091)
    ·
      refine ⟨33387385442795094220402637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22258256961863396146935091 33387385442795094220402637)
      ·
        refine ⟨12520269541048160332650989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33387385442795094220402637 12520269541048160332650989)
        ·
          refine ⟨4695101077893060124744121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12520269541048160332650989 4695101077893060124744121)
          ·
            refine ⟨3521325808419795093558091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4695101077893060124744121 3521325808419795093558091)
            ·
              refine ⟨5281988712629692640337137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3521325808419795093558091 5281988712629692640337137)
              ·
                refine ⟨3961491534472269480252853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5281988712629692640337137 3961491534472269480252853)
                ·
                  refine ⟨371389831356775263773705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3961491534472269480252853 371389831356775263773705)
                  ·
                    rfl

theorem cell20_813689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 2, 5].length) (baseStart_813689 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_813689 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_813689 prefixEnd_813689 := by exact prefixLift 813689
  have htrace : WordTrace (prefixWord ++ tailWord_813689) baseStart_813689 baseEnd_813689 := by
    simpa [prefixWord, tailWord_813689, baseEnd_813689] using wordTrace_append hprefix tailTrace_813689
  have hstable : (prefixWord ++ tailWord_813689).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813689).length < 2 ^ (prefixWord ++ tailWord_813689).sum := by decide
  have hdescent : baseEnd_813689 < baseStart_813689 := by decide
  rcases family_descends (prefixWord ++ tailWord_813689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813692 : List Nat := [2, 2, 2, 1, 1, 2, 5, 3, 2]
def baseStart_813692 : Nat := 118140960795 + 813692 * 2 ^ 59
def prefixEnd_813692 : Nat := 4983230072969 + 3 ^ 40 * 813692 * 2
def baseEnd_813692 : Nat := 371391200638520586673693

theorem tailTrace_813692 : CollatzResearch.WordTrace tailWord_813692 prefixEnd_813692 371391200638520586673693 := by
  unfold tailWord_813692
  simp only [CollatzResearch.WordTrace]
  refine ⟨14838892684070163187469665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19785190245426884249959553 14838892684070163187469665)
  ·
    refine ⟨11129169513052622390602249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14838892684070163187469665 11129169513052622390602249)
    ·
      refine ⟨8346877134789466792951687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11129169513052622390602249 8346877134789466792951687)
      ·
        refine ⟨12520315702184200189427531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8346877134789466792951687 12520315702184200189427531)
        ·
          refine ⟨18780473553276300284141297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12520315702184200189427531 18780473553276300284141297)
          ·
            refine ⟨14085355164957225213105973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18780473553276300284141297 14085355164957225213105973)
            ·
              refine ⟨1320502046714739863728685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14085355164957225213105973 1320502046714739863728685)
              ·
                refine ⟨495188267518027448898257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1320502046714739863728685 495188267518027448898257)
                ·
                  refine ⟨371391200638520586673693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 495188267518027448898257 371391200638520586673693)
                  ·
                    rfl

theorem cell20_813692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 3, 2].length) (baseStart_813692 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_813692 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_813692 prefixEnd_813692 := by exact prefixLift 813692
  have htrace : WordTrace (prefixWord ++ tailWord_813692) baseStart_813692 baseEnd_813692 := by
    simpa [prefixWord, tailWord_813692, baseEnd_813692] using wordTrace_append hprefix tailTrace_813692
  have hstable : (prefixWord ++ tailWord_813692).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813692).length < 2 ^ (prefixWord ++ tailWord_813692).sum := by decide
  have hdescent : baseEnd_813692 < baseStart_813692 := by decide
  rcases family_descends (prefixWord ++ tailWord_813692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813720 : List Nat := [2, 1, 2, 4, 1, 1, 4, 5]
def baseStart_813720 : Nat := 118140960795 + 813720 * 2 ^ 59
def prefixEnd_813720 : Nat := 4983230072969 + 3 ^ 40 * 813720 * 2
def baseEnd_813720 : Nat := 123801326867158977913415

theorem tailTrace_813720 : CollatzResearch.WordTrace tailWord_813720 prefixEnd_813720 123801326867158977913415 := by
  unfold tailWord_813720
  simp only [CollatzResearch.WordTrace]
  refine ⟨14839403306019443578479307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19785871074692591437972409 14839403306019443578479307)
  ·
    refine ⟨22259104959029165367718961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14839403306019443578479307 22259104959029165367718961)
    ·
      refine ⟨16694328719271874025789221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22259104959029165367718961 16694328719271874025789221)
      ·
        refine ⟨3130186634863476379835479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16694328719271874025789221 3130186634863476379835479)
        ·
          refine ⟨4695279952295214569753219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3130186634863476379835479 4695279952295214569753219)
          ·
            refine ⟨7042919928442821854629829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4695279952295214569753219 7042919928442821854629829)
            ·
              refine ⟨1320547486583029097743093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7042919928442821854629829 1320547486583029097743093)
              ·
                refine ⟨123801326867158977913415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1320547486583029097743093 123801326867158977913415)
                ·
                  rfl

theorem cell20_813720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 5].length) (baseStart_813720 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_813720 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_813720 prefixEnd_813720 := by exact prefixLift 813720
  have htrace : WordTrace (prefixWord ++ tailWord_813720) baseStart_813720 baseEnd_813720 := by
    simpa [prefixWord, tailWord_813720, baseEnd_813720] using wordTrace_append hprefix tailTrace_813720
  have hstable : (prefixWord ++ tailWord_813720).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813720).length < 2 ^ (prefixWord ++ tailWord_813720).sum := by decide
  have hdescent : baseEnd_813720 < baseStart_813720 := by decide
  rcases family_descends (prefixWord ++ tailWord_813720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813764 : List Nat := [2, 3, 3, 1, 1, 4, 2, 2, 2]
def baseStart_813764 : Nat := 118140960795 + 813764 * 2 ^ 59
def prefixEnd_813764 : Nat := 4983230072969 + 3 ^ 40 * 813764 * 2
def baseEnd_813764 : Nat := 371424063400408336273399

theorem tailTrace_813764 : CollatzResearch.WordTrace tailWord_813764 prefixEnd_813764 371424063400408336273399 := by
  unfold tailWord_813764
  simp only [CollatzResearch.WordTrace]
  refine ⟨14840205711939741335780173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19786940949252988447706897 14840205711939741335780173)
  ·
    refine ⟨5565077141977403000917565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14840205711939741335780173 5565077141977403000917565)
    ·
      refine ⟨2086903928241526125344087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5565077141977403000917565 2086903928241526125344087)
      ·
        refine ⟨3130355892362289188016131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2086903928241526125344087 3130355892362289188016131)
        ·
          refine ⟨4695533838543433782024197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3130355892362289188016131 4695533838543433782024197)
          ·
            refine ⟨880412594726893834129537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4695533838543433782024197 880412594726893834129537)
            ·
              refine ⟨660309446045170375597153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 880412594726893834129537 660309446045170375597153)
              ·
                refine ⟨495232084533877781697865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 660309446045170375597153 495232084533877781697865)
                ·
                  refine ⟨371424063400408336273399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 495232084533877781697865 371424063400408336273399)
                  ·
                    rfl

theorem cell20_813764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 2, 2, 2].length) (baseStart_813764 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_813764 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_813764 prefixEnd_813764 := by exact prefixLift 813764
  have htrace : WordTrace (prefixWord ++ tailWord_813764) baseStart_813764 baseEnd_813764 := by
    simpa [prefixWord, tailWord_813764, baseEnd_813764] using wordTrace_append hprefix tailTrace_813764
  have hstable : (prefixWord ++ tailWord_813764).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813764).length < 2 ^ (prefixWord ++ tailWord_813764).sum := by decide
  have hdescent : baseEnd_813764 < baseStart_813764 := by decide
  rcases family_descends (prefixWord ++ tailWord_813764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813768 : List Nat := [2, 1, 3, 1, 2, 4, 1, 4, 2]
def baseStart_813768 : Nat := 118140960795 + 813768 * 2 ^ 59
def prefixEnd_813768 : Nat := 4983230072969 + 3 ^ 40 * 813768 * 2
def baseEnd_813768 : Nat := 371425889109402100140049

theorem tailTrace_813768 : CollatzResearch.WordTrace tailWord_813768 prefixEnd_813768 371425889109402100140049 := by
  unfold tailWord_813768
  simp only [CollatzResearch.WordTrace]
  refine ⟨14840278657932495677352979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19787038210576660903137305 14840278657932495677352979)
  ·
    refine ⟨22260417986898743516029469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14840278657932495677352979 22260417986898743516029469)
    ·
      refine ⟨8347656745087028818511051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22260417986898743516029469 8347656745087028818511051)
      ·
        refine ⟨12521485117630543227766577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8347656745087028818511051 12521485117630543227766577)
        ·
          refine ⟨9391113838222907420824933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12521485117630543227766577 9391113838222907420824933)
          ·
            refine ⟨1760833844666795141404675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9391113838222907420824933 1760833844666795141404675)
            ·
              refine ⟨2641250767000192712107013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1760833844666795141404675 2641250767000192712107013)
              ·
                refine ⟨495234518812536133520065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2641250767000192712107013 495234518812536133520065)
                ·
                  refine ⟨371425889109402100140049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 495234518812536133520065 371425889109402100140049)
                  ·
                    rfl

theorem cell20_813768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 4, 2].length) (baseStart_813768 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_813768 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_813768 prefixEnd_813768 := by exact prefixLift 813768
  have htrace : WordTrace (prefixWord ++ tailWord_813768) baseStart_813768 baseEnd_813768 := by
    simpa [prefixWord, tailWord_813768, baseEnd_813768] using wordTrace_append hprefix tailTrace_813768
  have hstable : (prefixWord ++ tailWord_813768).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813768).length < 2 ^ (prefixWord ++ tailWord_813768).sum := by decide
  have hdescent : baseEnd_813768 < baseStart_813768 := by decide
  rcases family_descends (prefixWord ++ tailWord_813768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813806 : List Nat := [4, 1, 2, 1, 1, 3, 1, 5, 2]
def baseStart_813806 : Nat := 118140960795 + 813806 * 2 ^ 59
def prefixEnd_813806 : Nat := 4983230072969 + 3 ^ 40 * 813806 * 2
def baseEnd_813806 : Nat := 371443233344842856873227

theorem tailTrace_813806 : CollatzResearch.WordTrace tailWord_813806 prefixEnd_813806 371443233344842856873227 := by
  unfold tailWord_813806
  simp only [CollatzResearch.WordTrace]
  refine ⟨3710242911215915480573659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19787962193151549229726181 3710242911215915480573659)
  ·
    refine ⟨5565364366823873220860489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3710242911215915480573659 5565364366823873220860489)
    ·
      refine ⟨4174023275117904915645367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5565364366823873220860489 4174023275117904915645367)
      ·
        refine ⟨6261034912676857373468051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4174023275117904915645367 6261034912676857373468051)
        ·
          refine ⟨9391552369015286060202077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6261034912676857373468051 9391552369015286060202077)
          ·
            refine ⟨3521832138380732272575779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9391552369015286060202077 3521832138380732272575779)
            ·
              refine ⟨5282748207571098408863669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3521832138380732272575779 5282748207571098408863669)
              ·
                refine ⟨495257644459790475830969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5282748207571098408863669 495257644459790475830969)
                ·
                  refine ⟨371443233344842856873227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 495257644459790475830969 371443233344842856873227)
                  ·
                    rfl

theorem cell20_813806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 5, 2].length) (baseStart_813806 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_813806 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_813806 prefixEnd_813806 := by exact prefixLift 813806
  have htrace : WordTrace (prefixWord ++ tailWord_813806) baseStart_813806 baseEnd_813806 := by
    simpa [prefixWord, tailWord_813806, baseEnd_813806] using wordTrace_append hprefix tailTrace_813806
  have hstable : (prefixWord ++ tailWord_813806).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813806).length < 2 ^ (prefixWord ++ tailWord_813806).sum := by decide
  have hdescent : baseEnd_813806 < baseStart_813806 := by decide
  rcases family_descends (prefixWord ++ tailWord_813806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813812 : List Nat := [2, 6, 1, 1, 3, 1, 1, 2, 3]
def baseStart_813812 : Nat := 118140960795 + 813812 * 2 ^ 59
def prefixEnd_813812 : Nat := 4983230072969 + 3 ^ 40 * 813812 * 2
def baseEnd_813812 : Nat := 371445971908333502673203

theorem tailTrace_813812 : CollatzResearch.WordTrace tailWord_813812 prefixEnd_813812 371445971908333502673203 := by
  unfold tailWord_813812
  simp only [CollatzResearch.WordTrace]
  refine ⟨14841081063852793434653845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19788108085137057912871793 14841081063852793434653845)
  ·
    refine ⟨695675674868099692249399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 14841081063852793434653845 695675674868099692249399)
    ·
      refine ⟨1043513512302149538374099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 695675674868099692249399 1043513512302149538374099)
      ·
        refine ⟨1565270268453224307561149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1043513512302149538374099 1565270268453224307561149)
        ·
          refine ⟨586976350669959115335431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1565270268453224307561149 586976350669959115335431)
          ·
            refine ⟨880464526004938673003147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 586976350669959115335431 880464526004938673003147)
            ·
              refine ⟨1320696789007408009504721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 880464526004938673003147 1320696789007408009504721)
              ·
                refine ⟨990522591755556007128541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1320696789007408009504721 990522591755556007128541)
                ·
                  refine ⟨371445971908333502673203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 990522591755556007128541 371445971908333502673203)
                  ·
                    rfl

theorem cell20_813812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_813812 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_813812 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_813812 prefixEnd_813812 := by exact prefixLift 813812
  have htrace : WordTrace (prefixWord ++ tailWord_813812) baseStart_813812 baseEnd_813812 := by
    simpa [prefixWord, tailWord_813812, baseEnd_813812] using wordTrace_append hprefix tailTrace_813812
  have hstable : (prefixWord ++ tailWord_813812).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813812).length < 2 ^ (prefixWord ++ tailWord_813812).sum := by decide
  have hdescent : baseEnd_813812 < baseStart_813812 := by decide
  rcases family_descends (prefixWord ++ tailWord_813812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813820 : List Nat := [2, 2, 2, 1, 3, 2, 3, 2, 3]
def baseStart_813820 : Nat := 118140960795 + 813820 * 2 ^ 59
def prefixEnd_813820 : Nat := 4983230072969 + 3 ^ 40 * 813820 * 2
def baseEnd_813820 : Nat := 371449623326321030406503

theorem tailTrace_813820 : CollatzResearch.WordTrace tailWord_813820 prefixEnd_813820 371449623326321030406503 := by
  unfold tailWord_813820
  simp only [CollatzResearch.WordTrace]
  refine ⟨14841226955838302117799457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19788302607784402823732609 14841226955838302117799457)
  ·
    refine ⟨11130920216878726588349593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14841226955838302117799457 11130920216878726588349593)
    ·
      refine ⟨8348190162659044941262195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11130920216878726588349593 8348190162659044941262195)
      ·
        refine ⟨12522285243988567411893293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8348190162659044941262195 12522285243988567411893293)
        ·
          refine ⟨4695856966495712779459985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12522285243988567411893293 4695856966495712779459985)
          ·
            refine ⟨3521892724871784584594989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4695856966495712779459985 3521892724871784584594989)
            ·
              refine ⟨1320709771826919219223121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3521892724871784584594989 1320709771826919219223121)
              ·
                refine ⟨990532328870189414417341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1320709771826919219223121 990532328870189414417341)
                ·
                  refine ⟨371449623326321030406503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 990532328870189414417341 371449623326321030406503)
                  ·
                    rfl

theorem cell20_813820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 2, 3].length) (baseStart_813820 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_813820 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_813820 prefixEnd_813820 := by exact prefixLift 813820
  have htrace : WordTrace (prefixWord ++ tailWord_813820) baseStart_813820 baseEnd_813820 := by
    simpa [prefixWord, tailWord_813820, baseEnd_813820] using wordTrace_append hprefix tailTrace_813820
  have hstable : (prefixWord ++ tailWord_813820).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813820).length < 2 ^ (prefixWord ++ tailWord_813820).sum := by decide
  have hdescent : baseEnd_813820 < baseStart_813820 := by decide
  rcases family_descends (prefixWord ++ tailWord_813820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813841 : List Nat := [1, 2, 2, 1, 1, 3, 2, 5, 3]
def baseStart_813841 : Nat := 118140960795 + 813841 * 2 ^ 59
def prefixEnd_813841 : Nat := 4983230072969 + 3 ^ 40 * 813841 * 2
def baseEnd_813841 : Nat := 371459208298538290706417

theorem tailTrace_813841 : CollatzResearch.WordTrace tailWord_813841 prefixEnd_813841 371459208298538290706417 := by
  unfold tailWord_813841
  simp only [CollatzResearch.WordTrace]
  refine ⟨29683219844600524822113377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19788813229733683214742251 29683219844600524822113377)
  ·
    refine ⟨22262414883450393616585033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29683219844600524822113377 22262414883450393616585033)
    ·
      refine ⟨16696811162587795212438775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22262414883450393616585033 16696811162587795212438775)
      ·
        refine ⟨25045216743881692818658163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16696811162587795212438775 25045216743881692818658163)
        ·
          refine ⟨37567825115822539227987245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25045216743881692818658163 37567825115822539227987245)
          ·
            refine ⟨14087934418433452210495217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37567825115822539227987245 14087934418433452210495217)
            ·
              refine ⟨10565950813825089157871413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14087934418433452210495217 10565950813825089157871413)
              ·
                refine ⟨990557888796102108550445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10565950813825089157871413 990557888796102108550445)
                ·
                  refine ⟨371459208298538290706417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 990557888796102108550445 371459208298538290706417)
                  ·
                    rfl

theorem cell20_813841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 5, 3].length) (baseStart_813841 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_813841 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_813841 prefixEnd_813841 := by exact prefixLift 813841
  have htrace : WordTrace (prefixWord ++ tailWord_813841) baseStart_813841 baseEnd_813841 := by
    simpa [prefixWord, tailWord_813841, baseEnd_813841] using wordTrace_append hprefix tailTrace_813841
  have hstable : (prefixWord ++ tailWord_813841).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813841).length < 2 ^ (prefixWord ++ tailWord_813841).sum := by decide
  have hdescent : baseEnd_813841 < baseStart_813841 := by decide
  rcases family_descends (prefixWord ++ tailWord_813841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813878 : List Nat := [5, 1, 2, 2, 3, 1, 1, 1, 4]
def baseStart_813878 : Nat := 118140960795 + 813878 * 2 ^ 59
def prefixEnd_813878 : Nat := 4983230072969 + 3 ^ 40 * 813878 * 2
def baseEnd_813878 : Nat := 371476096106730606472933

theorem tailTrace_813878 : CollatzResearch.WordTrace tailWord_813878 prefixEnd_813878 371476096106730606472933 := by
  unfold tailWord_813878
  simp only [CollatzResearch.WordTrace]
  refine ⟨1855285584091655008825643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19789712896977653427473525 1855285584091655008825643)
  ·
    refine ⟨2782928376137482513238465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1855285584091655008825643 2782928376137482513238465)
    ·
      refine ⟨2087196282103111884928849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2782928376137482513238465 2087196282103111884928849)
      ·
        refine ⟨1565397211577333913696637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2087196282103111884928849 1565397211577333913696637)
        ·
          refine ⟨587023954341500217636239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1565397211577333913696637 587023954341500217636239)
          ·
            refine ⟨880535931512250326454359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 587023954341500217636239 880535931512250326454359)
            ·
              refine ⟨1320803897268375489681539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 880535931512250326454359 1320803897268375489681539)
              ·
                refine ⟨1981205845902563234522309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1320803897268375489681539 1981205845902563234522309)
                ·
                  refine ⟨371476096106730606472933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1981205845902563234522309 371476096106730606472933)
                  ·
                    rfl

theorem cell20_813878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 1, 4].length) (baseStart_813878 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_813878 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_813878 prefixEnd_813878 := by exact prefixLift 813878
  have htrace : WordTrace (prefixWord ++ tailWord_813878) baseStart_813878 baseEnd_813878 := by
    simpa [prefixWord, tailWord_813878, baseEnd_813878] using wordTrace_append hprefix tailTrace_813878
  have hstable : (prefixWord ++ tailWord_813878).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813878).length < 2 ^ (prefixWord ++ tailWord_813878).sum := by decide
  have hdescent : baseEnd_813878 < baseStart_813878 := by decide
  rcases family_descends (prefixWord ++ tailWord_813878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813879 : List Nat := [1, 1, 3, 1, 2, 1, 4, 4, 3]
def baseStart_813879 : Nat := 118140960795 + 813879 * 2 ^ 59
def prefixEnd_813879 : Nat := 4983230072969 + 3 ^ 40 * 813879 * 2
def baseEnd_813879 : Nat := 371476552533979047439595

theorem tailTrace_813879 : CollatzResearch.WordTrace tailWord_813879 prefixEnd_813879 371476552533979047439595 := by
  unfold tailWord_813879
  simp only [CollatzResearch.WordTrace]
  refine ⟨29684605818462857311996691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19789737212308571541331127 29684605818462857311996691)
  ·
    refine ⟨44526908727694285967995037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29684605818462857311996691 44526908727694285967995037)
    ·
      refine ⟨16697590772885357237998139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44526908727694285967995037 16697590772885357237998139)
      ·
        refine ⟨25046386159328035856997209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16697590772885357237998139 25046386159328035856997209)
        ·
          refine ⟨18784789619496026892747907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25046386159328035856997209 18784789619496026892747907)
          ·
            refine ⟨28177184429244040339121861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18784789619496026892747907 28177184429244040339121861)
            ·
              refine ⟨5283222080483257563585349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28177184429244040339121861 5283222080483257563585349)
              ·
                refine ⟨990604140090610793172253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5283222080483257563585349 990604140090610793172253)
                ·
                  refine ⟨371476552533979047439595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 990604140090610793172253 371476552533979047439595)
                  ·
                    rfl

theorem cell20_813879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 4, 3].length) (baseStart_813879 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_813879 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_813879 prefixEnd_813879 := by exact prefixLift 813879
  have htrace : WordTrace (prefixWord ++ tailWord_813879) baseStart_813879 baseEnd_813879 := by
    simpa [prefixWord, tailWord_813879, baseEnd_813879] using wordTrace_append hprefix tailTrace_813879
  have hstable : (prefixWord ++ tailWord_813879).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813879).length < 2 ^ (prefixWord ++ tailWord_813879).sum := by decide
  have hdescent : baseEnd_813879 < baseStart_813879 := by decide
  rcases family_descends (prefixWord ++ tailWord_813879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813882 : List Nat := [3, 1, 1, 1, 6, 2, 1, 1, 4]
def baseStart_813882 : Nat := 118140960795 + 813882 * 2 ^ 59
def prefixEnd_813882 : Nat := 4983230072969 + 3 ^ 40 * 813882 * 2
def baseEnd_813882 : Nat := 371477921815724370339583

theorem tailTrace_813882 : CollatzResearch.WordTrace tailWord_813882 prefixEnd_813882 371477921815724370339583 := by
  unfold tailWord_813882
  simp only [CollatzResearch.WordTrace]
  refine ⟨7421178809362997206088975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19789810158301325882903933 7421178809362997206088975)
  ·
    refine ⟨11131768214044495809133463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7421178809362997206088975 11131768214044495809133463)
    ·
      refine ⟨16697652321066743713700195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11131768214044495809133463 16697652321066743713700195)
      ·
        refine ⟨25046478481600115570550293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16697652321066743713700195 25046478481600115570550293)
        ·
          refine ⟨1174053678825005417369545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 25046478481600115570550293 1174053678825005417369545)
          ·
            refine ⟨880540259118754063027159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1174053678825005417369545 880540259118754063027159)
            ·
              refine ⟨1320810388678131094540739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 880540259118754063027159 1320810388678131094540739)
              ·
                refine ⟨1981215583017196641811109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1320810388678131094540739 1981215583017196641811109)
                ·
                  refine ⟨371477921815724370339583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1981215583017196641811109 371477921815724370339583)
                  ·
                    rfl

theorem cell20_813882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 1, 4].length) (baseStart_813882 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_813882 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_813882 prefixEnd_813882 := by exact prefixLift 813882
  have htrace : WordTrace (prefixWord ++ tailWord_813882) baseStart_813882 baseEnd_813882 := by
    simpa [prefixWord, tailWord_813882, baseEnd_813882] using wordTrace_append hprefix tailTrace_813882
  have hstable : (prefixWord ++ tailWord_813882).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813882).length < 2 ^ (prefixWord ++ tailWord_813882).sum := by decide
  have hdescent : baseEnd_813882 < baseStart_813882 := by decide
  rcases family_descends (prefixWord ++ tailWord_813882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
