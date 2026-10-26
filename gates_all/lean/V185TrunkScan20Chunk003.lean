import V185TrunkScan20Chunk002

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_17516 : List Nat := [2, 2, 1, 1, 3, 2, 4, 5]
def baseStart_17516 : Nat := 118140960795 + 17516 * 2 ^ 59
def prefixEnd_17516 : Nat := 4983230072969 + 3 ^ 40 * 17516 * 2
def baseEnd_17516 : Nat := 2664926561261837709467

theorem tailTrace_17516 : CollatzResearch.WordTrace tailWord_17516 prefixEnd_17516 2664926561261837709467 := by
  unfold tailWord_17516
  simp only [CollatzResearch.WordTrace]
  refine ⟨319430502274999169872201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 425907336366665559829601 319430502274999169872201)
  ·
    refine ⟨239572876706249377404151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 319430502274999169872201 239572876706249377404151)
    ·
      refine ⟨359359315059374066106227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239572876706249377404151 359359315059374066106227)
      ·
        refine ⟨539038972589061099159341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 359359315059374066106227 539038972589061099159341)
        ·
          refine ⟨202139614720897912184753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 539038972589061099159341 202139614720897912184753)
          ·
            refine ⟨151604711040673434138565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 202139614720897912184753 151604711040673434138565)
            ·
              refine ⟨28425883320126268900981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 151604711040673434138565 28425883320126268900981)
              ·
                refine ⟨2664926561261837709467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28425883320126268900981 2664926561261837709467)
                ·
                  rfl

theorem cell20_17516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 5].length) (baseStart_17516 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_17516 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_17516 prefixEnd_17516 := by exact prefixLift 17516
  have htrace : WordTrace (prefixWord ++ tailWord_17516) baseStart_17516 baseEnd_17516 := by
    simpa [prefixWord, tailWord_17516, baseEnd_17516] using wordTrace_append hprefix tailTrace_17516
  have hstable : (prefixWord ++ tailWord_17516).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17516).length < 2 ^ (prefixWord ++ tailWord_17516).sum := by decide
  have hdescent : baseEnd_17516 < baseStart_17516 := by decide
  rcases family_descends (prefixWord ++ tailWord_17516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17554 : List Nat := [3, 2, 3, 1, 1, 10]
def baseStart_17554 : Nat := 118140960795 + 17554 * 2 ^ 59
def prefixEnd_17554 : Nat := 4983230072969 + 3 ^ 40 * 17554 * 2
def baseEnd_17554 : Nat := 296745330341713698577

theorem tailTrace_17554 : CollatzResearch.WordTrace tailWord_17554 prefixEnd_17554 296745330341713698577 := by
  unfold tailWord_17554
  simp only [CollatzResearch.WordTrace]
  refine ⟨160061744603082707406929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 426831318941553886418477 160061744603082707406929)
  ·
    refine ⟨120046308452312030555197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160061744603082707406929 120046308452312030555197)
    ·
      refine ⟨45017365669617011458199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120046308452312030555197 45017365669617011458199)
      ·
        refine ⟨67526048504425517187299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45017365669617011458199 67526048504425517187299)
        ·
          refine ⟨101289072756638275780949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67526048504425517187299 101289072756638275780949)
          ·
            refine ⟨296745330341713698577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 101289072756638275780949 296745330341713698577)
            ·
              rfl

theorem cell20_17554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 10].length) (baseStart_17554 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_17554 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_17554 prefixEnd_17554 := by exact prefixLift 17554
  have htrace : WordTrace (prefixWord ++ tailWord_17554) baseStart_17554 baseEnd_17554 := by
    simpa [prefixWord, tailWord_17554, baseEnd_17554] using wordTrace_append hprefix tailTrace_17554
  have hstable : (prefixWord ++ tailWord_17554).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17554).length < 2 ^ (prefixWord ++ tailWord_17554).sum := by decide
  have hdescent : baseEnd_17554 < baseStart_17554 := by decide
  rcases family_descends (prefixWord ++ tailWord_17554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17560 : List Nat := [2, 1, 2, 4, 2, 3, 2, 2, 2]
def baseStart_17560 : Nat := 118140960795 + 17560 * 2 ^ 59
def prefixEnd_17560 : Nat := 4983230072969 + 3 ^ 40 * 17560 * 2
def baseEnd_17560 : Nat := 8014862482716915661555

theorem tailTrace_17560 : CollatzResearch.WordTrace tailWord_17560 prefixEnd_17560 8014862482716915661555 := by
  unfold tailWord_17560
  simp only [CollatzResearch.WordTrace]
  refine ⟨320232908195296927173067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 426977210927062569564089 320232908195296927173067)
  ·
    refine ⟨480349362292945390759601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 320232908195296927173067 480349362292945390759601)
    ·
      refine ⟨360262021719709043069701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 480349362292945390759601 360262021719709043069701)
      ·
        refine ⟨67549129072445445575569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 360262021719709043069701 67549129072445445575569)
        ·
          refine ⟨50661846804334084181677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67549129072445445575569 50661846804334084181677)
          ·
            refine ⟨18998192551625281568129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50661846804334084181677 18998192551625281568129)
            ·
              refine ⟨14248644413718961176097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18998192551625281568129 14248644413718961176097)
              ·
                refine ⟨10686483310289220882073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14248644413718961176097 10686483310289220882073)
                ·
                  refine ⟨8014862482716915661555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10686483310289220882073 8014862482716915661555)
                  ·
                    rfl

theorem cell20_17560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 2, 2, 2].length) (baseStart_17560 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_17560 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_17560 prefixEnd_17560 := by exact prefixLift 17560
  have htrace : WordTrace (prefixWord ++ tailWord_17560) baseStart_17560 baseEnd_17560 := by
    simpa [prefixWord, tailWord_17560, baseEnd_17560] using wordTrace_append hprefix tailTrace_17560
  have hstable : (prefixWord ++ tailWord_17560).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17560).length < 2 ^ (prefixWord ++ tailWord_17560).sum := by decide
  have hdescent : baseEnd_17560 < baseStart_17560 := by decide
  rcases family_descends (prefixWord ++ tailWord_17560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17585 : List Nat := [1, 2, 2, 5, 1, 1, 1, 1, 6]
def baseStart_17585 : Nat := 118140960795 + 17585 * 2 ^ 59
def prefixEnd_17585 : Nat := 4983230072969 + 3 ^ 40 * 17585 * 2
def baseEnd_17585 : Nat := 8026273163927939828119

theorem tailTrace_17585 : CollatzResearch.WordTrace tailWord_17585 prefixEnd_17585 8026273163927939828119 := by
  unfold tailWord_17585
  simp only [CollatzResearch.WordTrace]
  refine ⟨641377641300023124006209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 427585094200015416004139 641377641300023124006209)
  ·
    refine ⟨481033230975017343004657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 641377641300023124006209 481033230975017343004657)
    ·
      refine ⟨360774923231263007253493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 481033230975017343004657 360774923231263007253493)
      ·
        refine ⟨33822649052930906930015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 360774923231263007253493 33822649052930906930015)
        ·
          refine ⟨50733973579396360395023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33822649052930906930015 50733973579396360395023)
          ·
            refine ⟨76100960369094540592535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50733973579396360395023 76100960369094540592535)
            ·
              refine ⟨114151440553641810888803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76100960369094540592535 114151440553641810888803)
              ·
                refine ⟨171227160830462716333205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114151440553641810888803 171227160830462716333205)
                ·
                  refine ⟨8026273163927939828119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 171227160830462716333205 8026273163927939828119)
                  ·
                    rfl

theorem cell20_17585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 6].length) (baseStart_17585 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_17585 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_17585 prefixEnd_17585 := by exact prefixLift 17585
  have htrace : WordTrace (prefixWord ++ tailWord_17585) baseStart_17585 baseEnd_17585 := by
    simpa [prefixWord, tailWord_17585, baseEnd_17585] using wordTrace_append hprefix tailTrace_17585
  have hstable : (prefixWord ++ tailWord_17585).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17585).length < 2 ^ (prefixWord ++ tailWord_17585).sum := by decide
  have hdescent : baseEnd_17585 < baseStart_17585 := by decide
  rcases family_descends (prefixWord ++ tailWord_17585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17633 : List Nat := [1, 2, 3, 1, 3, 3, 3, 1, 3]
def baseStart_17633 : Nat := 118140960795 + 17633 * 2 ^ 59
def prefixEnd_17633 : Nat := 4983230072969 + 3 ^ 40 * 17633 * 2
def baseEnd_17633 : Nat := 8048181671853106227923

theorem tailTrace_17633 : CollatzResearch.WordTrace tailWord_17633 prefixEnd_17633 8048181671853106227923 := by
  unfold tailWord_17633
  simp only [CollatzResearch.WordTrace]
  refine ⟨643128345126127321753553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 428752230084084881169035 643128345126127321753553)
  ·
    refine ⟨482346258844595491315165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 643128345126127321753553 482346258844595491315165)
    ·
      refine ⟨180879847066723309243187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 482346258844595491315165 180879847066723309243187)
      ·
        refine ⟨271319770600084963864781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180879847066723309243187 271319770600084963864781)
        ·
          refine ⟨101744913975031861449293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 271319770600084963864781 101744913975031861449293)
          ·
            refine ⟨38154342740636948043485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 101744913975031861449293 38154342740636948043485)
            ·
              refine ⟨14307878527738855516307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38154342740636948043485 14307878527738855516307)
              ·
                refine ⟨21461817791608283274461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14307878527738855516307 21461817791608283274461)
                ·
                  refine ⟨8048181671853106227923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21461817791608283274461 8048181671853106227923)
                  ·
                    rfl

theorem cell20_17633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 3, 1, 3].length) (baseStart_17633 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_17633 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_17633 prefixEnd_17633 := by exact prefixLift 17633
  have htrace : WordTrace (prefixWord ++ tailWord_17633) baseStart_17633 baseEnd_17633 := by
    simpa [prefixWord, tailWord_17633, baseEnd_17633] using wordTrace_append hprefix tailTrace_17633
  have hstable : (prefixWord ++ tailWord_17633).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17633).length < 2 ^ (prefixWord ++ tailWord_17633).sum := by decide
  have hdescent : baseEnd_17633 < baseStart_17633 := by decide
  rcases family_descends (prefixWord ++ tailWord_17633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17668 : List Nat := [2, 3, 2, 2, 2, 1, 8]
def baseStart_17668 : Nat := 118140960795 + 17668 * 2 ^ 59
def prefixEnd_17668 : Nat := 4983230072969 + 3 ^ 40 * 17668 * 2
def baseEnd_17668 : Nat := 896017402838726673457

theorem tailTrace_17668 : CollatzResearch.WordTrace tailWord_17668 prefixEnd_17668 896017402838726673457 := by
  unfold tailWord_17668
  simp only [CollatzResearch.WordTrace]
  refine ⟨322202449999664149638829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 429603266666218866185105 322202449999664149638829)
  ·
    refine ⟨120825918749874056114561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 322202449999664149638829 120825918749874056114561)
    ·
      refine ⟨90619439062405542085921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120825918749874056114561 90619439062405542085921)
      ·
        refine ⟨67964579296804156564441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90619439062405542085921 67964579296804156564441)
        ·
          refine ⟨50973434472603117423331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67964579296804156564441 50973434472603117423331)
          ·
            refine ⟨76460151708904676134997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50973434472603117423331 76460151708904676134997)
            ·
              refine ⟨896017402838726673457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 76460151708904676134997 896017402838726673457)
              ·
                rfl

theorem cell20_17668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 8].length) (baseStart_17668 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_17668 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_17668 prefixEnd_17668 := by exact prefixLift 17668
  have htrace : WordTrace (prefixWord ++ tailWord_17668) baseStart_17668 baseEnd_17668 := by
    simpa [prefixWord, tailWord_17668, baseEnd_17668] using wordTrace_append hprefix tailTrace_17668
  have hstable : (prefixWord ++ tailWord_17668).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17668).length < 2 ^ (prefixWord ++ tailWord_17668).sum := by decide
  have hdescent : baseEnd_17668 < baseStart_17668 := by decide
  rcases family_descends (prefixWord ++ tailWord_17668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17675 : List Nat := [1, 1, 1, 1, 5, 3, 2, 1, 5]
def baseStart_17675 : Nat := 118140960795 + 17675 * 2 ^ 59
def prefixEnd_17675 : Nat := 4983230072969 + 3 ^ 40 * 17675 * 2
def baseEnd_17675 : Nat := 8067351616287626827751

theorem tailTrace_17675 : CollatzResearch.WordTrace tailWord_17675 prefixEnd_17675 8067351616287626827751 := by
  unfold tailWord_17675
  simp only [CollatzResearch.WordTrace]
  refine ⟨644660210973968494782479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 429773473982645663188319 644660210973968494782479)
  ·
    refine ⟨966990316460952742173719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 644660210973968494782479 966990316460952742173719)
    ·
      refine ⟨1450485474691429113260579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 966990316460952742173719 1450485474691429113260579)
      ·
        refine ⟨2175728212037143669890869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1450485474691429113260579 2175728212037143669890869)
        ·
          refine ⟨203974519878482219052269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2175728212037143669890869 203974519878482219052269)
          ·
            refine ⟨76490444954430832144601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 203974519878482219052269 76490444954430832144601)
            ·
              refine ⟨57367833715823124108451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76490444954430832144601 57367833715823124108451)
              ·
                refine ⟨86051750573734686162677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57367833715823124108451 86051750573734686162677)
                ·
                  refine ⟨8067351616287626827751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 86051750573734686162677 8067351616287626827751)
                  ·
                    rfl

theorem cell20_17675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 1, 5].length) (baseStart_17675 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_17675 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_17675 prefixEnd_17675 := by exact prefixLift 17675
  have htrace : WordTrace (prefixWord ++ tailWord_17675) baseStart_17675 baseEnd_17675 := by
    simpa [prefixWord, tailWord_17675, baseEnd_17675] using wordTrace_append hprefix tailTrace_17675
  have hstable : (prefixWord ++ tailWord_17675).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17675).length < 2 ^ (prefixWord ++ tailWord_17675).sum := by decide
  have hdescent : baseEnd_17675 < baseStart_17675 := by decide
  rcases family_descends (prefixWord ++ tailWord_17675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17678 : List Nat := [4, 1, 1, 2, 1, 5, 1, 1, 4]
def baseStart_17678 : Nat := 118140960795 + 17678 * 2 ^ 59
def prefixEnd_17678 : Nat := 4983230072969 + 3 ^ 40 * 17678 * 2
def baseEnd_17678 : Nat := 8068720898032949727739

theorem tailTrace_17678 : CollatzResearch.WordTrace tailWord_17678 prefixEnd_17678 8068720898032949727739 := by
  unfold tailWord_17678
  simp only [CollatzResearch.WordTrace]
  refine ⟨80596203745387500892711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 429846419975400004761125 80596203745387500892711)
  ·
    refine ⟨120894305618081251339067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80596203745387500892711 120894305618081251339067)
    ·
      refine ⟨181341458427121877008601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120894305618081251339067 181341458427121877008601)
      ·
        refine ⟨136006093820341407756451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 181341458427121877008601 136006093820341407756451)
        ·
          refine ⟨204009140730512111634677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136006093820341407756451 204009140730512111634677)
          ·
            refine ⟨19125856943485510465751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 204009140730512111634677 19125856943485510465751)
            ·
              refine ⟨28688785415228265698627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19125856943485510465751 28688785415228265698627)
              ·
                refine ⟨43033178122842398547941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28688785415228265698627 43033178122842398547941)
                ·
                  refine ⟨8068720898032949727739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43033178122842398547941 8068720898032949727739)
                  ·
                    rfl

theorem cell20_17678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 1, 4].length) (baseStart_17678 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_17678 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_17678 prefixEnd_17678 := by exact prefixLift 17678
  have htrace : WordTrace (prefixWord ++ tailWord_17678) baseStart_17678 baseEnd_17678 := by
    simpa [prefixWord, tailWord_17678, baseEnd_17678] using wordTrace_append hprefix tailTrace_17678
  have hstable : (prefixWord ++ tailWord_17678).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17678).length < 2 ^ (prefixWord ++ tailWord_17678).sum := by decide
  have hdescent : baseEnd_17678 < baseStart_17678 := by decide
  rcases family_descends (prefixWord ++ tailWord_17678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17727 : List Nat := [1, 1, 2, 2, 4, 10]
def baseStart_17727 : Nat := 118140960795 + 17727 * 2 ^ 59
def prefixEnd_17727 : Nat := 4983230072969 + 3 ^ 40 * 17727 * 2
def baseEnd_17727 : Nat := 299669845674316929415

theorem tailTrace_17727 : CollatzResearch.WordTrace tailWord_17727 prefixEnd_17727 299669845674316929415 := by
  unfold tailWord_17727
  simp only [CollatzResearch.WordTrace]
  refine ⟨646556806785581375675435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 431037871190387583783623 646556806785581375675435)
  ·
    refine ⟨969835210178372063513153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 646556806785581375675435 969835210178372063513153)
    ·
      refine ⟨727376407633779047634865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 969835210178372063513153 727376407633779047634865)
      ·
        refine ⟨545532305725334285726149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 727376407633779047634865 545532305725334285726149)
        ·
          refine ⟨102287307323500178573653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 545532305725334285726149 102287307323500178573653)
          ·
            refine ⟨299669845674316929415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 102287307323500178573653 299669845674316929415)
            ·
              rfl

theorem cell20_17727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 10].length) (baseStart_17727 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_17727 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_17727 prefixEnd_17727 := by exact prefixLift 17727
  have htrace : WordTrace (prefixWord ++ tailWord_17727) baseStart_17727 baseEnd_17727 := by
    simpa [prefixWord, tailWord_17727, baseEnd_17727] using wordTrace_append hprefix tailTrace_17727
  have hstable : (prefixWord ++ tailWord_17727).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17727).length < 2 ^ (prefixWord ++ tailWord_17727).sum := by decide
  have hdescent : baseEnd_17727 < baseStart_17727 := by decide
  rcases family_descends (prefixWord ++ tailWord_17727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17789 : List Nat := [1, 4, 1, 1, 2, 2, 3, 1, 5]
def baseStart_17789 : Nat := 118140960795 + 17789 * 2 ^ 59
def prefixEnd_17789 : Nat := 4983230072969 + 3 ^ 40 * 17789 * 2
def baseEnd_17789 : Nat := 8119384322609897027285

theorem tailTrace_17789 : CollatzResearch.WordTrace tailWord_17789 prefixEnd_17789 8119384322609897027285 := by
  unfold tailWord_17789
  simp only [CollatzResearch.WordTrace]
  refine ⟨648818132560965964432421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 432545421707310642954947 648818132560965964432421)
  ·
    refine ⟨121653399855181118331079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 648818132560965964432421 121653399855181118331079)
    ·
      refine ⟨182480099782771677496619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121653399855181118331079 182480099782771677496619)
      ·
        refine ⟨273720149674157516244929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182480099782771677496619 273720149674157516244929)
        ·
          refine ⟨205290112255618137183697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 273720149674157516244929 205290112255618137183697)
          ·
            refine ⟨153967584191713602887773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 205290112255618137183697 153967584191713602887773)
            ·
              refine ⟨57737844071892601082915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 153967584191713602887773 57737844071892601082915)
              ·
                refine ⟨86606766107838901624373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57737844071892601082915 86606766107838901624373)
                ·
                  refine ⟨8119384322609897027285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 86606766107838901624373 8119384322609897027285)
                  ·
                    rfl

theorem cell20_17789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_17789 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_17789 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_17789 prefixEnd_17789 := by exact prefixLift 17789
  have htrace : WordTrace (prefixWord ++ tailWord_17789) baseStart_17789 baseEnd_17789 := by
    simpa [prefixWord, tailWord_17789, baseEnd_17789] using wordTrace_append hprefix tailTrace_17789
  have hstable : (prefixWord ++ tailWord_17789).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17789).length < 2 ^ (prefixWord ++ tailWord_17789).sum := by decide
  have hdescent : baseEnd_17789 < baseStart_17789 := by decide
  rcases family_descends (prefixWord ++ tailWord_17789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17803 : List Nat := [1, 1, 1, 1, 4, 3, 2, 7]
def baseStart_17803 : Nat := 118140960795 + 17803 * 2 ^ 59
def prefixEnd_17803 : Nat := 4983230072969 + 3 ^ 40 * 17803 * 2
def baseEnd_17803 : Nat := 2708591434696023520187

theorem tailTrace_17803 : CollatzResearch.WordTrace tailWord_17803 prefixEnd_17803 2708591434696023520187 := by
  unfold tailWord_17803
  simp only [CollatzResearch.WordTrace]
  refine ⟨649328754510246355442063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 432885836340164236961375 649328754510246355442063)
  ·
    refine ⟨973993131765369533163095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 649328754510246355442063 973993131765369533163095)
    ·
      refine ⟨1460989697648054299744643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 973993131765369533163095 1460989697648054299744643)
      ·
        refine ⟨2191484546472081449616965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1460989697648054299744643 2191484546472081449616965)
        ·
          refine ⟨410903352463515271803181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2191484546472081449616965 410903352463515271803181)
          ·
            refine ⟨154088757173818226926193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 410903352463515271803181 154088757173818226926193)
            ·
              refine ⟨115566567880363670194645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 154088757173818226926193 115566567880363670194645)
              ·
                refine ⟨2708591434696023520187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 115566567880363670194645 2708591434696023520187)
                ·
                  rfl

theorem cell20_17803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 7].length) (baseStart_17803 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_17803 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_17803 prefixEnd_17803 := by exact prefixLift 17803
  have htrace : WordTrace (prefixWord ++ tailWord_17803) baseStart_17803 baseEnd_17803 := by
    simpa [prefixWord, tailWord_17803, baseEnd_17803] using wordTrace_append hprefix tailTrace_17803
  have hstable : (prefixWord ++ tailWord_17803).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17803).length < 2 ^ (prefixWord ++ tailWord_17803).sum := by decide
  have hdescent : baseEnd_17803 < baseStart_17803 := by decide
  rcases family_descends (prefixWord ++ tailWord_17803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17816 : List Nat := [2, 1, 2, 5, 2, 2, 2, 4]
def baseStart_17816 : Nat := 118140960795 + 17816 * 2 ^ 59
def prefixEnd_17816 : Nat := 4983230072969 + 3 ^ 40 * 17816 * 2
def baseEnd_17816 : Nat := 2710569286105934375725

theorem tailTrace_17816 : CollatzResearch.WordTrace tailWord_17816 prefixEnd_17816 2710569286105934375725 := by
  unfold tailWord_17816
  simp only [CollatzResearch.WordTrace]
  refine ⟨324901451731574787832651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 433201935642099717110201 324901451731574787832651)
  ·
    refine ⟨487352177597362181748977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 324901451731574787832651 487352177597362181748977)
    ·
      refine ⟨365514133198021636311733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 487352177597362181748977 365514133198021636311733)
      ·
        refine ⟨34266949987314528404225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 365514133198021636311733 34266949987314528404225)
        ·
          refine ⟨25700212490485896303169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34266949987314528404225 25700212490485896303169)
          ·
            refine ⟨19275159367864422227377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25700212490485896303169 19275159367864422227377)
            ·
              refine ⟨14456369525898316670533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19275159367864422227377 14456369525898316670533)
              ·
                refine ⟨2710569286105934375725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14456369525898316670533 2710569286105934375725)
                ·
                  rfl

theorem cell20_17816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 2, 4].length) (baseStart_17816 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_17816 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_17816 prefixEnd_17816 := by exact prefixLift 17816
  have htrace : WordTrace (prefixWord ++ tailWord_17816) baseStart_17816 baseEnd_17816 := by
    simpa [prefixWord, tailWord_17816, baseEnd_17816] using wordTrace_append hprefix tailTrace_17816
  have hstable : (prefixWord ++ tailWord_17816).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17816).length < 2 ^ (prefixWord ++ tailWord_17816).sum := by decide
  have hdescent : baseEnd_17816 < baseStart_17816 := by decide
  rcases family_descends (prefixWord ++ tailWord_17816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17837 : List Nat := [1, 5, 2, 2, 1, 3, 6]
def baseStart_17837 : Nat := 118140960795 + 17837 * 2 ^ 59
def prefixEnd_17837 : Nat := 4983230072969 + 3 ^ 40 * 17837 * 2
def baseEnd_17837 : Nat := 904588092281673714121

theorem tailTrace_17837 : CollatzResearch.WordTrace tailWord_17837 prefixEnd_17837 904588092281673714121 := by
  unfold tailWord_17837
  simp only [CollatzResearch.WordTrace]
  refine ⟨650568836387070162179765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 433712557591380108119843 650568836387070162179765)
  ·
    refine ⟨60990828411287827704353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 650568836387070162179765 60990828411287827704353)
    ·
      refine ⟨45743121308465870778265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60990828411287827704353 45743121308465870778265)
      ·
        refine ⟨34307340981349403083699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45743121308465870778265 34307340981349403083699)
        ·
          refine ⟨51461011472024104625549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34307340981349403083699 51461011472024104625549)
          ·
            refine ⟨19297879302009039234581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51461011472024104625549 19297879302009039234581)
            ·
              refine ⟨904588092281673714121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 19297879302009039234581 904588092281673714121)
              ·
                rfl

theorem cell20_17837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 6].length) (baseStart_17837 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_17837 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_17837 prefixEnd_17837 := by exact prefixLift 17837
  have htrace : WordTrace (prefixWord ++ tailWord_17837) baseStart_17837 baseEnd_17837 := by
    simpa [prefixWord, tailWord_17837, baseEnd_17837] using wordTrace_append hprefix tailTrace_17837
  have hstable : (prefixWord ++ tailWord_17837).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17837).length < 2 ^ (prefixWord ++ tailWord_17837).sum := by decide
  have hdescent : baseEnd_17837 < baseStart_17837 := by decide
  rcases family_descends (prefixWord ++ tailWord_17837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17903 : List Nat := [1, 1, 2, 1, 4, 1, 3, 4, 3]
def baseStart_17903 : Nat := 118140960795 + 17903 * 2 ^ 59
def prefixEnd_17903 : Nat := 4983230072969 + 3 ^ 40 * 17903 * 2
def baseEnd_17903 : Nat := 8171417028932167226819

theorem tailTrace_17903 : CollatzResearch.WordTrace tailWord_17903 prefixEnd_17903 8171417028932167226819 := by
  unfold tailWord_17903
  simp only [CollatzResearch.WordTrace]
  refine ⟨652976054147963434082363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 435317369431975622721575 652976054147963434082363)
  ·
    refine ⟨979464081221945151123545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 652976054147963434082363 979464081221945151123545)
    ·
      refine ⟨734598060916458863342659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 979464081221945151123545 734598060916458863342659)
      ·
        refine ⟨1101897091374688295013989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 734598060916458863342659 1101897091374688295013989)
        ·
          refine ⟨206605704632754055315123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1101897091374688295013989 206605704632754055315123)
          ·
            refine ⟨309908556949131082972685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 206605704632754055315123 309908556949131082972685)
            ·
              refine ⟨116215708855924156114757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 309908556949131082972685 116215708855924156114757)
              ·
                refine ⟨21790445410485779271517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 116215708855924156114757 21790445410485779271517)
                ·
                  refine ⟨8171417028932167226819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21790445410485779271517 8171417028932167226819)
                  ·
                    rfl

theorem cell20_17903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 4, 3].length) (baseStart_17903 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_17903 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_17903 prefixEnd_17903 := by exact prefixLift 17903
  have htrace : WordTrace (prefixWord ++ tailWord_17903) baseStart_17903 baseEnd_17903 := by
    simpa [prefixWord, tailWord_17903, baseEnd_17903] using wordTrace_append hprefix tailTrace_17903
  have hstable : (prefixWord ++ tailWord_17903).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17903).length < 2 ^ (prefixWord ++ tailWord_17903).sum := by decide
  have hdescent : baseEnd_17903 < baseStart_17903 := by decide
  rcases family_descends (prefixWord ++ tailWord_17903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17926 : List Nat := [6, 2, 1, 1, 2, 1, 3, 4]
def baseStart_17926 : Nat := 118140960795 + 17926 * 2 ^ 59
def prefixEnd_17926 : Nat := 4983230072969 + 3 ^ 40 * 17926 * 2
def baseEnd_17926 : Nat := 2727304951882103153353

theorem tailTrace_17926 : CollatzResearch.WordTrace tailWord_17926 prefixEnd_17926 2727304951882103153353 := by
  unfold tailWord_17926
  simp only [CollatzResearch.WordTrace]
  refine ⟨20431716658269948817801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 435876622043092241446421 20431716658269948817801)
  ·
    refine ⟨15323787493702461613351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20431716658269948817801 15323787493702461613351)
    ·
      refine ⟨22985681240553692420027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15323787493702461613351 22985681240553692420027)
      ·
        refine ⟨34478521860830538630041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22985681240553692420027 34478521860830538630041)
        ·
          refine ⟨25858891395622903972531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34478521860830538630041 25858891395622903972531)
          ·
            refine ⟨38788337093434355958797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25858891395622903972531 38788337093434355958797)
            ·
              refine ⟨14545626410037883484549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38788337093434355958797 14545626410037883484549)
              ·
                refine ⟨2727304951882103153353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14545626410037883484549 2727304951882103153353)
                ·
                  rfl

theorem cell20_17926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_17926 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_17926 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_17926 prefixEnd_17926 := by exact prefixLift 17926
  have htrace : WordTrace (prefixWord ++ tailWord_17926) baseStart_17926 baseEnd_17926 := by
    simpa [prefixWord, tailWord_17926, baseEnd_17926] using wordTrace_append hprefix tailTrace_17926
  have hstable : (prefixWord ++ tailWord_17926).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17926).length < 2 ^ (prefixWord ++ tailWord_17926).sum := by decide
  have hdescent : baseEnd_17926 < baseStart_17926 := by decide
  rcases family_descends (prefixWord ++ tailWord_17926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17927 : List Nat := [1, 1, 4, 3, 2, 2, 1, 2, 4]
def baseStart_17927 : Nat := 118140960795 + 17927 * 2 ^ 59
def prefixEnd_17927 : Nat := 4983230072969 + 3 ^ 40 * 17927 * 2
def baseEnd_17927 : Nat := 8182371282894750426721

theorem tailTrace_17927 : CollatzResearch.WordTrace tailWord_17927 prefixEnd_17927 8182371282894750426721 := by
  unfold tailWord_17927
  simp only [CollatzResearch.WordTrace]
  refine ⟨653851406061015532956035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 435900937374010355304023 653851406061015532956035)
  ·
    refine ⟨980777109091523299434053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 653851406061015532956035 980777109091523299434053)
    ·
      refine ⟨183895707954660618643885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 980777109091523299434053 183895707954660618643885)
      ·
        refine ⟨68960890482997731991457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 183895707954660618643885 68960890482997731991457)
        ·
          refine ⟨51720667862248298993593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68960890482997731991457 51720667862248298993593)
          ·
            refine ⟨38790500896686224245195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51720667862248298993593 38790500896686224245195)
            ·
              refine ⟨58185751345029336367793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38790500896686224245195 58185751345029336367793)
              ·
                refine ⟨43639313508772002275845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58185751345029336367793 43639313508772002275845)
                ·
                  refine ⟨8182371282894750426721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43639313508772002275845 8182371282894750426721)
                  ·
                    rfl

theorem cell20_17927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 2, 4].length) (baseStart_17927 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_17927 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_17927 prefixEnd_17927 := by exact prefixLift 17927
  have htrace : WordTrace (prefixWord ++ tailWord_17927) baseStart_17927 baseEnd_17927 := by
    simpa [prefixWord, tailWord_17927, baseEnd_17927] using wordTrace_append hprefix tailTrace_17927
  have hstable : (prefixWord ++ tailWord_17927).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17927).length < 2 ^ (prefixWord ++ tailWord_17927).sum := by decide
  have hdescent : baseEnd_17927 < baseStart_17927 := by decide
  rcases family_descends (prefixWord ++ tailWord_17927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17940 : List Nat := [2, 4, 3, 1, 2, 1, 2, 3, 2]
def baseStart_17940 : Nat := 118140960795 + 17940 * 2 ^ 59
def prefixEnd_17940 : Nat := 4983230072969 + 3 ^ 40 * 17940 * 2
def baseEnd_17940 : Nat := 8188304837124482993335

theorem tailTrace_17940 : CollatzResearch.WordTrace tailWord_17940 prefixEnd_17940 8188304837124482993335 := by
  unfold tailWord_17940
  simp only [CollatzResearch.WordTrace]
  refine ⟨327162777506959376589637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 436217036675945835452849 327162777506959376589637)
  ·
    refine ⟨61343020782554883110557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 327162777506959376589637 61343020782554883110557)
    ·
      refine ⟨23003632793458081166459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61343020782554883110557 23003632793458081166459)
      ·
        refine ⟨34505449190187121749689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23003632793458081166459 34505449190187121749689)
        ·
          refine ⟨25879086892640341312267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34505449190187121749689 25879086892640341312267)
          ·
            refine ⟨38818630338960511968401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25879086892640341312267 38818630338960511968401)
            ·
              refine ⟨29113972754220383976301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38818630338960511968401 29113972754220383976301)
              ·
                refine ⟨10917739782832643991113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29113972754220383976301 10917739782832643991113)
                ·
                  refine ⟨8188304837124482993335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10917739782832643991113 8188304837124482993335)
                  ·
                    rfl

theorem cell20_17940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 3, 2].length) (baseStart_17940 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_17940 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_17940 prefixEnd_17940 := by exact prefixLift 17940
  have htrace : WordTrace (prefixWord ++ tailWord_17940) baseStart_17940 baseEnd_17940 := by
    simpa [prefixWord, tailWord_17940, baseEnd_17940] using wordTrace_append hprefix tailTrace_17940
  have hstable : (prefixWord ++ tailWord_17940).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17940).length < 2 ^ (prefixWord ++ tailWord_17940).sum := by decide
  have hdescent : baseEnd_17940 < baseStart_17940 := by decide
  rcases family_descends (prefixWord ++ tailWord_17940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17948 : List Nat := [2, 2, 3, 1, 2, 1, 1, 2, 6]
def baseStart_17948 : Nat := 118140960795 + 17948 * 2 ^ 59
def prefixEnd_17948 : Nat := 4983230072969 + 3 ^ 40 * 17948 * 2
def baseEnd_17948 : Nat := 8191956255112010726635

theorem tailTrace_17948 : CollatzResearch.WordTrace tailWord_17948 prefixEnd_17948 8191956255112010726635 := by
  unfold tailWord_17948
  simp only [CollatzResearch.WordTrace]
  refine ⟨327308669492468059735249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 436411559323290746313665 327308669492468059735249)
  ·
    refine ⟨245481502119351044801437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 327308669492468059735249 245481502119351044801437)
    ·
      refine ⟨92055563294756641800539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 245481502119351044801437 92055563294756641800539)
      ·
        refine ⟨138083344942134962700809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92055563294756641800539 138083344942134962700809)
        ·
          refine ⟨103562508706601222025607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138083344942134962700809 103562508706601222025607)
          ·
            refine ⟨155343763059901833038411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103562508706601222025607 155343763059901833038411)
            ·
              refine ⟨233015644589852749557617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 155343763059901833038411 233015644589852749557617)
              ·
                refine ⟨174761733442389562168213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 233015644589852749557617 174761733442389562168213)
                ·
                  refine ⟨8191956255112010726635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 174761733442389562168213 8191956255112010726635)
                  ·
                    rfl

theorem cell20_17948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 6].length) (baseStart_17948 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_17948 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_17948 prefixEnd_17948 := by exact prefixLift 17948
  have htrace : WordTrace (prefixWord ++ tailWord_17948) baseStart_17948 baseEnd_17948 := by
    simpa [prefixWord, tailWord_17948, baseEnd_17948] using wordTrace_append hprefix tailTrace_17948
  have hstable : (prefixWord ++ tailWord_17948).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17948).length < 2 ^ (prefixWord ++ tailWord_17948).sum := by decide
  have hdescent : baseEnd_17948 < baseStart_17948 := by decide
  rcases family_descends (prefixWord ++ tailWord_17948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17950 : List Nat := [4, 3, 3, 1, 1, 2, 1, 2, 3]
def baseStart_17950 : Nat := 118140960795 + 17950 * 2 ^ 59
def prefixEnd_17950 : Nat := 4983230072969 + 3 ^ 40 * 17950 * 2
def baseEnd_17950 : Nat := 8192869109608892659961

theorem tailTrace_17950 : CollatzResearch.WordTrace tailWord_17950 prefixEnd_17950 8192869109608892659961 := by
  unfold tailWord_17950
  simp only [CollatzResearch.WordTrace]
  refine ⟨81836285622211307630413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 436460189985126974028869 81836285622211307630413)
  ·
    refine ⟨30688607108329240361405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81836285622211307630413 30688607108329240361405)
    ·
      refine ⟨11508227665623465135527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30688607108329240361405 11508227665623465135527)
      ·
        refine ⟨17262341498435197703291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11508227665623465135527 17262341498435197703291)
        ·
          refine ⟨25893512247652796554937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17262341498435197703291 25893512247652796554937)
          ·
            refine ⟨19420134185739597416203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25893512247652796554937 19420134185739597416203)
            ·
              refine ⟨29130201278609396124305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19420134185739597416203 29130201278609396124305)
              ·
                refine ⟨21847650958957047093229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29130201278609396124305 21847650958957047093229)
                ·
                  refine ⟨8192869109608892659961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21847650958957047093229 8192869109608892659961)
                  ·
                    rfl

theorem cell20_17950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_17950 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_17950 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_17950 prefixEnd_17950 := by exact prefixLift 17950
  have htrace : WordTrace (prefixWord ++ tailWord_17950) baseStart_17950 baseEnd_17950 := by
    simpa [prefixWord, tailWord_17950, baseEnd_17950] using wordTrace_append hprefix tailTrace_17950
  have hstable : (prefixWord ++ tailWord_17950).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17950).length < 2 ^ (prefixWord ++ tailWord_17950).sum := by decide
  have hdescent : baseEnd_17950 < baseStart_17950 := by decide
  rcases family_descends (prefixWord ++ tailWord_17950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18000 : List Nat := [2, 1, 1, 1, 1, 3, 3, 1, 7]
def baseStart_18000 : Nat := 118140960795 + 18000 * 2 ^ 59
def prefixEnd_18000 : Nat := 4983230072969 + 3 ^ 40 * 18000 * 2
def baseEnd_18000 : Nat := 8215690472030940993089

theorem tailTrace_18000 : CollatzResearch.WordTrace tailWord_18000 prefixEnd_18000 8215690472030940993089 := by
  unfold tailWord_18000
  simp only [CollatzResearch.WordTrace]
  refine ⟨328256967398274500181727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 437675956531032666908969 328256967398274500181727)
  ·
    refine ⟨492385451097411750272591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 328256967398274500181727 492385451097411750272591)
    ·
      refine ⟨738578176646117625408887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 492385451097411750272591 738578176646117625408887)
      ·
        refine ⟨1107867264969176438113331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 738578176646117625408887 1107867264969176438113331)
        ·
          refine ⟨1661800897453764657169997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1107867264969176438113331 1661800897453764657169997)
          ·
            refine ⟨623175336545161746438749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1661800897453764657169997 623175336545161746438749)
            ·
              refine ⟨233690751204435654914531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 623175336545161746438749 233690751204435654914531)
              ·
                refine ⟨350536126806653482371797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 233690751204435654914531 350536126806653482371797)
                ·
                  refine ⟨8215690472030940993089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 350536126806653482371797 8215690472030940993089)
                  ·
                    rfl

theorem cell20_18000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 7].length) (baseStart_18000 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_18000 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_18000 prefixEnd_18000 := by exact prefixLift 18000
  have htrace : WordTrace (prefixWord ++ tailWord_18000) baseStart_18000 baseEnd_18000 := by
    simpa [prefixWord, tailWord_18000, baseEnd_18000] using wordTrace_append hprefix tailTrace_18000
  have hstable : (prefixWord ++ tailWord_18000).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18000).length < 2 ^ (prefixWord ++ tailWord_18000).sum := by decide
  have hdescent : baseEnd_18000 < baseStart_18000 := by decide
  rcases family_descends (prefixWord ++ tailWord_18000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18017 : List Nat := [1, 2, 3, 1, 1, 3, 2, 4, 3]
def baseStart_18017 : Nat := 118140960795 + 18017 * 2 ^ 59
def prefixEnd_18017 : Nat := 4983230072969 + 3 ^ 40 * 18017 * 2
def baseEnd_18017 : Nat := 8223449735254437426353

theorem tailTrace_18017 : CollatzResearch.WordTrace tailWord_18017 prefixEnd_18017 8223449735254437426353 := by
  unfold tailWord_18017
  simp only [CollatzResearch.WordTrace]
  refine ⟨657133975734960903732305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 438089317156640602488203 657133975734960903732305)
  ·
    refine ⟨492850481801220677799229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 657133975734960903732305 492850481801220677799229)
    ·
      refine ⟨184818930675457754174711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 492850481801220677799229 184818930675457754174711)
      ·
        refine ⟨277228396013186631262067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184818930675457754174711 277228396013186631262067)
        ·
          refine ⟨415842594019779946893101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 277228396013186631262067 415842594019779946893101)
          ·
            refine ⟨155940972757417480084913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 415842594019779946893101 155940972757417480084913)
            ·
              refine ⟨116955729568063110063685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 155940972757417480084913 116955729568063110063685)
              ·
                refine ⟨21929199294011833136941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 116955729568063110063685 21929199294011833136941)
                ·
                  refine ⟨8223449735254437426353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21929199294011833136941 8223449735254437426353)
                  ·
                    rfl

theorem cell20_18017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 4, 3].length) (baseStart_18017 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_18017 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_18017 prefixEnd_18017 := by exact prefixLift 18017
  have htrace : WordTrace (prefixWord ++ tailWord_18017) baseStart_18017 baseEnd_18017 := by
    simpa [prefixWord, tailWord_18017, baseEnd_18017] using wordTrace_append hprefix tailTrace_18017
  have hstable : (prefixWord ++ tailWord_18017).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18017).length < 2 ^ (prefixWord ++ tailWord_18017).sum := by decide
  have hdescent : baseEnd_18017 < baseStart_18017 := by decide
  rcases family_descends (prefixWord ++ tailWord_18017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18030 : List Nat := [4, 1, 2, 2, 3, 2, 2, 1, 3]
def baseStart_18030 : Nat := 118140960795 + 18030 * 2 ^ 59
def prefixEnd_18030 : Nat := 4983230072969 + 3 ^ 40 * 18030 * 2
def baseEnd_18030 : Nat := 8229383289484169992967

theorem tailTrace_18030 : CollatzResearch.WordTrace tailWord_18030 prefixEnd_18030 8229383289484169992967 := by
  unfold tailWord_18030
  simp only [CollatzResearch.WordTrace]
  refine ⟨82201015585983015494443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 438405416458576082637029 82201015585983015494443)
  ·
    refine ⟨123301523378974523241665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82201015585983015494443 123301523378974523241665)
    ·
      refine ⟨92476142534230892431249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123301523378974523241665 92476142534230892431249)
      ·
        refine ⟨69357106900673169323437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92476142534230892431249 69357106900673169323437)
        ·
          refine ⟨26008915087752438496289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69357106900673169323437 26008915087752438496289)
          ·
            refine ⟨19506686315814328872217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26008915087752438496289 19506686315814328872217)
            ·
              refine ⟨14630014736860746654163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19506686315814328872217 14630014736860746654163)
              ·
                refine ⟨21945022105291119981245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14630014736860746654163 21945022105291119981245)
                ·
                  refine ⟨8229383289484169992967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21945022105291119981245 8229383289484169992967)
                  ·
                    rfl

theorem cell20_18030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 2, 1, 3].length) (baseStart_18030 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_18030 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_18030 prefixEnd_18030 := by exact prefixLift 18030
  have htrace : WordTrace (prefixWord ++ tailWord_18030) baseStart_18030 baseEnd_18030 := by
    simpa [prefixWord, tailWord_18030, baseEnd_18030] using wordTrace_append hprefix tailTrace_18030
  have hstable : (prefixWord ++ tailWord_18030).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18030).length < 2 ^ (prefixWord ++ tailWord_18030).sum := by decide
  have hdescent : baseEnd_18030 < baseStart_18030 := by decide
  rcases family_descends (prefixWord ++ tailWord_18030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18034 : List Nat := [3, 2, 1, 2, 3, 2, 1, 3, 3]
def baseStart_18034 : Nat := 118140960795 + 18034 * 2 ^ 59
def prefixEnd_18034 : Nat := 4983230072969 + 3 ^ 40 * 18034 * 2
def baseEnd_18034 : Nat := 8231208998477933859617

theorem tailTrace_18034 : CollatzResearch.WordTrace tailWord_18034 prefixEnd_18034 8231208998477933859617 := by
  unfold tailWord_18034
  simp only [CollatzResearch.WordTrace]
  refine ⟨164438504168343201775289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 438502677782248538067437 164438504168343201775289)
  ·
    refine ⟨123328878126257401331467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164438504168343201775289 123328878126257401331467)
    ·
      refine ⟨184993317189386101997201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123328878126257401331467 184993317189386101997201)
      ·
        refine ⟨138744987892039576497901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 184993317189386101997201 138744987892039576497901)
        ·
          refine ⟨52029370459514841186713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 138744987892039576497901 52029370459514841186713)
          ·
            refine ⟨39022027844636130890035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52029370459514841186713 39022027844636130890035)
            ·
              refine ⟨58533041766954196335053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39022027844636130890035 58533041766954196335053)
              ·
                refine ⟨21949890662607823625645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58533041766954196335053 21949890662607823625645)
                ·
                  refine ⟨8231208998477933859617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21949890662607823625645 8231208998477933859617)
                  ·
                    rfl

theorem cell20_18034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 3, 3].length) (baseStart_18034 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_18034 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_18034 prefixEnd_18034 := by exact prefixLift 18034
  have htrace : WordTrace (prefixWord ++ tailWord_18034) baseStart_18034 baseEnd_18034 := by
    simpa [prefixWord, tailWord_18034, baseEnd_18034] using wordTrace_append hprefix tailTrace_18034
  have hstable : (prefixWord ++ tailWord_18034).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18034).length < 2 ^ (prefixWord ++ tailWord_18034).sum := by decide
  have hdescent : baseEnd_18034 < baseStart_18034 := by decide
  rcases family_descends (prefixWord ++ tailWord_18034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18072 : List Nat := [2, 1, 2, 4, 1, 3, 2, 2, 3]
def baseStart_18072 : Nat := 118140960795 + 18072 * 2 ^ 59
def prefixEnd_18072 : Nat := 4983230072969 + 3 ^ 40 * 18072 * 2
def baseEnd_18072 : Nat := 8248553233918690592795

theorem tailTrace_18072 : CollatzResearch.WordTrace tailWord_18072 prefixEnd_18072 8248553233918690592795 := by
  unfold tailWord_18072
  simp only [CollatzResearch.WordTrace]
  refine ⟨329569995267852648492235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 439426660357136864656313 329569995267852648492235)
  ·
    refine ⟨494354992901778972738353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 329569995267852648492235 494354992901778972738353)
    ·
      refine ⟨370766244676334229553765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 494354992901778972738353 370766244676334229553765)
      ·
        refine ⟨69518670876812668041331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 370766244676334229553765 69518670876812668041331)
        ·
          refine ⟨104278006315219002061997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69518670876812668041331 104278006315219002061997)
          ·
            refine ⟨39104252368207125773249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 104278006315219002061997 39104252368207125773249)
            ·
              refine ⟨29328189276155344329937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39104252368207125773249 29328189276155344329937)
              ·
                refine ⟨21996141957116508247453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29328189276155344329937 21996141957116508247453)
                ·
                  refine ⟨8248553233918690592795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21996141957116508247453 8248553233918690592795)
                  ·
                    rfl

theorem cell20_18072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 2, 3].length) (baseStart_18072 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_18072 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_18072 prefixEnd_18072 := by exact prefixLift 18072
  have htrace : WordTrace (prefixWord ++ tailWord_18072) baseStart_18072 baseEnd_18072 := by
    simpa [prefixWord, tailWord_18072, baseEnd_18072] using wordTrace_append hprefix tailTrace_18072
  have hstable : (prefixWord ++ tailWord_18072).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18072).length < 2 ^ (prefixWord ++ tailWord_18072).sum := by decide
  have hdescent : baseEnd_18072 < baseStart_18072 := by decide
  rcases family_descends (prefixWord ++ tailWord_18072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18082 : List Nat := [3, 3, 1, 4, 1, 2, 1, 5]
def baseStart_18082 : Nat := 118140960795 + 18082 * 2 ^ 59
def prefixEnd_18082 : Nat := 4983230072969 + 3 ^ 40 * 18082 * 2
def baseEnd_18082 : Nat := 2751039168801033419807

theorem tailTrace_18082 : CollatzResearch.WordTrace tailWord_18082 prefixEnd_18082 2751039168801033419807 := by
  unfold tailWord_18082
  simp only [CollatzResearch.WordTrace]
  refine ⟨164876180124869251212125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 439669813666318003232333 164876180124869251212125)
  ·
    refine ⟨61828567546825969204547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 164876180124869251212125 61828567546825969204547)
    ·
      refine ⟨92742851320238953806821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61828567546825969204547 92742851320238953806821)
      ·
        refine ⟨17389284622544803838779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92742851320238953806821 17389284622544803838779)
        ·
          refine ⟨26083926933817205758169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17389284622544803838779 26083926933817205758169)
          ·
            refine ⟨19562945200362904318627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26083926933817205758169 19562945200362904318627)
            ·
              refine ⟨29344417800544356477941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19562945200362904318627 29344417800544356477941)
              ·
                refine ⟨2751039168801033419807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29344417800544356477941 2751039168801033419807)
                ·
                  rfl

theorem cell20_18082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 5].length) (baseStart_18082 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_18082 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_18082 prefixEnd_18082 := by exact prefixLift 18082
  have htrace : WordTrace (prefixWord ++ tailWord_18082) baseStart_18082 baseEnd_18082 := by
    simpa [prefixWord, tailWord_18082, baseEnd_18082] using wordTrace_append hprefix tailTrace_18082
  have hstable : (prefixWord ++ tailWord_18082).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18082).length < 2 ^ (prefixWord ++ tailWord_18082).sum := by decide
  have hdescent : baseEnd_18082 < baseStart_18082 := by decide
  rcases family_descends (prefixWord ++ tailWord_18082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18124 : List Nat := [2, 2, 1, 5, 2, 1, 7]
def baseStart_18124 : Nat := 118140960795 + 18124 * 2 ^ 59
def prefixEnd_18124 : Nat := 4983230072969 + 3 ^ 40 * 18124 * 2
def baseEnd_18124 : Nat := 919143050093068984361

theorem tailTrace_18124 : CollatzResearch.WordTrace tailWord_18124 prefixEnd_18124 919143050093068984361 := by
  unfold tailWord_18124
  simp only [CollatzResearch.WordTrace]
  refine ⟨330518293173659088938713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 440691057564878785251617 330518293173659088938713)
  ·
    refine ⟨247888719880244316704035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 330518293173659088938713 247888719880244316704035)
    ·
      refine ⟨371833079820366475056053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247888719880244316704035 371833079820366475056053)
      ·
        refine ⟨34859351233159357036505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 371833079820366475056053 34859351233159357036505)
        ·
          refine ⟨26144513424869517777379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34859351233159357036505 26144513424869517777379)
          ·
            refine ⟨39216770137304276666069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26144513424869517777379 39216770137304276666069)
            ·
              refine ⟨919143050093068984361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 39216770137304276666069 919143050093068984361)
              ·
                rfl

theorem cell20_18124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 7].length) (baseStart_18124 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_18124 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_18124 prefixEnd_18124 := by exact prefixLift 18124
  have htrace : WordTrace (prefixWord ++ tailWord_18124) baseStart_18124 baseEnd_18124 := by
    simpa [prefixWord, tailWord_18124, baseEnd_18124] using wordTrace_append hprefix tailTrace_18124
  have hstable : (prefixWord ++ tailWord_18124).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18124).length < 2 ^ (prefixWord ++ tailWord_18124).sum := by decide
  have hdescent : baseEnd_18124 < baseStart_18124 := by decide
  rcases family_descends (prefixWord ++ tailWord_18124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18138 : List Nat := [3, 1, 1, 2, 2, 3, 1, 3, 4]
def baseStart_18138 : Nat := 118140960795 + 18138 * 2 ^ 59
def prefixEnd_18138 : Nat := 4983230072969 + 3 ^ 40 * 18138 * 2
def baseEnd_18138 : Nat := 8278677432315794392525

theorem tailTrace_18138 : CollatzResearch.WordTrace tailWord_18138 prefixEnd_18138 8278677432315794392525 := by
  unfold tailWord_18138
  simp only [CollatzResearch.WordTrace]
  refine ⟨165386802074149642221767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 441031472197732379258045 165386802074149642221767)
  ·
    refine ⟨248080203111224463332651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165386802074149642221767 248080203111224463332651)
    ·
      refine ⟨372120304666836694998977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248080203111224463332651 372120304666836694998977)
      ·
        refine ⟨279090228500127521249233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 372120304666836694998977 279090228500127521249233)
        ·
          refine ⟨209317671375095640936925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 279090228500127521249233 209317671375095640936925)
          ·
            refine ⟨78494126765660865351347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 209317671375095640936925 78494126765660865351347)
            ·
              refine ⟨117741190148491298027021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78494126765660865351347 117741190148491298027021)
              ·
                refine ⟨44152946305684236760133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 117741190148491298027021 44152946305684236760133)
                ·
                  refine ⟨8278677432315794392525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44152946305684236760133 8278677432315794392525)
                  ·
                    rfl

theorem cell20_18138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 3, 4].length) (baseStart_18138 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_18138 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_18138 prefixEnd_18138 := by exact prefixLift 18138
  have htrace : WordTrace (prefixWord ++ tailWord_18138) baseStart_18138 baseEnd_18138 := by
    simpa [prefixWord, tailWord_18138, baseEnd_18138] using wordTrace_append hprefix tailTrace_18138
  have hstable : (prefixWord ++ tailWord_18138).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18138).length < 2 ^ (prefixWord ++ tailWord_18138).sum := by decide
  have hdescent : baseEnd_18138 < baseStart_18138 := by decide
  rcases family_descends (prefixWord ++ tailWord_18138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18148 : List Nat := [2, 3, 1, 1, 1, 3, 5, 1, 3]
def baseStart_18148 : Nat := 118140960795 + 18148 * 2 ^ 59
def prefixEnd_18148 : Nat := 4983230072969 + 3 ^ 40 * 18148 * 2
def baseEnd_18148 : Nat := 8283241704800204059151

theorem tailTrace_18148 : CollatzResearch.WordTrace tailWord_18148 prefixEnd_18148 8283241704800204059151 := by
  unfold tailWord_18148
  simp only [CollatzResearch.WordTrace]
  refine ⟨330955969130185138375549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 441274625506913517834065 330955969130185138375549)
  ·
    refine ⟨124108488423819426890831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 330955969130185138375549 124108488423819426890831)
    ·
      refine ⟨186162732635729140336247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124108488423819426890831 186162732635729140336247)
      ·
        refine ⟨279244098953593710504371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186162732635729140336247 279244098953593710504371)
        ·
          refine ⟨418866148430390565756557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 279244098953593710504371 418866148430390565756557)
          ·
            refine ⟨157074805661396462158709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 418866148430390565756557 157074805661396462158709)
            ·
              refine ⟨14725763030755918327379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 157074805661396462158709 14725763030755918327379)
              ·
                refine ⟨22088644546133877491069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14725763030755918327379 22088644546133877491069)
                ·
                  refine ⟨8283241704800204059151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22088644546133877491069 8283241704800204059151)
                  ·
                    rfl

theorem cell20_18148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 5, 1, 3].length) (baseStart_18148 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_18148 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_18148 prefixEnd_18148 := by exact prefixLift 18148
  have htrace : WordTrace (prefixWord ++ tailWord_18148) baseStart_18148 baseEnd_18148 := by
    simpa [prefixWord, tailWord_18148, baseEnd_18148] using wordTrace_append hprefix tailTrace_18148
  have hstable : (prefixWord ++ tailWord_18148).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18148).length < 2 ^ (prefixWord ++ tailWord_18148).sum := by decide
  have hdescent : baseEnd_18148 < baseStart_18148 := by decide
  rcases family_descends (prefixWord ++ tailWord_18148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18207 : List Nat := [1, 1, 2, 4, 2, 1, 3, 3, 3]
def baseStart_18207 : Nat := 118140960795 + 18207 * 2 ^ 59
def prefixEnd_18207 : Nat := 4983230072969 + 3 ^ 40 * 18207 * 2
def baseEnd_18207 : Nat := 8310170912458221092243

theorem tailTrace_18207 : CollatzResearch.WordTrace tailWord_18207 prefixEnd_18207 8310170912458221092243 := by
  unfold tailWord_18207
  simp only [CollatzResearch.WordTrace]
  refine ⟨664063845046623353148875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 442709230031082235432583 664063845046623353148875)
  ·
    refine ⟨996095767569935029723313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 664063845046623353148875 996095767569935029723313)
    ·
      refine ⟨747071825677451272292485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 996095767569935029723313 747071825677451272292485)
      ·
        refine ⟨140075967314522113554841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 747071825677451272292485 140075967314522113554841)
        ·
          refine ⟨105056975485891585166131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140075967314522113554841 105056975485891585166131)
          ·
            refine ⟨157585463228837377749197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105056975485891585166131 157585463228837377749197)
            ·
              refine ⟨59094548710814016655949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 157585463228837377749197 59094548710814016655949)
              ·
                refine ⟨22160455766555256245981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59094548710814016655949 22160455766555256245981)
                ·
                  refine ⟨8310170912458221092243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22160455766555256245981 8310170912458221092243)
                  ·
                    rfl

theorem cell20_18207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 3, 3].length) (baseStart_18207 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_18207 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_18207 prefixEnd_18207 := by exact prefixLift 18207
  have htrace : WordTrace (prefixWord ++ tailWord_18207) baseStart_18207 baseEnd_18207 := by
    simpa [prefixWord, tailWord_18207, baseEnd_18207] using wordTrace_append hprefix tailTrace_18207
  have hstable : (prefixWord ++ tailWord_18207).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18207).length < 2 ^ (prefixWord ++ tailWord_18207).sum := by decide
  have hdescent : baseEnd_18207 < baseStart_18207 := by decide
  rcases family_descends (prefixWord ++ tailWord_18207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18245 : List Nat := [1, 3, 1, 1, 1, 2, 6, 2, 3]
def baseStart_18245 : Nat := 118140960795 + 18245 * 2 ^ 59
def prefixEnd_18245 : Nat := 4983230072969 + 3 ^ 40 * 18245 * 2
def baseEnd_18245 : Nat := 8327515147898977825421

theorem tailTrace_18245 : CollatzResearch.WordTrace tailWord_18245 prefixEnd_18245 8327515147898977825421 := by
  unfold tailWord_18245
  simp only [CollatzResearch.WordTrace]
  refine ⟨665449818908955843032189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 443633212605970562021459 665449818908955843032189)
  ·
    refine ⟨249543682090858441137071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 665449818908955843032189 249543682090858441137071)
    ·
      refine ⟨374315523136287661705607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249543682090858441137071 374315523136287661705607)
      ·
        refine ⟨561473284704431492558411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 374315523136287661705607 561473284704431492558411)
        ·
          refine ⟨842209927056647238837617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 561473284704431492558411 842209927056647238837617)
          ·
            refine ⟨631657445292485429128213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 842209927056647238837617 631657445292485429128213)
            ·
              refine ⟨29608942748085254490385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 631657445292485429128213 29608942748085254490385)
              ·
                refine ⟨22206707061063940867789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29608942748085254490385 22206707061063940867789)
                ·
                  refine ⟨8327515147898977825421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22206707061063940867789 8327515147898977825421)
                  ·
                    rfl

theorem cell20_18245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 2, 3].length) (baseStart_18245 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_18245 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_18245 prefixEnd_18245 := by exact prefixLift 18245
  have htrace : WordTrace (prefixWord ++ tailWord_18245) baseStart_18245 baseEnd_18245 := by
    simpa [prefixWord, tailWord_18245, baseEnd_18245] using wordTrace_append hprefix tailTrace_18245
  have hstable : (prefixWord ++ tailWord_18245).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18245).length < 2 ^ (prefixWord ++ tailWord_18245).sum := by decide
  have hdescent : baseEnd_18245 < baseStart_18245 := by decide
  rcases family_descends (prefixWord ++ tailWord_18245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18248 : List Nat := [2, 1, 3, 1, 1, 4, 4, 2, 2]
def baseStart_18248 : Nat := 118140960795 + 18248 * 2 ^ 59
def prefixEnd_18248 : Nat := 4983230072969 + 3 ^ 40 * 18248 * 2
def baseEnd_18248 : Nat := 8328884429644300725409

theorem tailTrace_18248 : CollatzResearch.WordTrace tailWord_18248 prefixEnd_18248 8328884429644300725409 := by
  unfold tailWord_18248
  simp only [CollatzResearch.WordTrace]
  refine ⟨332779618949043677695699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 443706158598724903594265 332779618949043677695699)
  ·
    refine ⟨499169428423565516543549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 332779618949043677695699 499169428423565516543549)
    ·
      refine ⟨187188535658837068703831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 499169428423565516543549 187188535658837068703831)
      ·
        refine ⟨280782803488255603055747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187188535658837068703831 280782803488255603055747)
        ·
          refine ⟨421174205232383404583621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 280782803488255603055747 421174205232383404583621)
          ·
            refine ⟨78970163481071888359429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 421174205232383404583621 78970163481071888359429)
            ·
              refine ⟨14806905652700979067393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 78970163481071888359429 14806905652700979067393)
              ·
                refine ⟨11105179239525734300545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14806905652700979067393 11105179239525734300545)
                ·
                  refine ⟨8328884429644300725409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11105179239525734300545 8328884429644300725409)
                  ·
                    rfl

theorem cell20_18248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 4, 2, 2].length) (baseStart_18248 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_18248 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_18248 prefixEnd_18248 := by exact prefixLift 18248
  have htrace : WordTrace (prefixWord ++ tailWord_18248) baseStart_18248 baseEnd_18248 := by
    simpa [prefixWord, tailWord_18248, baseEnd_18248] using wordTrace_append hprefix tailTrace_18248
  have hstable : (prefixWord ++ tailWord_18248).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18248).length < 2 ^ (prefixWord ++ tailWord_18248).sum := by decide
  have hdescent : baseEnd_18248 < baseStart_18248 := by decide
  rcases family_descends (prefixWord ++ tailWord_18248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18286 : List Nat := [4, 1, 2, 3, 1, 1, 1, 5, 2]
def baseStart_18286 : Nat := 118140960795 + 18286 * 2 ^ 59
def prefixEnd_18286 : Nat := 4983230072969 + 3 ^ 40 * 18286 * 2
def baseEnd_18286 : Nat := 8346228665085057458587

theorem tailTrace_18286 : CollatzResearch.WordTrace tailWord_18286 prefixEnd_18286 8346228665085057458587 := by
  unfold tailWord_18286
  simp only [CollatzResearch.WordTrace]
  refine ⟨83368151470052480659339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 444630141173613230183141 83368151470052480659339)
  ·
    refine ⟨125052227205078720989009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83368151470052480659339 125052227205078720989009)
    ·
      refine ⟨93789170403809040741757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125052227205078720989009 93789170403809040741757)
      ·
        refine ⟨35170938901428390278159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93789170403809040741757 35170938901428390278159)
        ·
          refine ⟨52756408352142585417239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35170938901428390278159 52756408352142585417239)
          ·
            refine ⟨79134612528213878125859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52756408352142585417239 79134612528213878125859)
            ·
              refine ⟨118701918792320817188789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79134612528213878125859 118701918792320817188789)
              ·
                refine ⟨11128304886780076611449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 118701918792320817188789 11128304886780076611449)
                ·
                  refine ⟨8346228665085057458587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11128304886780076611449 8346228665085057458587)
                  ·
                    rfl

theorem cell20_18286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 5, 2].length) (baseStart_18286 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_18286 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_18286 prefixEnd_18286 := by exact prefixLift 18286
  have htrace : WordTrace (prefixWord ++ tailWord_18286) baseStart_18286 baseEnd_18286 := by
    simpa [prefixWord, tailWord_18286, baseEnd_18286] using wordTrace_append hprefix tailTrace_18286
  have hstable : (prefixWord ++ tailWord_18286).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18286).length < 2 ^ (prefixWord ++ tailWord_18286).sum := by decide
  have hdescent : baseEnd_18286 < baseStart_18286 := by decide
  rcases family_descends (prefixWord ++ tailWord_18286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18304 : List Nat := [2, 1, 1, 2, 1, 2, 5, 1, 5]
def baseStart_18304 : Nat := 118140960795 + 18304 * 2 ^ 59
def prefixEnd_18304 : Nat := 4983230072969 + 3 ^ 40 * 18304 * 2
def baseEnd_18304 : Nat := 8354444355556994858513

theorem tailTrace_18304 : CollatzResearch.WordTrace tailWord_18304 prefixEnd_18304 8354444355556994858513 := by
  unfold tailWord_18304
  simp only [CollatzResearch.WordTrace]
  refine ⟨333800862847604459714983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 445067817130139279619977 333800862847604459714983)
  ·
    refine ⟨500701294271406689572475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 333800862847604459714983 500701294271406689572475)
    ·
      refine ⟨751051941407110034358713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 500701294271406689572475 751051941407110034358713)
      ·
        refine ⟨563288956055332525769035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 751051941407110034358713 563288956055332525769035)
        ·
          refine ⟨844933434082998788653553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 563288956055332525769035 844933434082998788653553)
          ·
            refine ⟨633700075562249091490165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 844933434082998788653553 633700075562249091490165)
            ·
              refine ⟨59409382083960852327203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 633700075562249091490165 59409382083960852327203)
              ·
                refine ⟨89114073125941278490805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59409382083960852327203 89114073125941278490805)
                ·
                  refine ⟨8354444355556994858513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 89114073125941278490805 8354444355556994858513)
                  ·
                    rfl

theorem cell20_18304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 1, 5].length) (baseStart_18304 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_18304 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_18304 prefixEnd_18304 := by exact prefixLift 18304
  have htrace : WordTrace (prefixWord ++ tailWord_18304) baseStart_18304 baseEnd_18304 := by
    simpa [prefixWord, tailWord_18304, baseEnd_18304] using wordTrace_append hprefix tailTrace_18304
  have hstable : (prefixWord ++ tailWord_18304).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18304).length < 2 ^ (prefixWord ++ tailWord_18304).sum := by decide
  have hdescent : baseEnd_18304 < baseStart_18304 := by decide
  rcases family_descends (prefixWord ++ tailWord_18304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18307 : List Nat := [1, 1, 1, 3, 4, 2, 2, 4, 2]
def baseStart_18307 : Nat := 118140960795 + 18307 * 2 ^ 59
def prefixEnd_18307 : Nat := 4983230072969 + 3 ^ 40 * 18307 * 2
def baseEnd_18307 : Nat := 8355813637302317758501

theorem tailTrace_18307 : CollatzResearch.WordTrace tailWord_18307 prefixEnd_18307 8355813637302317758501 := by
  unfold tailWord_18307
  simp only [CollatzResearch.WordTrace]
  refine ⟨667711144684340431789175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 445140763122893621192783 667711144684340431789175)
  ·
    refine ⟨1001566717026510647683763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 667711144684340431789175 1001566717026510647683763)
    ·
      refine ⟨1502350075539765971525645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1001566717026510647683763 1502350075539765971525645)
      ·
        refine ⟨563381278327412239322117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1502350075539765971525645 563381278327412239322117)
        ·
          refine ⟨105633989686389794872897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 563381278327412239322117 105633989686389794872897)
          ·
            refine ⟨79225492264792346154673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105633989686389794872897 79225492264792346154673)
            ·
              refine ⟨59419119198594259616005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79225492264792346154673 59419119198594259616005)
              ·
                refine ⟨11141084849736423678001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59419119198594259616005 11141084849736423678001)
                ·
                  refine ⟨8355813637302317758501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11141084849736423678001 8355813637302317758501)
                  ·
                    rfl

theorem cell20_18307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 4, 2].length) (baseStart_18307 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_18307 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_18307 prefixEnd_18307 := by exact prefixLift 18307
  have htrace : WordTrace (prefixWord ++ tailWord_18307) baseStart_18307 baseEnd_18307 := by
    simpa [prefixWord, tailWord_18307, baseEnd_18307] using wordTrace_append hprefix tailTrace_18307
  have hstable : (prefixWord ++ tailWord_18307).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18307).length < 2 ^ (prefixWord ++ tailWord_18307).sum := by decide
  have hdescent : baseEnd_18307 < baseStart_18307 := by decide
  rcases family_descends (prefixWord ++ tailWord_18307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18376 : List Nat := [2, 1, 3, 1, 4, 1, 4, 1, 3]
def baseStart_18376 : Nat := 118140960795 + 18376 * 2 ^ 59
def prefixEnd_18376 : Nat := 4983230072969 + 3 ^ 40 * 18376 * 2
def baseEnd_18376 : Nat := 8387307117444744458219

theorem tailTrace_18376 : CollatzResearch.WordTrace tailWord_18376 prefixEnd_18376 8387307117444744458219 := by
  unfold tailWord_18376
  simp only [CollatzResearch.WordTrace]
  refine ⟨335113890717182608025491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 446818520956243477367321 335113890717182608025491)
  ·
    refine ⟨502670836075773912038237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 335113890717182608025491 502670836075773912038237)
    ·
      refine ⟨188501563528415217014339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 502670836075773912038237 188501563528415217014339)
      ·
        refine ⟨282752345292622825521509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188501563528415217014339 282752345292622825521509)
        ·
          refine ⟨53016064742366779785283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 282752345292622825521509 53016064742366779785283)
          ·
            refine ⟨79524097113550169677925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53016064742366779785283 79524097113550169677925)
            ·
              refine ⟨14910768208790656814611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 79524097113550169677925 14910768208790656814611)
              ·
                refine ⟨22366152313185985221917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14910768208790656814611 22366152313185985221917)
                ·
                  refine ⟨8387307117444744458219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22366152313185985221917 8387307117444744458219)
                  ·
                    rfl

theorem cell20_18376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 4, 1, 3].length) (baseStart_18376 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_18376 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_18376 prefixEnd_18376 := by exact prefixLift 18376
  have htrace : WordTrace (prefixWord ++ tailWord_18376) baseStart_18376 baseEnd_18376 := by
    simpa [prefixWord, tailWord_18376, baseEnd_18376] using wordTrace_append hprefix tailTrace_18376
  have hstable : (prefixWord ++ tailWord_18376).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18376).length < 2 ^ (prefixWord ++ tailWord_18376).sum := by decide
  have hdescent : baseEnd_18376 < baseStart_18376 := by decide
  rcases family_descends (prefixWord ++ tailWord_18376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18413 : List Nat := [1, 5, 1, 4, 2, 1, 2, 2, 2]
def baseStart_18413 : Nat := 118140960795 + 18413 * 2 ^ 59
def prefixEnd_18413 : Nat := 4983230072969 + 3 ^ 40 * 18413 * 2
def baseEnd_18413 : Nat := 8404194925637060224735

theorem tailTrace_18413 : CollatzResearch.WordTrace tailWord_18413 prefixEnd_18413 8404194925637060224735 := by
  unfold tailWord_18413
  simp only [CollatzResearch.WordTrace]
  refine ⟨671577282300320535147893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 447718188200213690098595 671577282300320535147893)
  ·
    refine ⟨62960370215655050170115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 671577282300320535147893 62960370215655050170115)
    ·
      refine ⟨94440555323482575255173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62960370215655050170115 94440555323482575255173)
      ·
        refine ⟨17707604123152982860345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 94440555323482575255173 17707604123152982860345)
        ·
          refine ⟨13280703092364737145259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17707604123152982860345 13280703092364737145259)
          ·
            refine ⟨19921054638547105717889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13280703092364737145259 19921054638547105717889)
            ·
              refine ⟨14940790978910329288417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19921054638547105717889 14940790978910329288417)
              ·
                refine ⟨11205593234182746966313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14940790978910329288417 11205593234182746966313)
                ·
                  refine ⟨8404194925637060224735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11205593234182746966313 8404194925637060224735)
                  ·
                    rfl

theorem cell20_18413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 2, 2, 2].length) (baseStart_18413 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_18413 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_18413 prefixEnd_18413 := by exact prefixLift 18413
  have htrace : WordTrace (prefixWord ++ tailWord_18413) baseStart_18413 baseEnd_18413 := by
    simpa [prefixWord, tailWord_18413, baseEnd_18413] using wordTrace_append hprefix tailTrace_18413
  have hstable : (prefixWord ++ tailWord_18413).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18413).length < 2 ^ (prefixWord ++ tailWord_18413).sum := by decide
  have hdescent : baseEnd_18413 < baseStart_18413 := by decide
  rcases family_descends (prefixWord ++ tailWord_18413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18414 : List Nat := [4, 1, 2, 1, 3, 2, 2, 2, 3]
def baseStart_18414 : Nat := 118140960795 + 18414 * 2 ^ 59
def prefixEnd_18414 : Nat := 4983230072969 + 3 ^ 40 * 18414 * 2
def baseEnd_18414 : Nat := 8404651352885501191397

theorem tailTrace_18414 : CollatzResearch.WordTrace tailWord_18414 prefixEnd_18414 8404651352885501191397 := by
  unfold tailWord_18414
  simp only [CollatzResearch.WordTrace]
  refine ⟨83951719412087213241787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 447742503531131803956197 83951719412087213241787)
  ·
    refine ⟨125927579118130819862681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83951719412087213241787 125927579118130819862681)
    ·
      refine ⟨94445684338598114897011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125927579118130819862681 94445684338598114897011)
      ·
        refine ⟨141668526507897172345517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94445684338598114897011 141668526507897172345517)
        ·
          refine ⟨53125697440461439629569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 141668526507897172345517 53125697440461439629569)
          ·
            refine ⟨39844273080346079722177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53125697440461439629569 39844273080346079722177)
            ·
              refine ⟨29883204810259559791633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39844273080346079722177 29883204810259559791633)
              ·
                refine ⟨22412403607694669843725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29883204810259559791633 22412403607694669843725)
                ·
                  refine ⟨8404651352885501191397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22412403607694669843725 8404651352885501191397)
                  ·
                    rfl

theorem cell20_18414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 2, 3].length) (baseStart_18414 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_18414 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_18414 prefixEnd_18414 := by exact prefixLift 18414
  have htrace : WordTrace (prefixWord ++ tailWord_18414) baseStart_18414 baseEnd_18414 := by
    simpa [prefixWord, tailWord_18414, baseEnd_18414] using wordTrace_append hprefix tailTrace_18414
  have hstable : (prefixWord ++ tailWord_18414).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18414).length < 2 ^ (prefixWord ++ tailWord_18414).sum := by decide
  have hdescent : baseEnd_18414 < baseStart_18414 := by decide
  rcases family_descends (prefixWord ++ tailWord_18414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18417 : List Nat := [1, 2, 2, 2, 5, 2, 2, 2, 2]
def baseStart_18417 : Nat := 118140960795 + 18417 * 2 ^ 59
def prefixEnd_18417 : Nat := 4983230072969 + 3 ^ 40 * 18417 * 2
def baseEnd_18417 : Nat := 8406020634630824091385

theorem tailTrace_18417 : CollatzResearch.WordTrace tailWord_18417 prefixEnd_18417 8406020634630824091385 := by
  unfold tailWord_18417
  simp only [CollatzResearch.WordTrace]
  refine ⟨671723174285829218293505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 447815449523886145529003 671723174285829218293505)
  ·
    refine ⟨503792380714371913720129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 671723174285829218293505 503792380714371913720129)
    ·
      refine ⟨377844285535778935290097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 503792380714371913720129 377844285535778935290097)
      ·
        refine ⟨283383214151834201467573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 377844285535778935290097 283383214151834201467573)
        ·
          refine ⟨26567176326734456387585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 283383214151834201467573 26567176326734456387585)
          ·
            refine ⟨19925382245050842290689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26567176326734456387585 19925382245050842290689)
            ·
              refine ⟨14944036683788131718017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19925382245050842290689 14944036683788131718017)
              ·
                refine ⟨11208027512841098788513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14944036683788131718017 11208027512841098788513)
                ·
                  refine ⟨8406020634630824091385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11208027512841098788513 8406020634630824091385)
                  ·
                    rfl

theorem cell20_18417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 2, 2, 2].length) (baseStart_18417 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_18417 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_18417 prefixEnd_18417 := by exact prefixLift 18417
  have htrace : WordTrace (prefixWord ++ tailWord_18417) baseStart_18417 baseEnd_18417 := by
    simpa [prefixWord, tailWord_18417, baseEnd_18417] using wordTrace_append hprefix tailTrace_18417
  have hstable : (prefixWord ++ tailWord_18417).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18417).length < 2 ^ (prefixWord ++ tailWord_18417).sum := by decide
  have hdescent : baseEnd_18417 < baseStart_18417 := by decide
  rcases family_descends (prefixWord ++ tailWord_18417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18432 : List Nat := [2, 1, 1, 2, 1, 1, 1, 11]
def baseStart_18432 : Nat := 118140960795 + 18432 * 2 ^ 59
def prefixEnd_18432 : Nat := 4983230072969 + 3 ^ 40 * 18432 * 2
def baseEnd_18432 : Nat := 2804289014452479530441

theorem tailTrace_18432 : CollatzResearch.WordTrace tailWord_18432 prefixEnd_18432 2804289014452479530441 := by
  unfold tailWord_18432
  simp only [CollatzResearch.WordTrace]
  refine ⟨336135134615743390044775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 448180179487657853393033 336135134615743390044775)
  ·
    refine ⟨504202701923615085067163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 336135134615743390044775 504202701923615085067163)
    ·
      refine ⟨756304052885422627600745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 504202701923615085067163 756304052885422627600745)
      ·
        refine ⟨567228039664066970700559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 756304052885422627600745 567228039664066970700559)
        ·
          refine ⟨850842059496100456050839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 567228039664066970700559 850842059496100456050839)
          ·
            refine ⟨1276263089244150684076259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 850842059496100456050839 1276263089244150684076259)
            ·
              refine ⟨1914394633866226026114389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1276263089244150684076259 1914394633866226026114389)
              ·
                refine ⟨2804289014452479530441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 1914394633866226026114389 2804289014452479530441)
                ·
                  rfl

theorem cell20_18432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 11].length) (baseStart_18432 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_18432 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_18432 prefixEnd_18432 := by exact prefixLift 18432
  have htrace : WordTrace (prefixWord ++ tailWord_18432) baseStart_18432 baseEnd_18432 := by
    simpa [prefixWord, tailWord_18432, baseEnd_18432] using wordTrace_append hprefix tailTrace_18432
  have hstable : (prefixWord ++ tailWord_18432).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18432).length < 2 ^ (prefixWord ++ tailWord_18432).sum := by decide
  have hdescent : baseEnd_18432 < baseStart_18432 := by decide
  rcases family_descends (prefixWord ++ tailWord_18432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18456 : List Nat := [2, 1, 2, 3, 2, 1, 2, 2, 5]
def baseStart_18456 : Nat := 118140960795 + 18456 * 2 ^ 59
def prefixEnd_18456 : Nat := 4983230072969 + 3 ^ 40 * 18456 * 2
def baseEnd_18456 : Nat := 8423821297320021791225

theorem tailTrace_18456 : CollatzResearch.WordTrace tailWord_18456 prefixEnd_18456 8423821297320021791225 := by
  unfold tailWord_18456
  simp only [CollatzResearch.WordTrace]
  refine ⟨336572810572269439481611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 448763747429692585975481 336572810572269439481611)
  ·
    refine ⟨504859215858404159222417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 336572810572269439481611 504859215858404159222417)
    ·
      refine ⟨378644411893803119416813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 504859215858404159222417 378644411893803119416813)
      ·
        refine ⟨141991654460176169781305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 378644411893803119416813 141991654460176169781305)
        ·
          refine ⟨106493740845132127335979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141991654460176169781305 106493740845132127335979)
          ·
            refine ⟨159740611267698191003969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106493740845132127335979 159740611267698191003969)
            ·
              refine ⟨119805458450773643252977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 159740611267698191003969 119805458450773643252977)
              ·
                refine ⟨89854093838080232439733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 119805458450773643252977 89854093838080232439733)
                ·
                  refine ⟨8423821297320021791225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 89854093838080232439733 8423821297320021791225)
                  ·
                    rfl

theorem cell20_18456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 2, 5].length) (baseStart_18456 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_18456 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_18456 prefixEnd_18456 := by exact prefixLift 18456
  have htrace : WordTrace (prefixWord ++ tailWord_18456) baseStart_18456 baseEnd_18456 := by
    simpa [prefixWord, tailWord_18456, baseEnd_18456] using wordTrace_append hprefix tailTrace_18456
  have hstable : (prefixWord ++ tailWord_18456).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18456).length < 2 ^ (prefixWord ++ tailWord_18456).sum := by decide
  have hdescent : baseEnd_18456 < baseStart_18456 := by decide
  rcases family_descends (prefixWord ++ tailWord_18456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18463 : List Nat := [1, 1, 2, 4, 1, 2, 1, 2, 6]
def baseStart_18463 : Nat := 118140960795 + 18463 * 2 ^ 59
def prefixEnd_18463 : Nat := 4983230072969 + 3 ^ 40 * 18463 * 2
def baseEnd_18463 : Nat := 8427016288059108557863

theorem tailTrace_18463 : CollatzResearch.WordTrace tailWord_18463 prefixEnd_18463 8427016288059108557863 := by
  unfold tailWord_18463
  simp only [CollatzResearch.WordTrace]
  refine ⟨673400932119179074468043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 448933954746119382978695 673400932119179074468043)
  ·
    refine ⟨1010101398178768611702065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 673400932119179074468043 1010101398178768611702065)
    ·
      refine ⟨757576048634076458776549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1010101398178768611702065 757576048634076458776549)
      ·
        refine ⟨142045509118889336020603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 757576048634076458776549 142045509118889336020603)
        ·
          refine ⟨213068263678334004030905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142045509118889336020603 213068263678334004030905)
          ·
            refine ⟨159801197758750503023179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 213068263678334004030905 159801197758750503023179)
            ·
              refine ⟨239701796638125754534769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159801197758750503023179 239701796638125754534769)
              ·
                refine ⟨179776347478594315901077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 239701796638125754534769 179776347478594315901077)
                ·
                  refine ⟨8427016288059108557863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 179776347478594315901077 8427016288059108557863)
                  ·
                    rfl

theorem cell20_18463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 6].length) (baseStart_18463 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_18463 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_18463 prefixEnd_18463 := by exact prefixLift 18463
  have htrace : WordTrace (prefixWord ++ tailWord_18463) baseStart_18463 baseEnd_18463 := by
    simpa [prefixWord, tailWord_18463, baseEnd_18463] using wordTrace_append hprefix tailTrace_18463
  have hstable : (prefixWord ++ tailWord_18463).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18463).length < 2 ^ (prefixWord ++ tailWord_18463).sum := by decide
  have hdescent : baseEnd_18463 < baseStart_18463 := by decide
  rcases family_descends (prefixWord ++ tailWord_18463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18480 : List Nat := [2, 1, 1, 1, 2, 6, 2, 1, 4]
def baseStart_18480 : Nat := 118140960795 + 18480 * 2 ^ 59
def prefixEnd_18480 : Nat := 4983230072969 + 3 ^ 40 * 18480 * 2
def baseEnd_18480 : Nat := 8434775551282604991127

theorem tailTrace_18480 : CollatzResearch.WordTrace tailWord_18480 prefixEnd_18480 8434775551282604991127 := by
  unfold tailWord_18480
  simp only [CollatzResearch.WordTrace]
  refine ⟨337010486528795488918447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 449347315371727318557929 337010486528795488918447)
  ·
    refine ⟨505515729793193233377671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 337010486528795488918447 505515729793193233377671)
    ·
      refine ⟨758273594689789850066507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 505515729793193233377671 758273594689789850066507)
      ·
        refine ⟨1137410392034684775099761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 758273594689789850066507 1137410392034684775099761)
        ·
          refine ⟨853057794026013581324821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1137410392034684775099761 853057794026013581324821)
          ·
            refine ⟨39987084094969386624601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 853057794026013581324821 39987084094969386624601)
            ·
              refine ⟨29990313071227039968451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39987084094969386624601 29990313071227039968451)
              ·
                refine ⟨44985469606840559952677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29990313071227039968451 44985469606840559952677)
                ·
                  refine ⟨8434775551282604991127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44985469606840559952677 8434775551282604991127)
                  ·
                    rfl

theorem cell20_18480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 1, 4].length) (baseStart_18480 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_18480 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_18480 prefixEnd_18480 := by exact prefixLift 18480
  have htrace : WordTrace (prefixWord ++ tailWord_18480) baseStart_18480 baseEnd_18480 := by
    simpa [prefixWord, tailWord_18480, baseEnd_18480] using wordTrace_append hprefix tailTrace_18480
  have hstable : (prefixWord ++ tailWord_18480).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18480).length < 2 ^ (prefixWord ++ tailWord_18480).sum := by decide
  have hdescent : baseEnd_18480 < baseStart_18480 := by decide
  rcases family_descends (prefixWord ++ tailWord_18480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18532 : List Nat := [2, 3, 1, 1, 2, 1, 4, 1, 5]
def baseStart_18532 : Nat := 118140960795 + 18532 * 2 ^ 59
def prefixEnd_18532 : Nat := 4983230072969 + 3 ^ 40 * 18532 * 2
def baseEnd_18532 : Nat := 8458509768201535257581

theorem tailTrace_18532 : CollatzResearch.WordTrace tailWord_18532 prefixEnd_18532 8458509768201535257581 := by
  unfold tailWord_18532
  simp only [CollatzResearch.WordTrace]
  refine ⟨337958784434601929364925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 450611712579469239153233 337958784434601929364925)
  ·
    refine ⟨126734544162975723511847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 337958784434601929364925 126734544162975723511847)
    ·
      refine ⟨190101816244463585267771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126734544162975723511847 190101816244463585267771)
      ·
        refine ⟨285152724366695377901657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190101816244463585267771 285152724366695377901657)
        ·
          refine ⟨213864543275021533426243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 285152724366695377901657 213864543275021533426243)
          ·
            refine ⟨320796814912532300139365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 213864543275021533426243 320796814912532300139365)
            ·
              refine ⟨60149402796099806276131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 320796814912532300139365 60149402796099806276131)
              ·
                refine ⟨90224104194149709414197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60149402796099806276131 90224104194149709414197)
                ·
                  refine ⟨8458509768201535257581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 90224104194149709414197 8458509768201535257581)
                  ·
                    rfl

theorem cell20_18532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_18532 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_18532 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_18532 prefixEnd_18532 := by exact prefixLift 18532
  have htrace : WordTrace (prefixWord ++ tailWord_18532) baseStart_18532 baseEnd_18532 := by
    simpa [prefixWord, tailWord_18532, baseEnd_18532] using wordTrace_append hprefix tailTrace_18532
  have hstable : (prefixWord ++ tailWord_18532).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18532).length < 2 ^ (prefixWord ++ tailWord_18532).sum := by decide
  have hdescent : baseEnd_18532 < baseStart_18532 := by decide
  rcases family_descends (prefixWord ++ tailWord_18532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18580 : List Nat := [2, 4, 2, 3, 1, 8]
def baseStart_18580 : Nat := 118140960795 + 18580 * 2 ^ 59
def prefixEnd_18580 : Nat := 4983230072969 + 3 ^ 40 * 18580 * 2
def baseEnd_18580 : Nat := 314089565782470431755

theorem tailTrace_18580 : CollatzResearch.WordTrace tailWord_18580 prefixEnd_18580 314089565782470431755 := by
  unfold tailWord_18580
  simp only [CollatzResearch.WordTrace]
  refine ⟨338834136347654028238597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 451778848463538704318129 338834136347654028238597)
  ·
    refine ⟨63531400565185130294737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 338834136347654028238597 63531400565185130294737)
    ·
      refine ⟨47648550423888847721053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63531400565185130294737 47648550423888847721053)
      ·
        refine ⟨17868206408958317895395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47648550423888847721053 17868206408958317895395)
        ·
          refine ⟨26802309613437476843093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17868206408958317895395 26802309613437476843093)
          ·
            refine ⟨314089565782470431755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 26802309613437476843093 314089565782470431755)
            ·
              rfl

theorem cell20_18580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 8].length) (baseStart_18580 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_18580 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_18580 prefixEnd_18580 := by exact prefixLift 18580
  have htrace : WordTrace (prefixWord ++ tailWord_18580) baseStart_18580 baseEnd_18580 := by
    simpa [prefixWord, tailWord_18580, baseEnd_18580] using wordTrace_append hprefix tailTrace_18580
  have hstable : (prefixWord ++ tailWord_18580).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18580).length < 2 ^ (prefixWord ++ tailWord_18580).sum := by decide
  have hdescent : baseEnd_18580 < baseStart_18580 := by decide
  rcases family_descends (prefixWord ++ tailWord_18580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18584 : List Nat := [2, 1, 2, 4, 11]
def baseStart_18584 : Nat := 118140960795 + 18584 * 2 ^ 59
def prefixEnd_18584 : Nat := 4983230072969 + 3 ^ 40 * 18584 * 2
def baseEnd_18584 : Nat := 104719061544697105235

theorem tailTrace_18584 : CollatzResearch.WordTrace tailWord_18584 prefixEnd_18584 104719061544697105235 := by
  unfold tailWord_18584
  simp only [CollatzResearch.WordTrace]
  refine ⟨338907082340408369811403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 451876109787211159748537 338907082340408369811403)
  ·
    refine ⟨508360623510612554717105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 338907082340408369811403 508360623510612554717105)
    ·
      refine ⟨381270467632959416037829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 508360623510612554717105 381270467632959416037829)
      ·
        refine ⟨71488212681179890507093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 381270467632959416037829 71488212681179890507093)
        ·
          refine ⟨104719061544697105235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 71488212681179890507093 104719061544697105235)
          ·
            rfl

theorem cell20_18584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 11].length) (baseStart_18584 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_18584 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_18584 prefixEnd_18584 := by exact prefixLift 18584
  have htrace : WordTrace (prefixWord ++ tailWord_18584) baseStart_18584 baseEnd_18584 := by
    simpa [prefixWord, tailWord_18584, baseEnd_18584] using wordTrace_append hprefix tailTrace_18584
  have hstable : (prefixWord ++ tailWord_18584).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18584).length < 2 ^ (prefixWord ++ tailWord_18584).sum := by decide
  have hdescent : baseEnd_18584 < baseStart_18584 := by decide
  rcases family_descends (prefixWord ++ tailWord_18584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18586 : List Nat := [3, 1, 1, 5, 3, 1, 2, 2, 2]
def baseStart_18586 : Nat := 118140960795 + 18586 * 2 ^ 59
def prefixEnd_18586 : Nat := 4983230072969 + 3 ^ 40 * 18586 * 2
def baseEnd_18586 : Nat := 8483156839617347457361

theorem tailTrace_18586 : CollatzResearch.WordTrace tailWord_18586 prefixEnd_18586 8483156839617347457361 := by
  unfold tailWord_18586
  simp only [CollatzResearch.WordTrace]
  refine ⟨169471777668392770298903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 451924740449047387463741 169471777668392770298903)
  ·
    refine ⟨254207666502589155448355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169471777668392770298903 254207666502589155448355)
    ·
      refine ⟨381311499753883733172533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254207666502589155448355 381311499753883733172533)
      ·
        refine ⟨35747953101926599984925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 381311499753883733172533 35747953101926599984925)
        ·
          refine ⟨13405482413222474994347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35747953101926599984925 13405482413222474994347)
          ·
            refine ⟨20108223619833712491521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13405482413222474994347 20108223619833712491521)
            ·
              refine ⟨15081167714875284368641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20108223619833712491521 15081167714875284368641)
              ·
                refine ⟨11310875786156463276481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15081167714875284368641 11310875786156463276481)
                ·
                  refine ⟨8483156839617347457361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11310875786156463276481 8483156839617347457361)
                  ·
                    rfl

theorem cell20_18586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 2, 2, 2].length) (baseStart_18586 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_18586 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_18586 prefixEnd_18586 := by exact prefixLift 18586
  have htrace : WordTrace (prefixWord ++ tailWord_18586) baseStart_18586 baseEnd_18586 := by
    simpa [prefixWord, tailWord_18586, baseEnd_18586] using wordTrace_append hprefix tailTrace_18586
  have hstable : (prefixWord ++ tailWord_18586).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18586).length < 2 ^ (prefixWord ++ tailWord_18586).sum := by decide
  have hdescent : baseEnd_18586 < baseStart_18586 := by decide
  rcases family_descends (prefixWord ++ tailWord_18586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18615 : List Nat := [1, 1, 3, 1, 4, 2, 1, 1, 6]
def baseStart_18615 : Nat := 118140960795 + 18615 * 2 ^ 59
def prefixEnd_18615 : Nat := 4983230072969 + 3 ^ 40 * 18615 * 2
def baseEnd_18615 : Nat := 8496393229822135490575

theorem tailTrace_18615 : CollatzResearch.WordTrace tailWord_18615 prefixEnd_18615 8496393229822135490575 := by
  unfold tailWord_18615
  simp only [CollatzResearch.WordTrace]
  refine ⟨678944827568509034001299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 452629885045672689334199 678944827568509034001299)
  ·
    refine ⟨1018417241352763551001949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 678944827568509034001299 1018417241352763551001949)
    ·
      refine ⟨381906465507286331625731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1018417241352763551001949 381906465507286331625731)
      ·
        refine ⟨572859698260929497438597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 381906465507286331625731 572859698260929497438597)
        ·
          refine ⟨107411193423924280769737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 572859698260929497438597 107411193423924280769737)
          ·
            refine ⟨80558395067943210577303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107411193423924280769737 80558395067943210577303)
            ·
              refine ⟨120837592601914815865955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80558395067943210577303 120837592601914815865955)
              ·
                refine ⟨181256388902872223798933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 120837592601914815865955 181256388902872223798933)
                ·
                  refine ⟨8496393229822135490575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 181256388902872223798933 8496393229822135490575)
                  ·
                    rfl

theorem cell20_18615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 6].length) (baseStart_18615 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_18615 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_18615 prefixEnd_18615 := by exact prefixLift 18615
  have htrace : WordTrace (prefixWord ++ tailWord_18615) baseStart_18615 baseEnd_18615 := by
    simpa [prefixWord, tailWord_18615, baseEnd_18615] using wordTrace_append hprefix tailTrace_18615
  have hstable : (prefixWord ++ tailWord_18615).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18615).length < 2 ^ (prefixWord ++ tailWord_18615).sum := by decide
  have hdescent : baseEnd_18615 < baseStart_18615 := by decide
  rcases family_descends (prefixWord ++ tailWord_18615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18628 : List Nat := [2, 3, 3, 1, 2, 2, 2, 3, 2]
def baseStart_18628 : Nat := 118140960795 + 18628 * 2 ^ 59
def prefixEnd_18628 : Nat := 4983230072969 + 3 ^ 40 * 18628 * 2
def baseEnd_18628 : Nat := 8502326784051868057189

theorem tailTrace_18628 : CollatzResearch.WordTrace tailWord_18628 prefixEnd_18628 8502326784051868057189 := by
  unfold tailWord_18628
  simp only [CollatzResearch.WordTrace]
  refine ⟨339709488260706127112269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 452945984347608169483025 339709488260706127112269)
  ·
    refine ⟨127391058097764797667101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 339709488260706127112269 127391058097764797667101)
    ·
      refine ⟨47771646786661799125163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127391058097764797667101 47771646786661799125163)
      ·
        refine ⟨71657470179992698687745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47771646786661799125163 71657470179992698687745)
        ·
          refine ⟨53743102634994524015809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71657470179992698687745 53743102634994524015809)
          ·
            refine ⟨40307326976245893011857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53743102634994524015809 40307326976245893011857)
            ·
              refine ⟨30230495232184419758893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40307326976245893011857 30230495232184419758893)
              ·
                refine ⟨11336435712069157409585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30230495232184419758893 11336435712069157409585)
                ·
                  refine ⟨8502326784051868057189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11336435712069157409585 8502326784051868057189)
                  ·
                    rfl

theorem cell20_18628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 3, 2].length) (baseStart_18628 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_18628 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_18628 prefixEnd_18628 := by exact prefixLift 18628
  have htrace : WordTrace (prefixWord ++ tailWord_18628) baseStart_18628 baseEnd_18628 := by
    simpa [prefixWord, tailWord_18628, baseEnd_18628] using wordTrace_append hprefix tailTrace_18628
  have hstable : (prefixWord ++ tailWord_18628).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18628).length < 2 ^ (prefixWord ++ tailWord_18628).sum := by decide
  have hdescent : baseEnd_18628 < baseStart_18628 := by decide
  rcases family_descends (prefixWord ++ tailWord_18628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18642 : List Nat := [3, 2, 2, 2, 1, 4, 1, 2, 3]
def baseStart_18642 : Nat := 118140960795 + 18642 * 2 ^ 59
def prefixEnd_18642 : Nat := 4983230072969 + 3 ^ 40 * 18642 * 2
def baseEnd_18642 : Nat := 8508716765530041590465

theorem tailTrace_18642 : CollatzResearch.WordTrace tailWord_18642 prefixEnd_18642 8508716765530041590465 := by
  unfold tailWord_18642
  simp only [CollatzResearch.WordTrace]
  refine ⟨169982399617673161308545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 453286398980461763489453 169982399617673161308545)
  ·
    refine ⟨127486799713254870981409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169982399617673161308545 127486799713254870981409)
    ·
      refine ⟨95615099784941153236057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127486799713254870981409 95615099784941153236057)
      ·
        refine ⟨71711324838705864927043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95615099784941153236057 71711324838705864927043)
        ·
          refine ⟨107566987258058797390565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71711324838705864927043 107566987258058797390565)
          ·
            refine ⟨20168810110886024510731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 107566987258058797390565 20168810110886024510731)
            ·
              refine ⟨30253215166329036766097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20168810110886024510731 30253215166329036766097)
              ·
                refine ⟨22689911374746777574573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30253215166329036766097 22689911374746777574573)
                ·
                  refine ⟨8508716765530041590465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22689911374746777574573 8508716765530041590465)
                  ·
                    rfl

theorem cell20_18642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 2, 3].length) (baseStart_18642 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_18642 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_18642 prefixEnd_18642 := by exact prefixLift 18642
  have htrace : WordTrace (prefixWord ++ tailWord_18642) baseStart_18642 baseEnd_18642 := by
    simpa [prefixWord, tailWord_18642, baseEnd_18642] using wordTrace_append hprefix tailTrace_18642
  have hstable : (prefixWord ++ tailWord_18642).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18642).length < 2 ^ (prefixWord ++ tailWord_18642).sum := by decide
  have hdescent : baseEnd_18642 < baseStart_18642 := by decide
  rcases family_descends (prefixWord ++ tailWord_18642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18659 : List Nat := [1, 1, 1, 8, 1, 1, 3, 1, 3]
def baseStart_18659 : Nat := 118140960795 + 18659 * 2 ^ 59
def prefixEnd_18659 : Nat := 4983230072969 + 3 ^ 40 * 18659 * 2
def baseEnd_18659 : Nat := 8516476028753538023729

theorem tailTrace_18659 : CollatzResearch.WordTrace tailWord_18659 prefixEnd_18659 8516476028753538023729 := by
  unfold tailWord_18659
  simp only [CollatzResearch.WordTrace]
  refine ⟨680549639409104548603031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 453699759606069699068687 680549639409104548603031)
  ·
    refine ⟨1020824459113656822904547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 680549639409104548603031 1020824459113656822904547)
    ·
      refine ⟨1531236688670485234356821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1020824459113656822904547 1531236688670485234356821)
      ·
        refine ⟨17944179945357248840119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 1531236688670485234356821 17944179945357248840119)
        ·
          refine ⟨26916269918035873260179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17944179945357248840119 26916269918035873260179)
          ·
            refine ⟨40374404877053809890269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26916269918035873260179 40374404877053809890269)
            ·
              refine ⟨15140401828895178708851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40374404877053809890269 15140401828895178708851)
              ·
                refine ⟨22710602743342768063277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15140401828895178708851 22710602743342768063277)
                ·
                  refine ⟨8516476028753538023729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22710602743342768063277 8516476028753538023729)
                  ·
                    rfl

theorem cell20_18659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 3, 1, 3].length) (baseStart_18659 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_18659 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_18659 prefixEnd_18659 := by exact prefixLift 18659
  have htrace : WordTrace (prefixWord ++ tailWord_18659) baseStart_18659 baseEnd_18659 := by
    simpa [prefixWord, tailWord_18659, baseEnd_18659] using wordTrace_append hprefix tailTrace_18659
  have hstable : (prefixWord ++ tailWord_18659).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18659).length < 2 ^ (prefixWord ++ tailWord_18659).sum := by decide
  have hdescent : baseEnd_18659 < baseStart_18659 := by decide
  rcases family_descends (prefixWord ++ tailWord_18659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18660 : List Nat := [2, 3, 1, 1, 1, 2, 1, 9]
def baseStart_18660 : Nat := 118140960795 + 18660 * 2 ^ 59
def prefixEnd_18660 : Nat := 4983230072969 + 3 ^ 40 * 18660 * 2
def baseEnd_18660 : Nat := 2838977485333992996797

theorem tailTrace_18660 : CollatzResearch.WordTrace tailWord_18660 prefixEnd_18660 2838977485333992996797 := by
  unfold tailWord_18660
  simp only [CollatzResearch.WordTrace]
  refine ⟨340293056202740859694717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 453724074936987812926289 340293056202740859694717)
  ·
    refine ⟨127609896076027822385519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 340293056202740859694717 127609896076027822385519)
    ·
      refine ⟨191414844114041733578279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127609896076027822385519 191414844114041733578279)
      ·
        refine ⟨287122266171062600367419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191414844114041733578279 287122266171062600367419)
        ·
          refine ⟨430683399256593900551129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 287122266171062600367419 430683399256593900551129)
          ·
            refine ⟨323012549442445425413347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 430683399256593900551129 323012549442445425413347)
            ·
              refine ⟨484518824163668138120021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 323012549442445425413347 484518824163668138120021)
              ·
                refine ⟨2838977485333992996797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 484518824163668138120021 2838977485333992996797)
                ·
                  rfl

theorem cell20_18660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 9].length) (baseStart_18660 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_18660 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_18660 prefixEnd_18660 := by exact prefixLift 18660
  have htrace : WordTrace (prefixWord ++ tailWord_18660) baseStart_18660 baseEnd_18660 := by
    simpa [prefixWord, tailWord_18660, baseEnd_18660] using wordTrace_append hprefix tailTrace_18660
  have hstable : (prefixWord ++ tailWord_18660).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18660).length < 2 ^ (prefixWord ++ tailWord_18660).sum := by decide
  have hdescent : baseEnd_18660 < baseStart_18660 := by decide
  rcases family_descends (prefixWord ++ tailWord_18660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18684 : List Nat := [2, 2, 2, 1, 4, 1, 1, 2, 5]
def baseStart_18684 : Nat := 118140960795 + 18684 * 2 ^ 59
def prefixEnd_18684 : Nat := 4983230072969 + 3 ^ 40 * 18684 * 2
def baseEnd_18684 : Nat := 8527886709964562190293

theorem tailTrace_18684 : CollatzResearch.WordTrace tailWord_18684 prefixEnd_18684 8527886709964562190293 := by
  unfold tailWord_18684
  simp only [CollatzResearch.WordTrace]
  refine ⟨340730732159266909131553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 454307642879022545508737 340730732159266909131553)
  ·
    refine ⟨255548049119450181848665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 340730732159266909131553 255548049119450181848665)
    ·
      refine ⟨191661036839587636386499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 255548049119450181848665 191661036839587636386499)
      ·
        refine ⟨287491555259381454579749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191661036839587636386499 287491555259381454579749)
        ·
          refine ⟨53904666611134022733703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 287491555259381454579749 53904666611134022733703)
          ·
            refine ⟨80856999916701034100555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53904666611134022733703 80856999916701034100555)
            ·
              refine ⟨121285499875051551150833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80856999916701034100555 121285499875051551150833)
              ·
                refine ⟨90964124906288663363125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 121285499875051551150833 90964124906288663363125)
                ·
                  refine ⟨8527886709964562190293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 90964124906288663363125 8527886709964562190293)
                  ·
                    rfl

theorem cell20_18684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 2, 5].length) (baseStart_18684 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_18684 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_18684 prefixEnd_18684 := by exact prefixLift 18684
  have htrace : WordTrace (prefixWord ++ tailWord_18684) baseStart_18684 baseEnd_18684 := by
    simpa [prefixWord, tailWord_18684, baseEnd_18684] using wordTrace_append hprefix tailTrace_18684
  have hstable : (prefixWord ++ tailWord_18684).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18684).length < 2 ^ (prefixWord ++ tailWord_18684).sum := by decide
  have hdescent : baseEnd_18684 < baseStart_18684 := by decide
  rcases family_descends (prefixWord ++ tailWord_18684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18698 : List Nat := [3, 1, 2, 2, 1, 1, 10]
def baseStart_18698 : Nat := 118140960795 + 18698 * 2 ^ 59
def prefixEnd_18698 : Nat := 4983230072969 + 3 ^ 40 * 18698 * 2
def baseEnd_18698 : Nat := 948252965715859524841

theorem tailTrace_18698 : CollatzResearch.WordTrace tailWord_18698 prefixEnd_18698 948252965715859524841 := by
  unfold tailWord_18698
  simp only [CollatzResearch.WordTrace]
  refine ⟨170493021566953552318187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 454648057511876139515165 170493021566953552318187)
  ·
    refine ⟨255739532350430328477281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170493021566953552318187 255739532350430328477281)
    ·
      refine ⟨191804649262822746357961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 255739532350430328477281 191804649262822746357961)
      ·
        refine ⟨143853486947117059768471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 191804649262822746357961 143853486947117059768471)
        ·
          refine ⟨215780230420675589652707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143853486947117059768471 215780230420675589652707)
          ·
            refine ⟨323670345631013384479061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 215780230420675589652707 323670345631013384479061)
            ·
              refine ⟨948252965715859524841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 323670345631013384479061 948252965715859524841)
              ·
                rfl

theorem cell20_18698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 10].length) (baseStart_18698 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_18698 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_18698 prefixEnd_18698 := by exact prefixLift 18698
  have htrace : WordTrace (prefixWord ++ tailWord_18698) baseStart_18698 baseEnd_18698 := by
    simpa [prefixWord, tailWord_18698, baseEnd_18698] using wordTrace_append hprefix tailTrace_18698
  have hstable : (prefixWord ++ tailWord_18698).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18698).length < 2 ^ (prefixWord ++ tailWord_18698).sum := by decide
  have hdescent : baseEnd_18698 < baseStart_18698 := by decide
  rcases family_descends (prefixWord ++ tailWord_18698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18743 : List Nat := [1, 1, 3, 1, 2, 1, 1, 3, 7]
def baseStart_18743 : Nat := 118140960795 + 18743 * 2 ^ 59
def prefixEnd_18743 : Nat := 4983230072969 + 3 ^ 40 * 18743 * 2
def baseEnd_18743 : Nat := 8554815917622579223385

theorem tailTrace_18743 : CollatzResearch.WordTrace tailWord_18743 prefixEnd_18743 8554815917622579223385 := by
  unfold tailWord_18743
  simp only [CollatzResearch.WordTrace]
  refine ⟨683613371104786894660883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 455742247403191263107255 683613371104786894660883)
  ·
    refine ⟨1025420056657180341991325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 683613371104786894660883 1025420056657180341991325)
    ·
      refine ⟨384532521246442628246747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1025420056657180341991325 384532521246442628246747)
      ·
        refine ⟨576798781869663942370121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 384532521246442628246747 576798781869663942370121)
        ·
          refine ⟨432599086402247956777591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 576798781869663942370121 432599086402247956777591)
          ·
            refine ⟨648898629603371935166387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 432599086402247956777591 648898629603371935166387)
            ·
              refine ⟨973347944405057902749581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 648898629603371935166387 973347944405057902749581)
              ·
                refine ⟨365005479151896713531093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 973347944405057902749581 365005479151896713531093)
                ·
                  refine ⟨8554815917622579223385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 365005479151896713531093 8554815917622579223385)
                  ·
                    rfl

theorem cell20_18743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 7].length) (baseStart_18743 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_18743 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_18743 prefixEnd_18743 := by exact prefixLift 18743
  have htrace : WordTrace (prefixWord ++ tailWord_18743) baseStart_18743 baseEnd_18743 := by
    simpa [prefixWord, tailWord_18743, baseEnd_18743] using wordTrace_append hprefix tailTrace_18743
  have hstable : (prefixWord ++ tailWord_18743).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18743).length < 2 ^ (prefixWord ++ tailWord_18743).sum := by decide
  have hdescent : baseEnd_18743 < baseStart_18743 := by decide
  rcases family_descends (prefixWord ++ tailWord_18743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18753 : List Nat := [1, 2, 5, 2, 2, 8]
def baseStart_18753 : Nat := 118140960795 + 18753 * 2 ^ 59
def prefixEnd_18753 : Nat := 4983230072969 + 3 ^ 40 * 18753 * 2
def baseEnd_18753 : Nat := 317014081115073662593

theorem tailTrace_18753 : CollatzResearch.WordTrace tailWord_18753 prefixEnd_18753 317014081115073662593 := by
  unfold tailWord_18753
  simp only [CollatzResearch.WordTrace]
  refine ⟨683978101068558602524913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 455985400712372401683275 683978101068558602524913)
  ·
    refine ⟨512983575801418951893685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 683978101068558602524913 512983575801418951893685)
    ·
      refine ⟨48092210231383026740033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 512983575801418951893685 48092210231383026740033)
      ·
        refine ⟨36069157673537270055025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48092210231383026740033 36069157673537270055025)
        ·
          refine ⟨27051868255152952541269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36069157673537270055025 27051868255152952541269)
          ·
            refine ⟨317014081115073662593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 27051868255152952541269 317014081115073662593)
            ·
              rfl

theorem cell20_18753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 8].length) (baseStart_18753 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_18753 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_18753 prefixEnd_18753 := by exact prefixLift 18753
  have htrace : WordTrace (prefixWord ++ tailWord_18753) baseStart_18753 baseEnd_18753 := by
    simpa [prefixWord, tailWord_18753, baseEnd_18753] using wordTrace_append hprefix tailTrace_18753
  have hstable : (prefixWord ++ tailWord_18753).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18753).length < 2 ^ (prefixWord ++ tailWord_18753).sum := by decide
  have hdescent : baseEnd_18753 < baseStart_18753 := by decide
  rcases family_descends (prefixWord ++ tailWord_18753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18760 : List Nat := [2, 1, 3, 1, 1, 2, 3, 4, 3]
def baseStart_18760 : Nat := 118140960795 + 18760 * 2 ^ 59
def prefixEnd_18760 : Nat := 4983230072969 + 3 ^ 40 * 18760 * 2
def baseEnd_18760 : Nat := 8562575180846075656649

theorem tailTrace_18760 : CollatzResearch.WordTrace tailWord_18760 prefixEnd_18760 8562575180846075656649 := by
  unfold tailWord_18760
  simp only [CollatzResearch.WordTrace]
  refine ⟨342116706021599399014867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 456155608028799198686489 342116706021599399014867)
  ·
    refine ⟨513175059032399098522301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 342116706021599399014867 513175059032399098522301)
    ·
      refine ⟨192440647137149661945863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 513175059032399098522301 192440647137149661945863)
      ·
        refine ⟨288660970705724492918795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192440647137149661945863 288660970705724492918795)
        ·
          refine ⟨432991456058586739378193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 288660970705724492918795 432991456058586739378193)
          ·
            refine ⟨324743592043940054533645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 432991456058586739378193 324743592043940054533645)
            ·
              refine ⟨121778847016477520450117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 324743592043940054533645 121778847016477520450117)
              ·
                refine ⟨22833533815589535084397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 121778847016477520450117 22833533815589535084397)
                ·
                  refine ⟨8562575180846075656649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22833533815589535084397 8562575180846075656649)
                  ·
                    rfl

theorem cell20_18760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 4, 3].length) (baseStart_18760 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_18760 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_18760 prefixEnd_18760 := by exact prefixLift 18760
  have htrace : WordTrace (prefixWord ++ tailWord_18760) baseStart_18760 baseEnd_18760 := by
    simpa [prefixWord, tailWord_18760, baseEnd_18760] using wordTrace_append hprefix tailTrace_18760
  have hstable : (prefixWord ++ tailWord_18760).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18760).length < 2 ^ (prefixWord ++ tailWord_18760).sum := by decide
  have hdescent : baseEnd_18760 < baseStart_18760 := by decide
  rcases family_descends (prefixWord ++ tailWord_18760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18784 : List Nat := [2, 1, 1, 3, 5, 1, 1, 2, 4]
def baseStart_18784 : Nat := 118140960795 + 18784 * 2 ^ 59
def prefixEnd_18784 : Nat := 4983230072969 + 3 ^ 40 * 18784 * 2
def baseEnd_18784 : Nat := 8573529434808658856551

theorem tailTrace_18784 : CollatzResearch.WordTrace tailWord_18784 prefixEnd_18784 8573529434808658856551 := by
  unfold tailWord_18784
  simp only [CollatzResearch.WordTrace]
  refine ⟨342554381978125448451703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 456739175970833931268937 342554381978125448451703)
  ·
    refine ⟨513831572967188172677555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 342554381978125448451703 513831572967188172677555)
    ·
      refine ⟨770747359450782259016333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 513831572967188172677555 770747359450782259016333)
      ·
        refine ⟨289030259794043347131125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 770747359450782259016333 289030259794043347131125)
        ·
          refine ⟨27096586855691563793543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 289030259794043347131125 27096586855691563793543)
          ·
            refine ⟨40644880283537345690315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27096586855691563793543 40644880283537345690315)
            ·
              refine ⟨60967320425306018535473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40644880283537345690315 60967320425306018535473)
              ·
                refine ⟨45725490318979513901605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60967320425306018535473 45725490318979513901605)
                ·
                  refine ⟨8573529434808658856551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45725490318979513901605 8573529434808658856551)
                  ·
                    rfl

theorem cell20_18784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 2, 4].length) (baseStart_18784 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_18784 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_18784 prefixEnd_18784 := by exact prefixLift 18784
  have htrace : WordTrace (prefixWord ++ tailWord_18784) baseStart_18784 baseEnd_18784 := by
    simpa [prefixWord, tailWord_18784, baseEnd_18784] using wordTrace_append hprefix tailTrace_18784
  have hstable : (prefixWord ++ tailWord_18784).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18784).length < 2 ^ (prefixWord ++ tailWord_18784).sum := by decide
  have hdescent : baseEnd_18784 < baseStart_18784 := by decide
  rcases family_descends (prefixWord ++ tailWord_18784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18818 : List Nat := [3, 4, 2, 1, 2, 1, 2, 1, 4]
def baseStart_18818 : Nat := 118140960795 + 18818 * 2 ^ 59
def prefixEnd_18818 : Nat := 4983230072969 + 3 ^ 40 * 18818 * 2
def baseEnd_18818 : Nat := 8589047961255651723079

theorem tailTrace_18818 : CollatzResearch.WordTrace tailWord_18818 prefixEnd_18818 8589047961255651723079 := by
  unfold tailWord_18818
  simp only [CollatzResearch.WordTrace]
  refine ⟨171587211458268675910277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 457565897222049802427405 171587211458268675910277)
  ·
    refine ⟨32172602148425376733177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 171587211458268675910277 32172602148425376733177)
    ·
      refine ⟨24129451611319032549883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32172602148425376733177 24129451611319032549883)
      ·
        refine ⟨36194177416978548824825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24129451611319032549883 36194177416978548824825)
        ·
          refine ⟨27145633062733911618619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36194177416978548824825 27145633062733911618619)
          ·
            refine ⟨40718449594100867427929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27145633062733911618619 40718449594100867427929)
            ·
              refine ⟨30538837195575650570947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40718449594100867427929 30538837195575650570947)
              ·
                refine ⟨45808255793363475856421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30538837195575650570947 45808255793363475856421)
                ·
                  refine ⟨8589047961255651723079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45808255793363475856421 8589047961255651723079)
                  ·
                    rfl

theorem cell20_18818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_18818 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_18818 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_18818 prefixEnd_18818 := by exact prefixLift 18818
  have htrace : WordTrace (prefixWord ++ tailWord_18818) baseStart_18818 baseEnd_18818 := by
    simpa [prefixWord, tailWord_18818, baseEnd_18818] using wordTrace_append hprefix tailTrace_18818
  have hstable : (prefixWord ++ tailWord_18818).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18818).length < 2 ^ (prefixWord ++ tailWord_18818).sum := by decide
  have hdescent : baseEnd_18818 < baseStart_18818 := by decide
  rcases family_descends (prefixWord ++ tailWord_18818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18838 : List Nat := [5, 3, 1, 2, 2, 1, 2, 4]
def baseStart_18838 : Nat := 118140960795 + 18838 * 2 ^ 59
def prefixEnd_18838 : Nat := 4983230072969 + 3 ^ 40 * 18838 * 2
def baseEnd_18838 : Nat := 2866058835408157018777

theorem tailTrace_18838 : CollatzResearch.WordTrace tailWord_18838 prefixEnd_18838 2866058835408157018777 := by
  unfold tailWord_18838
  simp only [CollatzResearch.WordTrace]
  refine ⟨42942394110038632460573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 458052203840412079579445 42942394110038632460573)
  ·
    refine ⟨16103397791264487172715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42942394110038632460573 16103397791264487172715)
    ·
      refine ⟨24155096686896730759073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16103397791264487172715 24155096686896730759073)
      ·
        refine ⟨18116322515172548069305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24155096686896730759073 18116322515172548069305)
        ·
          refine ⟨13587241886379411051979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18116322515172548069305 13587241886379411051979)
          ·
            refine ⟨20380862829569116577969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13587241886379411051979 20380862829569116577969)
            ·
              refine ⟨15285647122176837433477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20380862829569116577969 15285647122176837433477)
              ·
                refine ⟨2866058835408157018777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15285647122176837433477 2866058835408157018777)
                ·
                  rfl

theorem cell20_18838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 2, 4].length) (baseStart_18838 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_18838 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_18838 prefixEnd_18838 := by exact prefixLift 18838
  have htrace : WordTrace (prefixWord ++ tailWord_18838) baseStart_18838 baseEnd_18838 := by
    simpa [prefixWord, tailWord_18838, baseEnd_18838] using wordTrace_append hprefix tailTrace_18838
  have hstable : (prefixWord ++ tailWord_18838).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18838).length < 2 ^ (prefixWord ++ tailWord_18838).sum := by decide
  have hdescent : baseEnd_18838 < baseStart_18838 := by decide
  rcases family_descends (prefixWord ++ tailWord_18838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18846 : List Nat := [4, 3, 1, 2, 1, 2, 1, 6]
def baseStart_18846 : Nat := 118140960795 + 18846 * 2 ^ 59
def prefixEnd_18846 : Nat := 4983230072969 + 3 ^ 40 * 18846 * 2
def baseEnd_18846 : Nat := 2867275974737332929877

theorem tailTrace_18846 : CollatzResearch.WordTrace tailWord_18846 prefixEnd_18846 2867275974737332929877 := by
  unfold tailWord_18846
  simp only [CollatzResearch.WordTrace]
  refine ⟨85921261216454435707549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 458246726487756990440261 85921261216454435707549)
  ·
    refine ⟨32220472956170413390331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85921261216454435707549 32220472956170413390331)
    ·
      refine ⟨48330709434255620085497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32220472956170413390331 48330709434255620085497)
      ·
        refine ⟨36248032075691715064123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48330709434255620085497 36248032075691715064123)
        ·
          refine ⟨54372048113537572596185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36248032075691715064123 54372048113537572596185)
          ·
            refine ⟨40779036085153179447139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54372048113537572596185 40779036085153179447139)
            ·
              refine ⟨61168554127729769170709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40779036085153179447139 61168554127729769170709)
              ·
                refine ⟨2867275974737332929877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 61168554127729769170709 2867275974737332929877)
                ·
                  rfl

theorem cell20_18846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 6].length) (baseStart_18846 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_18846 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_18846 prefixEnd_18846 := by exact prefixLift 18846
  have htrace : WordTrace (prefixWord ++ tailWord_18846) baseStart_18846 baseEnd_18846 := by
    simpa [prefixWord, tailWord_18846, baseEnd_18846] using wordTrace_append hprefix tailTrace_18846
  have hstable : (prefixWord ++ tailWord_18846).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18846).length < 2 ^ (prefixWord ++ tailWord_18846).sum := by decide
  have hdescent : baseEnd_18846 < baseStart_18846 := by decide
  rcases family_descends (prefixWord ++ tailWord_18846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18856 : List Nat := [2, 1, 6, 1, 1, 1, 3, 3, 2]
def baseStart_18856 : Nat := 118140960795 + 18856 * 2 ^ 59
def prefixEnd_18856 : Nat := 4983230072969 + 3 ^ 40 * 18856 * 2
def baseEnd_18856 : Nat := 8606392196696408456257

theorem tailTrace_18856 : CollatzResearch.WordTrace tailWord_18856 prefixEnd_18856 8606392196696408456257 := by
  unfold tailWord_18856
  simp only [CollatzResearch.WordTrace]
  refine ⟨343867409847703596762211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 458489879796938129016281 343867409847703596762211)
  ·
    refine ⟨515801114771555395143317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 343867409847703596762211 515801114771555395143317)
    ·
      refine ⟨24178177254916659147343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 515801114771555395143317 24178177254916659147343)
      ·
        refine ⟨36267265882374988721015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24178177254916659147343 36267265882374988721015)
        ·
          refine ⟨54400898823562483081523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36267265882374988721015 54400898823562483081523)
          ·
            refine ⟨81601348235343724622285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54400898823562483081523 81601348235343724622285)
            ·
              refine ⟨30600505588253896733357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81601348235343724622285 30600505588253896733357)
              ·
                refine ⟨11475189595595211275009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30600505588253896733357 11475189595595211275009)
                ·
                  refine ⟨8606392196696408456257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11475189595595211275009 8606392196696408456257)
                  ·
                    rfl

theorem cell20_18856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 3, 2].length) (baseStart_18856 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_18856 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_18856 prefixEnd_18856 := by exact prefixLift 18856
  have htrace : WordTrace (prefixWord ++ tailWord_18856) baseStart_18856 baseEnd_18856 := by
    simpa [prefixWord, tailWord_18856, baseEnd_18856] using wordTrace_append hprefix tailTrace_18856
  have hstable : (prefixWord ++ tailWord_18856).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18856).length < 2 ^ (prefixWord ++ tailWord_18856).sum := by decide
  have hdescent : baseEnd_18856 < baseStart_18856 := by decide
  rcases family_descends (prefixWord ++ tailWord_18856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18884 : List Nat := [2, 3, 3, 2, 2, 1, 2, 5]
def baseStart_18884 : Nat := 118140960795 + 18884 * 2 ^ 59
def prefixEnd_18884 : Nat := 4983230072969 + 3 ^ 40 * 18884 * 2
def baseEnd_18884 : Nat := 2873057386550918507603

theorem tailTrace_18884 : CollatzResearch.WordTrace tailWord_18884 prefixEnd_18884 2873057386550918507603 := by
  unfold tailWord_18884
  simp only [CollatzResearch.WordTrace]
  refine ⟨344378031796983987771853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 459170709062645317029137 344378031796983987771853)
  ·
    refine ⟨129141761923868995414445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 344378031796983987771853 129141761923868995414445)
    ·
      refine ⟨48428160721450873280417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129141761923868995414445 48428160721450873280417)
      ·
        refine ⟨36321120541088154960313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48428160721450873280417 36321120541088154960313)
        ·
          refine ⟨27240840405816116220235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36321120541088154960313 27240840405816116220235)
          ·
            refine ⟨40861260608724174330353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27240840405816116220235 40861260608724174330353)
            ·
              refine ⟨30645945456543130747765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40861260608724174330353 30645945456543130747765)
              ·
                refine ⟨2873057386550918507603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30645945456543130747765 2873057386550918507603)
                ·
                  rfl

theorem cell20_18884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 5].length) (baseStart_18884 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_18884 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_18884 prefixEnd_18884 := by exact prefixLift 18884
  have htrace : WordTrace (prefixWord ++ tailWord_18884) baseStart_18884 baseEnd_18884 := by
    simpa [prefixWord, tailWord_18884, baseEnd_18884] using wordTrace_append hprefix tailTrace_18884
  have hstable : (prefixWord ++ tailWord_18884).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18884).length < 2 ^ (prefixWord ++ tailWord_18884).sum := by decide
  have hdescent : baseEnd_18884 < baseStart_18884 := by decide
  rcases family_descends (prefixWord ++ tailWord_18884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18888 : List Nat := [2, 1, 3, 1, 3, 2, 1, 7]
def baseStart_18888 : Nat := 118140960795 + 18888 * 2 ^ 59
def prefixEnd_18888 : Nat := 4983230072969 + 3 ^ 40 * 18888 * 2
def baseEnd_18888 : Nat := 2873665956215506463153

theorem tailTrace_18888 : CollatzResearch.WordTrace tailWord_18888 prefixEnd_18888 2873665956215506463153 := by
  unfold tailWord_18888
  simp only [CollatzResearch.WordTrace]
  refine ⟨344450977789738329344659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 459267970386317772459545 344450977789738329344659)
  ·
    refine ⟨516676466684607494016989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 344450977789738329344659 516676466684607494016989)
    ·
      refine ⟨193753675006727810256371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 516676466684607494016989 193753675006727810256371)
      ·
        refine ⟨290630512510091715384557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193753675006727810256371 290630512510091715384557)
        ·
          refine ⟨108986442191284393269209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 290630512510091715384557 108986442191284393269209)
          ·
            refine ⟨81739831643463294951907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108986442191284393269209 81739831643463294951907)
            ·
              refine ⟨122609747465194942427861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81739831643463294951907 122609747465194942427861)
              ·
                refine ⟨2873665956215506463153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 122609747465194942427861 2873665956215506463153)
                ·
                  rfl

theorem cell20_18888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 7].length) (baseStart_18888 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_18888 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_18888 prefixEnd_18888 := by exact prefixLift 18888
  have htrace : WordTrace (prefixWord ++ tailWord_18888) baseStart_18888 baseEnd_18888 := by
    simpa [prefixWord, tailWord_18888, baseEnd_18888] using wordTrace_append hprefix tailTrace_18888
  have hstable : (prefixWord ++ tailWord_18888).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18888).length < 2 ^ (prefixWord ++ tailWord_18888).sum := by decide
  have hdescent : baseEnd_18888 < baseStart_18888 := by decide
  rcases family_descends (prefixWord ++ tailWord_18888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18926 : List Nat := [4, 1, 2, 1, 2, 10]
def baseStart_18926 : Nat := 118140960795 + 18926 * 2 ^ 59
def prefixEnd_18926 : Nat := 4983230072969 + 3 ^ 40 * 18926 * 2
def baseEnd_18926 : Nat := 319938596447676893431

theorem tailTrace_18926 : CollatzResearch.WordTrace tailWord_18926 prefixEnd_18926 319938596447676893431 := by
  unfold tailWord_18926
  simp only [CollatzResearch.WordTrace]
  refine ⟨86285991180226143571579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 460191952961206099048421 86285991180226143571579)
  ·
    refine ⟨129428986770339215357369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86285991180226143571579 129428986770339215357369)
    ·
      refine ⟨97071740077754411518027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129428986770339215357369 97071740077754411518027)
      ·
        refine ⟨145607610116631617277041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97071740077754411518027 145607610116631617277041)
        ·
          refine ⟨109205707587473712957781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145607610116631617277041 109205707587473712957781)
          ·
            refine ⟨319938596447676893431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 109205707587473712957781 319938596447676893431)
            ·
              rfl

theorem cell20_18926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 10].length) (baseStart_18926 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_18926 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_18926 prefixEnd_18926 := by exact prefixLift 18926
  have htrace : WordTrace (prefixWord ++ tailWord_18926) baseStart_18926 baseEnd_18926 := by
    simpa [prefixWord, tailWord_18926, baseEnd_18926] using wordTrace_append hprefix tailTrace_18926
  have hstable : (prefixWord ++ tailWord_18926).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18926).length < 2 ^ (prefixWord ++ tailWord_18926).sum := by decide
  have hdescent : baseEnd_18926 < baseStart_18926 := by decide
  rcases family_descends (prefixWord ++ tailWord_18926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18936 : List Nat := [2, 1, 2, 1, 1, 4, 3, 4, 2]
def baseStart_18936 : Nat := 118140960795 + 18936 * 2 ^ 59
def prefixEnd_18936 : Nat := 4983230072969 + 3 ^ 40 * 18936 * 2
def baseEnd_18936 : Nat := 8642906376571685789263

theorem tailTrace_18936 : CollatzResearch.WordTrace tailWord_18936 prefixEnd_18936 8642906376571685789263 := by
  unfold tailWord_18936
  simp only [CollatzResearch.WordTrace]
  refine ⟨345326329702790428218331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 460435106270387237624441 345326329702790428218331)
  ·
    refine ⟨517989494554185642327497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 345326329702790428218331 517989494554185642327497)
    ·
      refine ⟨388492120915639231745623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 517989494554185642327497 388492120915639231745623)
      ·
        refine ⟨582738181373458847618435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 388492120915639231745623 582738181373458847618435)
        ·
          refine ⟨874107272060188271427653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 582738181373458847618435 874107272060188271427653)
          ·
            refine ⟨163895113511285300892685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 874107272060188271427653 163895113511285300892685)
            ·
              refine ⟨61460667566731987834757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 163895113511285300892685 61460667566731987834757)
              ·
                refine ⟨11523875168762247719017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61460667566731987834757 11523875168762247719017)
                ·
                  refine ⟨8642906376571685789263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11523875168762247719017 8642906376571685789263)
                  ·
                    rfl

theorem cell20_18936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 4, 2].length) (baseStart_18936 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_18936 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_18936 prefixEnd_18936 := by exact prefixLift 18936
  have htrace : WordTrace (prefixWord ++ tailWord_18936) baseStart_18936 baseEnd_18936 := by
    simpa [prefixWord, tailWord_18936, baseEnd_18936] using wordTrace_append hprefix tailTrace_18936
  have hstable : (prefixWord ++ tailWord_18936).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18936).length < 2 ^ (prefixWord ++ tailWord_18936).sum := by decide
  have hdescent : baseEnd_18936 < baseStart_18936 := by decide
  rcases family_descends (prefixWord ++ tailWord_18936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18984 : List Nat := [2, 1, 5, 2, 1, 3, 1, 2, 3]
def baseStart_18984 : Nat := 118140960795 + 18984 * 2 ^ 59
def prefixEnd_18984 : Nat := 4983230072969 + 3 ^ 40 * 18984 * 2
def baseEnd_18984 : Nat := 8664814884496852189067

theorem tailTrace_18984 : CollatzResearch.WordTrace tailWord_18984 prefixEnd_18984 8664814884496852189067 := by
  unfold tailWord_18984
  simp only [CollatzResearch.WordTrace]
  refine ⟨346201681615842527092003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 461602242154456702789337 346201681615842527092003)
  ·
    refine ⟨519302522423763790638005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 346201681615842527092003 519302522423763790638005)
    ·
      refine ⟨48684611477227855372313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 519302522423763790638005 48684611477227855372313)
      ·
        refine ⟨36513458607920891529235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48684611477227855372313 36513458607920891529235)
        ·
          refine ⟨54770187911881337293853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36513458607920891529235 54770187911881337293853)
          ·
            refine ⟨20538820466955501485195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54770187911881337293853 20538820466955501485195)
            ·
              refine ⟨30808230700433252227793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20538820466955501485195 30808230700433252227793)
              ·
                refine ⟨23106173025324939170845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30808230700433252227793 23106173025324939170845)
                ·
                  refine ⟨8664814884496852189067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23106173025324939170845 8664814884496852189067)
                  ·
                    rfl

theorem cell20_18984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 2, 3].length) (baseStart_18984 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_18984 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_18984 prefixEnd_18984 := by exact prefixLift 18984
  have htrace : WordTrace (prefixWord ++ tailWord_18984) baseStart_18984 baseEnd_18984 := by
    simpa [prefixWord, tailWord_18984, baseEnd_18984] using wordTrace_append hprefix tailTrace_18984
  have hstable : (prefixWord ++ tailWord_18984).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18984).length < 2 ^ (prefixWord ++ tailWord_18984).sum := by decide
  have hdescent : baseEnd_18984 < baseStart_18984 := by decide
  rcases family_descends (prefixWord ++ tailWord_18984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18995 : List Nat := [1, 1, 1, 2, 4, 2, 4, 1, 4]
def baseStart_18995 : Nat := 118140960795 + 18995 * 2 ^ 59
def prefixEnd_18995 : Nat := 4983230072969 + 3 ^ 40 * 18995 * 2
def baseEnd_18995 : Nat := 8669835584229702822355

theorem tailTrace_18995 : CollatzResearch.WordTrace tailWord_18995 prefixEnd_18995 8669835584229702822355 := by
  unfold tailWord_18995
  simp only [CollatzResearch.WordTrace]
  refine ⟨692804566191833932834439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 461869710794555955222959 692804566191833932834439)
  ·
    refine ⟨1039206849287750899251659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 692804566191833932834439 1039206849287750899251659)
    ·
      refine ⟨1558810273931626348877489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1039206849287750899251659 1558810273931626348877489)
      ·
        refine ⟨1169107705448719761658117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1558810273931626348877489 1169107705448719761658117)
        ·
          refine ⟨219207694771634955310897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1169107705448719761658117 219207694771634955310897)
          ·
            refine ⟨164405771078726216483173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 219207694771634955310897 164405771078726216483173)
            ·
              refine ⟨30826082077261165590595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 164405771078726216483173 30826082077261165590595)
              ·
                refine ⟨46239123115891748385893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30826082077261165590595 46239123115891748385893)
                ·
                  refine ⟨8669835584229702822355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46239123115891748385893 8669835584229702822355)
                  ·
                    rfl

theorem cell20_18995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 1, 4].length) (baseStart_18995 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_18995 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_18995 prefixEnd_18995 := by exact prefixLift 18995
  have htrace : WordTrace (prefixWord ++ tailWord_18995) baseStart_18995 baseEnd_18995 := by
    simpa [prefixWord, tailWord_18995, baseEnd_18995] using wordTrace_append hprefix tailTrace_18995
  have hstable : (prefixWord ++ tailWord_18995).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18995).length < 2 ^ (prefixWord ++ tailWord_18995).sum := by decide
  have hdescent : baseEnd_18995 < baseStart_18995 := by decide
  rcases family_descends (prefixWord ++ tailWord_18995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19036 : List Nat := [2, 2, 4, 1, 4, 1, 6]
def baseStart_19036 : Nat := 118140960795 + 19036 * 2 ^ 59
def prefixEnd_19036 : Nat := 4983230072969 + 3 ^ 40 * 19036 * 2
def baseEnd_19036 : Nat := 965394344601753606169

theorem tailTrace_19036 : CollatzResearch.WordTrace tailWord_19036 prefixEnd_19036 965394344601753606169 := by
  unfold tailWord_19036
  simp only [CollatzResearch.WordTrace]
  refine ⟨347149979521648967538481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 462866639362198623384641 347149979521648967538481)
  ·
    refine ⟨260362484641236725653861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 347149979521648967538481 260362484641236725653861)
    ·
      refine ⟨48817965870231886060099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 260362484641236725653861 48817965870231886060099)
      ·
        refine ⟨73226948805347829090149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48817965870231886060099 73226948805347829090149)
        ·
          refine ⟨13730052901002717954403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73226948805347829090149 13730052901002717954403)
          ·
            refine ⟨20595079351504076931605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13730052901002717954403 20595079351504076931605)
            ·
              refine ⟨965394344601753606169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 20595079351504076931605 965394344601753606169)
              ·
                rfl

theorem cell20_19036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 6].length) (baseStart_19036 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_19036 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_19036 prefixEnd_19036 := by exact prefixLift 19036
  have htrace : WordTrace (prefixWord ++ tailWord_19036) baseStart_19036 baseEnd_19036 := by
    simpa [prefixWord, tailWord_19036, baseEnd_19036] using wordTrace_append hprefix tailTrace_19036
  have hstable : (prefixWord ++ tailWord_19036).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19036).length < 2 ^ (prefixWord ++ tailWord_19036).sum := by decide
  have hdescent : baseEnd_19036 < baseStart_19036 := by decide
  rcases family_descends (prefixWord ++ tailWord_19036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19098 : List Nat := [3, 1, 1, 6, 1, 1, 2, 2, 3]
def baseStart_19098 : Nat := 118140960795 + 19098 * 2 ^ 59
def prefixEnd_19098 : Nat := 4983230072969 + 3 ^ 40 * 19098 * 2
def baseEnd_19098 : Nat := 8716847590819122388601

theorem tailTrace_19098 : CollatzResearch.WordTrace tailWord_19098 prefixEnd_19098 8716847590819122388601 := by
  unfold tailWord_19098
  simp only [CollatzResearch.WordTrace]
  refine ⟨174140321204670630958487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 464374189879121682555965 174140321204670630958487)
  ·
    refine ⟨261210481807005946437731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174140321204670630958487 261210481807005946437731)
    ·
      refine ⟨391815722710508919656597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261210481807005946437731 391815722710508919656597)
      ·
        refine ⟨18366362002055105608903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 391815722710508919656597 18366362002055105608903)
        ·
          refine ⟨27549543003082658413355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18366362002055105608903 27549543003082658413355)
          ·
            refine ⟨41324314504623987620033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27549543003082658413355 41324314504623987620033)
            ·
              refine ⟨30993235878467990715025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41324314504623987620033 30993235878467990715025)
              ·
                refine ⟨23244926908850993036269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30993235878467990715025 23244926908850993036269)
                ·
                  refine ⟨8716847590819122388601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23244926908850993036269 8716847590819122388601)
                  ·
                    rfl

theorem cell20_19098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 2, 3].length) (baseStart_19098 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_19098 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_19098 prefixEnd_19098 := by exact prefixLift 19098
  have htrace : WordTrace (prefixWord ++ tailWord_19098) baseStart_19098 baseEnd_19098 := by
    simpa [prefixWord, tailWord_19098, baseEnd_19098] using wordTrace_append hprefix tailTrace_19098
  have hstable : (prefixWord ++ tailWord_19098).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19098).length < 2 ^ (prefixWord ++ tailWord_19098).sum := by decide
  have hdescent : baseEnd_19098 < baseStart_19098 := by decide
  rcases family_descends (prefixWord ++ tailWord_19098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19105 : List Nat := [1, 2, 3, 3, 3, 1, 1, 4, 2]
def baseStart_19105 : Nat := 118140960795 + 19105 * 2 ^ 59
def prefixEnd_19105 : Nat := 4983230072969 + 3 ^ 40 * 19105 * 2
def baseEnd_19105 : Nat := 8720042581558209155239

theorem tailTrace_19105 : CollatzResearch.WordTrace tailWord_19105 prefixEnd_19105 8720042581558209155239 := by
  unfold tailWord_19105
  simp only [CollatzResearch.WordTrace]
  refine ⟨696816595793322719338769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 464544397195548479559179 696816595793322719338769)
  ·
    refine ⟨522612446844992039504077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 696816595793322719338769 522612446844992039504077)
    ·
      refine ⟨195979667566872014814029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 522612446844992039504077 195979667566872014814029)
      ·
        refine ⟨73492375337577005555261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 195979667566872014814029 73492375337577005555261)
        ·
          refine ⟨27559640751591377083223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73492375337577005555261 27559640751591377083223)
          ·
            refine ⟨41339461127387065624835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27559640751591377083223 41339461127387065624835)
            ·
              refine ⟨62009191691080598437253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41339461127387065624835 62009191691080598437253)
              ·
                refine ⟨11626723442077612206985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62009191691080598437253 11626723442077612206985)
                ·
                  refine ⟨8720042581558209155239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11626723442077612206985 8720042581558209155239)
                  ·
                    rfl

theorem cell20_19105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 4, 2].length) (baseStart_19105 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_19105 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_19105 prefixEnd_19105 := by exact prefixLift 19105
  have htrace : WordTrace (prefixWord ++ tailWord_19105) baseStart_19105 baseEnd_19105 := by
    simpa [prefixWord, tailWord_19105, baseEnd_19105] using wordTrace_append hprefix tailTrace_19105
  have hstable : (prefixWord ++ tailWord_19105).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19105).length < 2 ^ (prefixWord ++ tailWord_19105).sum := by decide
  have hdescent : baseEnd_19105 < baseStart_19105 := by decide
  rcases family_descends (prefixWord ++ tailWord_19105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19133 : List Nat := [1, 4, 1, 2, 1, 4, 3, 4]
def baseStart_19133 : Nat := 118140960795 + 19133 * 2 ^ 59
def prefixEnd_19133 : Nat := 4983230072969 + 3 ^ 40 * 19133 * 2
def baseEnd_19133 : Nat := 2910940848171518740597

theorem tailTrace_19133 : CollatzResearch.WordTrace tailWord_19133 prefixEnd_19133 2910940848171518740597 := by
  unfold tailWord_19133
  simp only [CollatzResearch.WordTrace]
  refine ⟨697837839691883501358053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 465225226461255667572035 697837839691883501358053)
  ·
    refine ⟨130844594942228156504635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 697837839691883501358053 130844594942228156504635)
    ·
      refine ⟨196266892413342234756953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130844594942228156504635 196266892413342234756953)
      ·
        refine ⟨147200169310006676067715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 196266892413342234756953 147200169310006676067715)
        ·
          refine ⟨220800253965010014101573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147200169310006676067715 220800253965010014101573)
          ·
            refine ⟨41400047618439377644045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 220800253965010014101573 41400047618439377644045)
            ·
              refine ⟨15525017856914766616517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41400047618439377644045 15525017856914766616517)
              ·
                refine ⟨2910940848171518740597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15525017856914766616517 2910940848171518740597)
                ·
                  rfl

theorem cell20_19133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 3, 4].length) (baseStart_19133 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_19133 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_19133 prefixEnd_19133 := by exact prefixLift 19133
  have htrace : WordTrace (prefixWord ++ tailWord_19133) baseStart_19133 baseEnd_19133 := by
    simpa [prefixWord, tailWord_19133, baseEnd_19133] using wordTrace_append hprefix tailTrace_19133
  have hstable : (prefixWord ++ tailWord_19133).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19133).length < 2 ^ (prefixWord ++ tailWord_19133).sum := by decide
  have hdescent : baseEnd_19133 < baseStart_19133 := by decide
  rcases family_descends (prefixWord ++ tailWord_19133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19157 : List Nat := [1, 3, 2, 5, 1, 1, 1, 1, 5]
def baseStart_19157 : Nat := 118140960795 + 19157 * 2 ^ 59
def prefixEnd_19157 : Nat := 4983230072969 + 3 ^ 40 * 19157 * 2
def baseEnd_19157 : Nat := 8743776798477139421693

theorem tailTrace_19157 : CollatzResearch.WordTrace tailWord_19157 prefixEnd_19157 8743776798477139421693 := by
  unfold tailWord_19157
  simp only [CollatzResearch.WordTrace]
  refine ⟨698713191604935600231725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 465808794403290400154483 698713191604935600231725)
  ·
    refine ⟨262017446851850850086897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 698713191604935600231725 262017446851850850086897)
    ·
      refine ⟨196513085138888137565173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 262017446851850850086897 196513085138888137565173)
      ·
        refine ⟨18423101731770762896735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 196513085138888137565173 18423101731770762896735)
        ·
          refine ⟨27634652597656144345103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18423101731770762896735 27634652597656144345103)
          ·
            refine ⟨41451978896484216517655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27634652597656144345103 41451978896484216517655)
            ·
              refine ⟨62177968344726324776483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41451978896484216517655 62177968344726324776483)
              ·
                refine ⟨93266952517089487164725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62177968344726324776483 93266952517089487164725)
                ·
                  refine ⟨8743776798477139421693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 93266952517089487164725 8743776798477139421693)
                  ·
                    rfl

theorem cell20_19157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 1, 5].length) (baseStart_19157 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_19157 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_19157 prefixEnd_19157 := by exact prefixLift 19157
  have htrace : WordTrace (prefixWord ++ tailWord_19157) baseStart_19157 baseEnd_19157 := by
    simpa [prefixWord, tailWord_19157, baseEnd_19157] using wordTrace_append hprefix tailTrace_19157
  have hstable : (prefixWord ++ tailWord_19157).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19157).length < 2 ^ (prefixWord ++ tailWord_19157).sum := by decide
  have hdescent : baseEnd_19157 < baseStart_19157 := by decide
  rcases family_descends (prefixWord ++ tailWord_19157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19161 : List Nat := [1, 2, 1, 2, 3, 2, 3, 1, 5]
def baseStart_19161 : Nat := 118140960795 + 19161 * 2 ^ 59
def prefixEnd_19161 : Nat := 4983230072969 + 3 ^ 40 * 19161 * 2
def baseEnd_19161 : Nat := 8745602507470903288343

theorem tailTrace_19161 : CollatzResearch.WordTrace tailWord_19161 prefixEnd_19161 8745602507470903288343 := by
  unfold tailWord_19161
  simp only [CollatzResearch.WordTrace]
  refine ⟨698859083590444283377337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 465906055726962855584891 698859083590444283377337)
  ·
    refine ⟨524144312692833212533003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 698859083590444283377337 524144312692833212533003)
    ·
      refine ⟨786216469039249818799505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 524144312692833212533003 786216469039249818799505)
      ·
        refine ⟨589662351779437364099629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 786216469039249818799505 589662351779437364099629)
        ·
          refine ⟨221123381917289011537361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 589662351779437364099629 221123381917289011537361)
          ·
            refine ⟨165842536437966758653021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 221123381917289011537361 165842536437966758653021)
            ·
              refine ⟨62190951164237534494883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 165842536437966758653021 62190951164237534494883)
              ·
                refine ⟨93286426746356301742325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62190951164237534494883 93286426746356301742325)
                ·
                  refine ⟨8745602507470903288343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 93286426746356301742325 8745602507470903288343)
                  ·
                    rfl

theorem cell20_19161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 1, 5].length) (baseStart_19161 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_19161 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_19161 prefixEnd_19161 := by exact prefixLift 19161
  have htrace : WordTrace (prefixWord ++ tailWord_19161) baseStart_19161 baseEnd_19161 := by
    simpa [prefixWord, tailWord_19161, baseEnd_19161] using wordTrace_append hprefix tailTrace_19161
  have hstable : (prefixWord ++ tailWord_19161).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19161).length < 2 ^ (prefixWord ++ tailWord_19161).sum := by decide
  have hdescent : baseEnd_19161 < baseStart_19161 := by decide
  rcases family_descends (prefixWord ++ tailWord_19161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19164 : List Nat := [2, 2, 5, 1, 1, 1, 1, 3, 4]
def baseStart_19164 : Nat := 118140960795 + 19164 * 2 ^ 59
def prefixEnd_19164 : Nat := 4983230072969 + 3 ^ 40 * 19164 * 2
def baseEnd_19164 : Nat := 8746971789216226188331

theorem tailTrace_19164 : CollatzResearch.WordTrace tailWord_19164 prefixEnd_19164 8746971789216226188331 := by
  unfold tailWord_19164
  simp only [CollatzResearch.WordTrace]
  refine ⟨349484251289787897868273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 465979001719717197157697 349484251289787897868273)
  ·
    refine ⟨262113188467340923401205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 349484251289787897868273 262113188467340923401205)
    ·
      refine ⟨24573111418813211568863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 262113188467340923401205 24573111418813211568863)
      ·
        refine ⟨36859667128219817353295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24573111418813211568863 36859667128219817353295)
        ·
          refine ⟨55289500692329726029943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36859667128219817353295 55289500692329726029943)
          ·
            refine ⟨82934251038494589044915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55289500692329726029943 82934251038494589044915)
            ·
              refine ⟨124401376557741883567373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82934251038494589044915 124401376557741883567373)
              ·
                refine ⟨46650516209153206337765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 124401376557741883567373 46650516209153206337765)
                ·
                  refine ⟨8746971789216226188331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46650516209153206337765 8746971789216226188331)
                  ·
                    rfl

theorem cell20_19164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 3, 4].length) (baseStart_19164 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_19164 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_19164 prefixEnd_19164 := by exact prefixLift 19164
  have htrace : WordTrace (prefixWord ++ tailWord_19164) baseStart_19164 baseEnd_19164 := by
    simpa [prefixWord, tailWord_19164, baseEnd_19164] using wordTrace_append hprefix tailTrace_19164
  have hstable : (prefixWord ++ tailWord_19164).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19164).length < 2 ^ (prefixWord ++ tailWord_19164).sum := by decide
  have hdescent : baseEnd_19164 < baseStart_19164 := by decide
  rcases family_descends (prefixWord ++ tailWord_19164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19198 : List Nat := [4, 2, 2, 1, 2, 3, 1, 3, 2]
def baseStart_19198 : Nat := 118140960795 + 19198 * 2 ^ 59
def prefixEnd_19198 : Nat := 4983230072969 + 3 ^ 40 * 19198 * 2
def baseEnd_19198 : Nat := 8762490315663219054859

theorem tailTrace_19198 : CollatzResearch.WordTrace tailWord_19198 prefixEnd_19198 8762490315663219054859 := by
  unfold tailWord_19198
  simp only [CollatzResearch.WordTrace]
  refine ⟨87526073057049950309281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 466805722970933068316165 87526073057049950309281)
  ·
    refine ⟨65644554792787462731961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87526073057049950309281 65644554792787462731961)
    ·
      refine ⟨49233416094590597048971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65644554792787462731961 49233416094590597048971)
      ·
        refine ⟨73850124141885895573457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49233416094590597048971 73850124141885895573457)
        ·
          refine ⟨55387593106414421680093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73850124141885895573457 55387593106414421680093)
          ·
            refine ⟨20770347414905408130035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55387593106414421680093 20770347414905408130035)
            ·
              refine ⟨31155521122358112195053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20770347414905408130035 31155521122358112195053)
              ·
                refine ⟨11683320420884292073145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31155521122358112195053 11683320420884292073145)
                ·
                  refine ⟨8762490315663219054859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11683320420884292073145 8762490315663219054859)
                  ·
                    rfl

theorem cell20_19198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 3, 2].length) (baseStart_19198 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_19198 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_19198 prefixEnd_19198 := by exact prefixLift 19198
  have htrace : WordTrace (prefixWord ++ tailWord_19198) baseStart_19198 baseEnd_19198 := by
    simpa [prefixWord, tailWord_19198, baseEnd_19198] using wordTrace_append hprefix tailTrace_19198
  have hstable : (prefixWord ++ tailWord_19198).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19198).length < 2 ^ (prefixWord ++ tailWord_19198).sum := by decide
  have hdescent : baseEnd_19198 < baseStart_19198 := by decide
  rcases family_descends (prefixWord ++ tailWord_19198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19229 : List Nat := [1, 4, 2, 4, 1, 2, 2, 1, 3]
def baseStart_19229 : Nat := 118140960795 + 19229 * 2 ^ 59
def prefixEnd_19229 : Nat := 4983230072969 + 3 ^ 40 * 19229 * 2
def baseEnd_19229 : Nat := 8776639560364889021399

theorem tailTrace_19229 : CollatzResearch.WordTrace tailWord_19229 prefixEnd_19229 8776639560364889021399 := by
  unfold tailWord_19229
  simp only [CollatzResearch.WordTrace]
  refine ⟨701339247344091896852741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 467559498229394597901827 701339247344091896852741)
  ·
    refine ⟨131501108877017230659889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 701339247344091896852741 131501108877017230659889)
    ·
      refine ⟨98625831657762922994917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131501108877017230659889 98625831657762922994917)
      ·
        refine ⟨18492343435830548061547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 98625831657762922994917 18492343435830548061547)
        ·
          refine ⟨27738515153745822092321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18492343435830548061547 27738515153745822092321)
          ·
            refine ⟨20803886365309366569241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27738515153745822092321 20803886365309366569241)
            ·
              refine ⟨15602914773982024926931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20803886365309366569241 15602914773982024926931)
              ·
                refine ⟨23404372160973037390397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15602914773982024926931 23404372160973037390397)
                ·
                  refine ⟨8776639560364889021399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23404372160973037390397 8776639560364889021399)
                  ·
                    rfl

theorem cell20_19229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 2, 1, 3].length) (baseStart_19229 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_19229 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_19229 prefixEnd_19229 := by exact prefixLift 19229
  have htrace : WordTrace (prefixWord ++ tailWord_19229) baseStart_19229 baseEnd_19229 := by
    simpa [prefixWord, tailWord_19229, baseEnd_19229] using wordTrace_append hprefix tailTrace_19229
  have hstable : (prefixWord ++ tailWord_19229).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19229).length < 2 ^ (prefixWord ++ tailWord_19229).sum := by decide
  have hdescent : baseEnd_19229 < baseStart_19229 := by decide
  rcases family_descends (prefixWord ++ tailWord_19229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19244 : List Nat := [2, 2, 1, 1, 1, 4, 2, 1, 6]
def baseStart_19244 : Nat := 118140960795 + 19244 * 2 ^ 59
def prefixEnd_19244 : Nat := 4983230072969 + 3 ^ 40 * 19244 * 2
def baseEnd_19244 : Nat := 8783485969091503521337

theorem tailTrace_19244 : CollatzResearch.WordTrace tailWord_19244 prefixEnd_19244 8783485969091503521337 := by
  unfold tailWord_19244
  simp only [CollatzResearch.WordTrace]
  refine ⟨350943171144874729324393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 467924228193166305765857 350943171144874729324393)
  ·
    refine ⟨263207378358656046993295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 350943171144874729324393 263207378358656046993295)
    ·
      refine ⟨394811067537984070489943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263207378358656046993295 394811067537984070489943)
      ·
        refine ⟨592216601306976105734915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 394811067537984070489943 592216601306976105734915)
        ·
          refine ⟨888324901960464158602373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 592216601306976105734915 888324901960464158602373)
          ·
            refine ⟨166560919117587029737945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 888324901960464158602373 166560919117587029737945)
            ·
              refine ⟨124920689338190272303459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 166560919117587029737945 124920689338190272303459)
              ·
                refine ⟨187381034007285408455189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 124920689338190272303459 187381034007285408455189)
                ·
                  refine ⟨8783485969091503521337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 187381034007285408455189 8783485969091503521337)
                  ·
                    rfl

theorem cell20_19244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 6].length) (baseStart_19244 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_19244 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_19244 prefixEnd_19244 := by exact prefixLift 19244
  have htrace : WordTrace (prefixWord ++ tailWord_19244) baseStart_19244 baseEnd_19244 := by
    simpa [prefixWord, tailWord_19244, baseEnd_19244] using wordTrace_append hprefix tailTrace_19244
  have hstable : (prefixWord ++ tailWord_19244).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19244).length < 2 ^ (prefixWord ++ tailWord_19244).sum := by decide
  have hdescent : baseEnd_19244 < baseStart_19244 := by decide
  rcases family_descends (prefixWord ++ tailWord_19244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19270 : List Nat := [6, 1, 1, 2, 2, 2, 2, 2, 2]
def baseStart_19270 : Nat := 118140960795 + 19270 * 2 ^ 59
def prefixEnd_19270 : Nat := 4983230072969 + 3 ^ 40 * 19270 * 2
def baseEnd_19270 : Nat := 8795353077550968654565

theorem tailTrace_19270 : CollatzResearch.WordTrace tailWord_19270 prefixEnd_19270 8795353077550968654565 := by
  unfold tailWord_19270
  simp only [CollatzResearch.WordTrace]
  refine ⟨21963582506111121846727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 468556426797037266063509 21963582506111121846727)
  ·
    refine ⟨32945373759166682770091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21963582506111121846727 32945373759166682770091)
    ·
      refine ⟨49418060638750024155137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32945373759166682770091 49418060638750024155137)
      ·
        refine ⟨37063545479062518116353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49418060638750024155137 37063545479062518116353)
        ·
          refine ⟨27797659109296888587265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37063545479062518116353 27797659109296888587265)
          ·
            refine ⟨20848244331972666440449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27797659109296888587265 20848244331972666440449)
            ·
              refine ⟨15636183248979499830337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20848244331972666440449 15636183248979499830337)
              ·
                refine ⟨11727137436734624872753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15636183248979499830337 11727137436734624872753)
                ·
                  refine ⟨8795353077550968654565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11727137436734624872753 8795353077550968654565)
                  ·
                    rfl

theorem cell20_19270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_19270 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_19270 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_19270 prefixEnd_19270 := by exact prefixLift 19270
  have htrace : WordTrace (prefixWord ++ tailWord_19270) baseStart_19270 baseEnd_19270 := by
    simpa [prefixWord, tailWord_19270, baseEnd_19270] using wordTrace_append hprefix tailTrace_19270
  have hstable : (prefixWord ++ tailWord_19270).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19270).length < 2 ^ (prefixWord ++ tailWord_19270).sum := by decide
  have hdescent : baseEnd_19270 < baseStart_19270 := by decide
  rcases family_descends (prefixWord ++ tailWord_19270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19299 : List Nat := [1, 1, 1, 5, 3, 2, 1, 2, 4]
def baseStart_19299 : Nat := 118140960795 + 19299 * 2 ^ 59
def prefixEnd_19299 : Nat := 4983230072969 + 3 ^ 40 * 19299 * 2
def baseEnd_19299 : Nat := 8808589467755756687779

theorem tailTrace_19299 : CollatzResearch.WordTrace tailWord_19299 prefixEnd_19299 8808589467755756687779 := by
  unfold tailWord_19299
  simp only [CollatzResearch.WordTrace]
  refine ⟨703892357090493851900951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 469261571393662567933967 703892357090493851900951)
  ·
    refine ⟨1055838535635740777851427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 703892357090493851900951 1055838535635740777851427)
    ·
      refine ⟨1583757803453611166777141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1055838535635740777851427 1583757803453611166777141)
      ·
        refine ⟨148477294073776046885357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1583757803453611166777141 148477294073776046885357)
        ·
          refine ⟨55678985277666017582009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 148477294073776046885357 55678985277666017582009)
          ·
            refine ⟨41759238958249513186507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55678985277666017582009 41759238958249513186507)
            ·
              refine ⟨62638858437374269779761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41759238958249513186507 62638858437374269779761)
              ·
                refine ⟨46979143828030702334821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62638858437374269779761 46979143828030702334821)
                ·
                  refine ⟨8808589467755756687779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46979143828030702334821 8808589467755756687779)
                  ·
                    rfl

theorem cell20_19299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 2, 4].length) (baseStart_19299 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_19299 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_19299 prefixEnd_19299 := by exact prefixLift 19299
  have htrace : WordTrace (prefixWord ++ tailWord_19299) baseStart_19299 baseEnd_19299 := by
    simpa [prefixWord, tailWord_19299, baseEnd_19299] using wordTrace_append hprefix tailTrace_19299
  have hstable : (prefixWord ++ tailWord_19299).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19299).length < 2 ^ (prefixWord ++ tailWord_19299).sum := by decide
  have hdescent : baseEnd_19299 < baseStart_19299 := by decide
  rcases family_descends (prefixWord ++ tailWord_19299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19337 : List Nat := [1, 2, 1, 1, 5, 3, 2, 1, 4]
def baseStart_19337 : Nat := 118140960795 + 19337 * 2 ^ 59
def prefixEnd_19337 : Nat := 4983230072969 + 3 ^ 40 * 19337 * 2
def baseEnd_19337 : Nat := 8825933703196513420957

theorem tailTrace_19337 : CollatzResearch.WordTrace tailWord_19337 prefixEnd_19337 8825933703196513420957 := by
  unfold tailWord_19337
  simp only [CollatzResearch.WordTrace]
  refine ⟨705278330952826341784265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 470185553968550894522843 705278330952826341784265)
  ·
    refine ⟨528958748214619756338199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 705278330952826341784265 528958748214619756338199)
    ·
      refine ⟨793438122321929634507299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 528958748214619756338199 793438122321929634507299)
      ·
        refine ⟨1190157183482894451760949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 793438122321929634507299 1190157183482894451760949)
        ·
          refine ⟨111577235951521354852589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1190157183482894451760949 111577235951521354852589)
          ·
            refine ⟨41841463481820508069721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111577235951521354852589 41841463481820508069721)
            ·
              refine ⟨31381097611365381052291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41841463481820508069721 31381097611365381052291)
              ·
                refine ⟨47071646417048071578437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31381097611365381052291 47071646417048071578437)
                ·
                  refine ⟨8825933703196513420957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47071646417048071578437 8825933703196513420957)
                  ·
                    rfl

theorem cell20_19337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 1, 4].length) (baseStart_19337 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_19337 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_19337 prefixEnd_19337 := by exact prefixLift 19337
  have htrace : WordTrace (prefixWord ++ tailWord_19337) baseStart_19337 baseEnd_19337 := by
    simpa [prefixWord, tailWord_19337, baseEnd_19337] using wordTrace_append hprefix tailTrace_19337
  have hstable : (prefixWord ++ tailWord_19337).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19337).length < 2 ^ (prefixWord ++ tailWord_19337).sum := by decide
  have hdescent : baseEnd_19337 < baseStart_19337 := by decide
  rcases family_descends (prefixWord ++ tailWord_19337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19361 : List Nat := [1, 2, 3, 4, 1, 1, 4, 4]
def baseStart_19361 : Nat := 118140960795 + 19361 * 2 ^ 59
def prefixEnd_19361 : Nat := 4983230072969 + 3 ^ 40 * 19361 * 2
def baseEnd_19361 : Nat := 2945629319053032206953

theorem tailTrace_19361 : CollatzResearch.WordTrace tailWord_19361 prefixEnd_19361 2945629319053032206953 := by
  unfold tailWord_19361
  simp only [CollatzResearch.WordTrace]
  refine ⟨706153682865878440657937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 470769121910585627105291 706153682865878440657937)
  ·
    refine ⟨529615262149408830493453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 706153682865878440657937 529615262149408830493453)
    ·
      refine ⟨198605723306028311435045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 529615262149408830493453 198605723306028311435045)
      ·
        refine ⟨37238573119880308394071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 198605723306028311435045 37238573119880308394071)
        ·
          refine ⟨55857859679820462591107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37238573119880308394071 55857859679820462591107)
          ·
            refine ⟨83786789519730693886661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55857859679820462591107 83786789519730693886661)
            ·
              refine ⟨15710023034949505103749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 83786789519730693886661 15710023034949505103749)
              ·
                refine ⟨2945629319053032206953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15710023034949505103749 2945629319053032206953)
                ·
                  rfl

theorem cell20_19361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 4, 4].length) (baseStart_19361 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_19361 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_19361 prefixEnd_19361 := by exact prefixLift 19361
  have htrace : WordTrace (prefixWord ++ tailWord_19361) baseStart_19361 baseEnd_19361 := by
    simpa [prefixWord, tailWord_19361, baseEnd_19361] using wordTrace_append hprefix tailTrace_19361
  have hstable : (prefixWord ++ tailWord_19361).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19361).length < 2 ^ (prefixWord ++ tailWord_19361).sum := by decide
  have hdescent : baseEnd_19361 < baseStart_19361 := by decide
  rcases family_descends (prefixWord ++ tailWord_19361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19375 : List Nat := [1, 1, 2, 1, 2, 2, 2, 7, 2]
def baseStart_19375 : Nat := 118140960795 + 19375 * 2 ^ 59
def prefixEnd_19375 : Nat := 4983230072969 + 3 ^ 40 * 19375 * 2
def baseEnd_19375 : Nat := 8843277938637270154135

theorem tailTrace_19375 : CollatzResearch.WordTrace tailWord_19375 prefixEnd_19375 8843277938637270154135 := by
  unfold tailWord_19375
  simp only [CollatzResearch.WordTrace]
  refine ⟨706664304815158831667579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 471109536543439221111719 706664304815158831667579)
  ·
    refine ⟨1059996457222738247501369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 706664304815158831667579 1059996457222738247501369)
    ·
      refine ⟨794997342917053685626027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1059996457222738247501369 794997342917053685626027)
      ·
        refine ⟨1192496014375580528439041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 794997342917053685626027 1192496014375580528439041)
        ·
          refine ⟨894372010781685396329281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1192496014375580528439041 894372010781685396329281)
          ·
            refine ⟨670779008086264047246961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 894372010781685396329281 670779008086264047246961)
            ·
              refine ⟨503084256064698035435221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 670779008086264047246961 503084256064698035435221)
              ·
                refine ⟨11791037251516360205513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 503084256064698035435221 11791037251516360205513)
                ·
                  refine ⟨8843277938637270154135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11791037251516360205513 8843277938637270154135)
                  ·
                    rfl

theorem cell20_19375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 7, 2].length) (baseStart_19375 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_19375 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_19375 prefixEnd_19375 := by exact prefixLift 19375
  have htrace : WordTrace (prefixWord ++ tailWord_19375) baseStart_19375 baseEnd_19375 := by
    simpa [prefixWord, tailWord_19375, baseEnd_19375] using wordTrace_append hprefix tailTrace_19375
  have hstable : (prefixWord ++ tailWord_19375).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19375).length < 2 ^ (prefixWord ++ tailWord_19375).sum := by decide
  have hdescent : baseEnd_19375 < baseStart_19375 := by decide
  rcases family_descends (prefixWord ++ tailWord_19375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19398 : List Nat := [6, 1, 3, 1, 1, 1, 1, 3, 3]
def baseStart_19398 : Nat := 118140960795 + 19398 * 2 ^ 59
def prefixEnd_19398 : Nat := 4983230072969 + 3 ^ 40 * 19398 * 2
def baseEnd_19398 : Nat := 8853775765351412387375

theorem tailTrace_19398 : CollatzResearch.WordTrace tailWord_19398 prefixEnd_19398 8853775765351412387375 := by
  unfold tailWord_19398
  simp only [CollatzResearch.WordTrace]
  refine ⟨22109474491619804992339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 471668789154555839836565 22109474491619804992339)
  ·
    refine ⟨33164211737429707488509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22109474491619804992339 33164211737429707488509)
    ·
      refine ⟨12436579401536140308191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33164211737429707488509 12436579401536140308191)
      ·
        refine ⟨18654869102304210462287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12436579401536140308191 18654869102304210462287)
        ·
          refine ⟨27982303653456315693431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18654869102304210462287 27982303653456315693431)
          ·
            refine ⟨41973455480184473540147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27982303653456315693431 41973455480184473540147)
            ·
              refine ⟨62960183220276710310221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41973455480184473540147 62960183220276710310221)
              ·
                refine ⟨23610068707603766366333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62960183220276710310221 23610068707603766366333)
                ·
                  refine ⟨8853775765351412387375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23610068707603766366333 8853775765351412387375)
                  ·
                    rfl

theorem cell20_19398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_19398 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_19398 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_19398 prefixEnd_19398 := by exact prefixLift 19398
  have htrace : WordTrace (prefixWord ++ tailWord_19398) baseStart_19398 baseEnd_19398 := by
    simpa [prefixWord, tailWord_19398, baseEnd_19398] using wordTrace_append hprefix tailTrace_19398
  have hstable : (prefixWord ++ tailWord_19398).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19398).length < 2 ^ (prefixWord ++ tailWord_19398).sum := by decide
  have hdescent : baseEnd_19398 < baseStart_19398 := by decide
  rcases family_descends (prefixWord ++ tailWord_19398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19403 : List Nat := [1, 1, 1, 1, 3, 5, 1, 7]
def baseStart_19403 : Nat := 118140960795 + 19403 * 2 ^ 59
def prefixEnd_19403 : Nat := 4983230072969 + 3 ^ 40 * 19403 * 2
def baseEnd_19403 : Nat := 2952019300531205740229

theorem tailTrace_19403 : CollatzResearch.WordTrace tailWord_19403 prefixEnd_19403 2952019300531205740229 := by
  unfold tailWord_19403
  simp only [CollatzResearch.WordTrace]
  refine ⟨707685548713719613686863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 471790365809146409124575 707685548713719613686863)
  ·
    refine ⟨1061528323070579420530295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 707685548713719613686863 1061528323070579420530295)
    ·
      refine ⟨1592292484605869130795443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1061528323070579420530295 1592292484605869130795443)
      ·
        refine ⟨2388438726908803696193165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1592292484605869130795443 2388438726908803696193165)
        ·
          refine ⟨895664522590801386072437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2388438726908803696193165 895664522590801386072437)
          ·
            refine ⟨83968548992887629944291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 895664522590801386072437 83968548992887629944291)
            ·
              refine ⟨125952823489331444916437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83968548992887629944291 125952823489331444916437)
              ·
                refine ⟨2952019300531205740229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 125952823489331444916437 2952019300531205740229)
                ·
                  rfl

theorem cell20_19403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 7].length) (baseStart_19403 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_19403 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_19403 prefixEnd_19403 := by exact prefixLift 19403
  have htrace : WordTrace (prefixWord ++ tailWord_19403) baseStart_19403 baseEnd_19403 := by
    simpa [prefixWord, tailWord_19403, baseEnd_19403] using wordTrace_append hprefix tailTrace_19403
  have hstable : (prefixWord ++ tailWord_19403).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19403).length < 2 ^ (prefixWord ++ tailWord_19403).sum := by decide
  have hdescent : baseEnd_19403 < baseStart_19403 := by decide
  rcases family_descends (prefixWord ++ tailWord_19403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19406 : List Nat := [4, 1, 1, 1, 2, 4, 1, 3, 3]
def baseStart_19406 : Nat := 118140960795 + 19406 * 2 ^ 59
def prefixEnd_19406 : Nat := 4983230072969 + 3 ^ 40 * 19406 * 2
def baseEnd_19406 : Nat := 8857427183338940120675

theorem tailTrace_19406 : CollatzResearch.WordTrace tailWord_19406 prefixEnd_19406 8857427183338940120675 := by
  unfold tailWord_19406
  simp only [CollatzResearch.WordTrace]
  refine ⟨88474370962856390755759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 471863311801900750697381 88474370962856390755759)
  ·
    refine ⟨132711556444284586133639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88474370962856390755759 132711556444284586133639)
    ·
      refine ⟨199067334666426879200459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132711556444284586133639 199067334666426879200459)
      ·
        refine ⟨298601001999640318800689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199067334666426879200459 298601001999640318800689)
        ·
          refine ⟨223950751499730239100517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 298601001999640318800689 223950751499730239100517)
          ·
            refine ⟨41990765906199419831347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 223950751499730239100517 41990765906199419831347)
            ·
              refine ⟨62986148859299129747021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41990765906199419831347 62986148859299129747021)
              ·
                refine ⟨23619805822237173655133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62986148859299129747021 23619805822237173655133)
                ·
                  refine ⟨8857427183338940120675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23619805822237173655133 8857427183338940120675)
                  ·
                    rfl

theorem cell20_19406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 3, 3].length) (baseStart_19406 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_19406 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_19406 prefixEnd_19406 := by exact prefixLift 19406
  have htrace : WordTrace (prefixWord ++ tailWord_19406) baseStart_19406 baseEnd_19406 := by
    simpa [prefixWord, tailWord_19406, baseEnd_19406] using wordTrace_append hprefix tailTrace_19406
  have hstable : (prefixWord ++ tailWord_19406).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19406).length < 2 ^ (prefixWord ++ tailWord_19406).sum := by decide
  have hdescent : baseEnd_19406 < baseStart_19406 := by decide
  rcases family_descends (prefixWord ++ tailWord_19406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19441 : List Nat := [1, 2, 2, 2, 4, 9]
def baseStart_19441 : Nat := 118140960795 + 19441 * 2 ^ 59
def prefixEnd_19441 : Nat := 4983230072969 + 3 ^ 40 * 19441 * 2
def baseEnd_19441 : Nat := 328644523593865701995

theorem tailTrace_19441 : CollatzResearch.WordTrace tailWord_19441 prefixEnd_19441 328644523593865701995 := by
  unfold tailWord_19441
  simp only [CollatzResearch.WordTrace]
  refine ⟨709071522576052103570177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 472714348384034735713451 709071522576052103570177)
  ·
    refine ⟨531803641932039077677633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 709071522576052103570177 531803641932039077677633)
    ·
      refine ⟨398852731449029308258225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 531803641932039077677633 398852731449029308258225)
      ·
        refine ⟨299139548586771981193669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 398852731449029308258225 299139548586771981193669)
        ·
          refine ⟨56088665360019746473813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 299139548586771981193669 56088665360019746473813)
          ·
            refine ⟨328644523593865701995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 56088665360019746473813 328644523593865701995)
            ·
              rfl

theorem cell20_19441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 9].length) (baseStart_19441 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_19441 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_19441 prefixEnd_19441 := by exact prefixLift 19441
  have htrace : WordTrace (prefixWord ++ tailWord_19441) baseStart_19441 baseEnd_19441 := by
    simpa [prefixWord, tailWord_19441, baseEnd_19441] using wordTrace_append hprefix tailTrace_19441
  have hstable : (prefixWord ++ tailWord_19441).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19441).length < 2 ^ (prefixWord ++ tailWord_19441).sum := by decide
  have hdescent : baseEnd_19441 < baseStart_19441 := by decide
  rcases family_descends (prefixWord ++ tailWord_19441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19454 : List Nat := [4, 2, 2, 2, 2, 2, 1, 5]
def baseStart_19454 : Nat := 118140960795 + 19454 * 2 ^ 59
def prefixEnd_19454 : Nat := 4983230072969 + 3 ^ 40 * 19454 * 2
def baseEnd_19454 : Nat := 2959778563754702173493

theorem tailTrace_19454 : CollatzResearch.WordTrace tailWord_19454 prefixEnd_19454 2959778563754702173493 := by
  unfold tailWord_19454
  simp only [CollatzResearch.WordTrace]
  refine ⟨88693208941119415474177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 473030447685970215862277 88693208941119415474177)
  ·
    refine ⟨66519906705839561605633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88693208941119415474177 66519906705839561605633)
    ·
      refine ⟨49889930029379671204225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66519906705839561605633 49889930029379671204225)
      ·
        refine ⟨37417447522034753403169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49889930029379671204225 37417447522034753403169)
        ·
          refine ⟨28063085641526065052377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37417447522034753403169 28063085641526065052377)
          ·
            refine ⟨21047314231144548789283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28063085641526065052377 21047314231144548789283)
            ·
              refine ⟨31570971346716823183925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21047314231144548789283 31570971346716823183925)
              ·
                refine ⟨2959778563754702173493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31570971346716823183925 2959778563754702173493)
                ·
                  rfl

theorem cell20_19454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 5].length) (baseStart_19454 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_19454 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_19454 prefixEnd_19454 := by exact prefixLift 19454
  have htrace : WordTrace (prefixWord ++ tailWord_19454) baseStart_19454 baseEnd_19454 := by
    simpa [prefixWord, tailWord_19454, baseEnd_19454] using wordTrace_append hprefix tailTrace_19454
  have hstable : (prefixWord ++ tailWord_19454).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19454).length < 2 ^ (prefixWord ++ tailWord_19454).sum := by decide
  have hdescent : baseEnd_19454 < baseStart_19454 := by decide
  rcases family_descends (prefixWord ++ tailWord_19454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19485 : List Nat := [1, 4, 2, 2, 3, 1, 2, 3, 2]
def baseStart_19485 : Nat := 118140960795 + 19485 * 2 ^ 59
def prefixEnd_19485 : Nat := 4983230072969 + 3 ^ 40 * 19485 * 2
def baseEnd_19485 : Nat := 8893484935965776487019

theorem tailTrace_19485 : CollatzResearch.WordTrace tailWord_19485 prefixEnd_19485 8893484935965776487019 := by
  unfold tailWord_19485
  simp only [CollatzResearch.WordTrace]
  refine ⟨710676334416647618171909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 473784222944431745447939 710676334416647618171909)
  ·
    refine ⟨133251812703121428407233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 710676334416647618171909 133251812703121428407233)
    ·
      refine ⟨99938859527341071305425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133251812703121428407233 99938859527341071305425)
      ·
        refine ⟨74954144645505803479069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99938859527341071305425 74954144645505803479069)
        ·
          refine ⟨28107804242064676304651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74954144645505803479069 28107804242064676304651)
          ·
            refine ⟨42161706363097014456977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28107804242064676304651 42161706363097014456977)
            ·
              refine ⟨31621279772322760842733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42161706363097014456977 31621279772322760842733)
              ·
                refine ⟨11857979914621035316025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31621279772322760842733 11857979914621035316025)
                ·
                  refine ⟨8893484935965776487019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11857979914621035316025 8893484935965776487019)
                  ·
                    rfl

theorem cell20_19485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 3, 2].length) (baseStart_19485 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_19485 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_19485 prefixEnd_19485 := by exact prefixLift 19485
  have htrace : WordTrace (prefixWord ++ tailWord_19485) baseStart_19485 baseEnd_19485 := by
    simpa [prefixWord, tailWord_19485, baseEnd_19485] using wordTrace_append hprefix tailTrace_19485
  have hstable : (prefixWord ++ tailWord_19485).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19485).length < 2 ^ (prefixWord ++ tailWord_19485).sum := by decide
  have hdescent : baseEnd_19485 < baseStart_19485 := by decide
  rcases family_descends (prefixWord ++ tailWord_19485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19520 : List Nat := [2, 1, 1, 2, 2, 3, 5, 1, 3]
def baseStart_19520 : Nat := 118140960795 + 19520 * 2 ^ 59
def prefixEnd_19520 : Nat := 4983230072969 + 3 ^ 40 * 19520 * 2
def baseEnd_19520 : Nat := 8909459889661210320209

theorem tailTrace_19520 : CollatzResearch.WordTrace tailWord_19520 prefixEnd_19520 8909459889661210320209 := by
  unfold tailWord_19520
  simp only [CollatzResearch.WordTrace]
  refine ⟨355976444644924297848007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 474635259526565730464009 355976444644924297848007)
  ·
    refine ⟨533964666967386446772011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 355976444644924297848007 533964666967386446772011)
    ·
      refine ⟨800947000451079670158017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 533964666967386446772011 800947000451079670158017)
      ·
        refine ⟨600710250338309752618513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 800947000451079670158017 600710250338309752618513)
        ·
          refine ⟨450532687753732314463885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 600710250338309752618513 450532687753732314463885)
          ·
            refine ⟨168949757907649617923957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 450532687753732314463885 168949757907649617923957)
            ·
              refine ⟨15839039803842151680371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 168949757907649617923957 15839039803842151680371)
              ·
                refine ⟨23758559705763227520557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15839039803842151680371 23758559705763227520557)
                ·
                  refine ⟨8909459889661210320209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23758559705763227520557 8909459889661210320209)
                  ·
                    rfl

theorem cell20_19520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 5, 1, 3].length) (baseStart_19520 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_19520 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_19520 prefixEnd_19520 := by exact prefixLift 19520
  have htrace : WordTrace (prefixWord ++ tailWord_19520) baseStart_19520 baseEnd_19520 := by
    simpa [prefixWord, tailWord_19520, baseEnd_19520] using wordTrace_append hprefix tailTrace_19520
  have hstable : (prefixWord ++ tailWord_19520).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19520).length < 2 ^ (prefixWord ++ tailWord_19520).sum := by decide
  have hdescent : baseEnd_19520 < baseStart_19520 := by decide
  rcases family_descends (prefixWord ++ tailWord_19520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19565 : List Nat := [1, 5, 1, 1, 2, 2, 3, 1, 4]
def baseStart_19565 : Nat := 118140960795 + 19565 * 2 ^ 59
def prefixEnd_19565 : Nat := 4983230072969 + 3 ^ 40 * 19565 * 2
def baseEnd_19565 : Nat := 8929999115841053820025

theorem tailTrace_19565 : CollatzResearch.WordTrace tailWord_19565 prefixEnd_19565 8929999115841053820025 := by
  unfold tailWord_19565
  simp only [CollatzResearch.WordTrace]
  refine ⟨713594174126821281084149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 475729449417880854056099 713594174126821281084149)
  ·
    refine ⟨66899453824389495101639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 713594174126821281084149 66899453824389495101639)
    ·
      refine ⟨100349180736584242652459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66899453824389495101639 100349180736584242652459)
      ·
        refine ⟨150523771104876363978689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100349180736584242652459 150523771104876363978689)
        ·
          refine ⟨112892828328657272984017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150523771104876363978689 112892828328657272984017)
          ·
            refine ⟨84669621246492954738013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112892828328657272984017 84669621246492954738013)
            ·
              refine ⟨31751107967434858026755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84669621246492954738013 31751107967434858026755)
              ·
                refine ⟨47626661951152287040133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31751107967434858026755 47626661951152287040133)
                ·
                  refine ⟨8929999115841053820025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47626661951152287040133 8929999115841053820025)
                  ·
                    rfl

theorem cell20_19565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_19565 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_19565 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_19565 prefixEnd_19565 := by exact prefixLift 19565
  have htrace : WordTrace (prefixWord ++ tailWord_19565) baseStart_19565 baseEnd_19565 := by
    simpa [prefixWord, tailWord_19565, baseEnd_19565] using wordTrace_append hprefix tailTrace_19565
  have hstable : (prefixWord ++ tailWord_19565).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19565).length < 2 ^ (prefixWord ++ tailWord_19565).sum := by decide
  have hdescent : baseEnd_19565 < baseStart_19565 := by decide
  rcases family_descends (prefixWord ++ tailWord_19565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19593 : List Nat := [1, 2, 1, 1, 4, 3, 2, 6]
def baseStart_19593 : Nat := 118140960795 + 19593 * 2 ^ 59
def prefixEnd_19593 : Nat := 4983230072969 + 3 ^ 40 * 19593 * 2
def baseEnd_19593 : Nat := 2980926359599133628859

theorem tailTrace_19593 : CollatzResearch.WordTrace tailWord_19593 prefixEnd_19593 2980926359599133628859 := by
  unfold tailWord_19593
  simp only [CollatzResearch.WordTrace]
  refine ⟨714615418025382063103433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 476410278683588042068955 714615418025382063103433)
  ·
    refine ⟨535961563519036547327575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 714615418025382063103433 535961563519036547327575)
    ·
      refine ⟨803942345278554820991363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 535961563519036547327575 803942345278554820991363)
      ·
        refine ⟨1205913517917832231487045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 803942345278554820991363 1205913517917832231487045)
        ·
          refine ⟨226108784609593543403821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1205913517917832231487045 226108784609593543403821)
          ·
            refine ⟨84790794228597578776433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 226108784609593543403821 84790794228597578776433)
            ·
              refine ⟨63593095671448184082325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84790794228597578776433 63593095671448184082325)
              ·
                refine ⟨2980926359599133628859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 63593095671448184082325 2980926359599133628859)
                ·
                  rfl

theorem cell20_19593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 6].length) (baseStart_19593 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_19593 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_19593 prefixEnd_19593 := by exact prefixLift 19593
  have htrace : WordTrace (prefixWord ++ tailWord_19593) baseStart_19593 baseEnd_19593 := by
    simpa [prefixWord, tailWord_19593, baseEnd_19593] using wordTrace_append hprefix tailTrace_19593
  have hstable : (prefixWord ++ tailWord_19593).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19593).length < 2 ^ (prefixWord ++ tailWord_19593).sum := by decide
  have hdescent : baseEnd_19593 < baseStart_19593 := by decide
  rcases family_descends (prefixWord ++ tailWord_19593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19600 : List Nat := [2, 1, 1, 1, 1, 1, 4, 4, 5]
def baseStart_19600 : Nat := 118140960795 + 19600 * 2 ^ 59
def prefixEnd_19600 : Nat := 4983230072969 + 3 ^ 40 * 19600 * 2
def baseEnd_19600 : Nat := 8945974069536487653215

theorem tailTrace_19600 : CollatzResearch.WordTrace tailWord_19600 prefixEnd_19600 8945974069536487653215 := by
  unfold tailWord_19600
  simp only [CollatzResearch.WordTrace]
  refine ⟨357435364500011129304127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 476580486000014839072169 357435364500011129304127)
  ·
    refine ⟨536153046750016693956191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 357435364500011129304127 536153046750016693956191)
    ·
      refine ⟨804229570125025040934287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 536153046750016693956191 804229570125025040934287)
      ·
        refine ⟨1206344355187537561401431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 804229570125025040934287 1206344355187537561401431)
        ·
          refine ⟨1809516532781306342102147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1206344355187537561401431 1809516532781306342102147)
          ·
            refine ⟨2714274799171959513153221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1809516532781306342102147 2714274799171959513153221)
            ·
              refine ⟨508926524844742408716229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2714274799171959513153221 508926524844742408716229)
              ·
                refine ⟨95423723408389201634293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 508926524844742408716229 95423723408389201634293)
                ·
                  refine ⟨8945974069536487653215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 95423723408389201634293 8945974069536487653215)
                  ·
                    rfl

theorem cell20_19600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 4, 5].length) (baseStart_19600 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_19600 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_19600 prefixEnd_19600 := by exact prefixLift 19600
  have htrace : WordTrace (prefixWord ++ tailWord_19600) baseStart_19600 baseEnd_19600 := by
    simpa [prefixWord, tailWord_19600, baseEnd_19600] using wordTrace_append hprefix tailTrace_19600
  have hstable : (prefixWord ++ tailWord_19600).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19600).length < 2 ^ (prefixWord ++ tailWord_19600).sum := by decide
  have hdescent : baseEnd_19600 < baseStart_19600 := by decide
  rcases family_descends (prefixWord ++ tailWord_19600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19620 : List Nat := [2, 3, 1, 2, 3, 2, 1, 4, 2]
def baseStart_19620 : Nat := 118140960795 + 19620 * 2 ^ 59
def prefixEnd_19620 : Nat := 4983230072969 + 3 ^ 40 * 19620 * 2
def baseEnd_19620 : Nat := 8955102614505306986467

theorem tailTrace_19620 : CollatzResearch.WordTrace tailWord_19620 prefixEnd_19620 8955102614505306986467 := by
  unfold tailWord_19620
  simp only [CollatzResearch.WordTrace]
  refine ⟨357800094463782837168157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 477066792618377116224209 357800094463782837168157)
  ·
    refine ⟨134175035423918563938059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 357800094463782837168157 134175035423918563938059)
    ·
      refine ⟨201262553135877845907089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134175035423918563938059 201262553135877845907089)
      ·
        refine ⟨150946914851908384430317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 201262553135877845907089 150946914851908384430317)
        ·
          refine ⟨56605093069465644161369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 150946914851908384430317 56605093069465644161369)
          ·
            refine ⟨42453819802099233121027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56605093069465644161369 42453819802099233121027)
            ·
              refine ⟨63680729703148849681541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42453819802099233121027 63680729703148849681541)
              ·
                refine ⟨11940136819340409315289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63680729703148849681541 11940136819340409315289)
                ·
                  refine ⟨8955102614505306986467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11940136819340409315289 8955102614505306986467)
                  ·
                    rfl

theorem cell20_19620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 4, 2].length) (baseStart_19620 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_19620 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_19620 prefixEnd_19620 := by exact prefixLift 19620
  have htrace : WordTrace (prefixWord ++ tailWord_19620) baseStart_19620 baseEnd_19620 := by
    simpa [prefixWord, tailWord_19620, baseEnd_19620] using wordTrace_append hprefix tailTrace_19620
  have hstable : (prefixWord ++ tailWord_19620).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19620).length < 2 ^ (prefixWord ++ tailWord_19620).sum := by decide
  have hdescent : baseEnd_19620 < baseStart_19620 := by decide
  rcases family_descends (prefixWord ++ tailWord_19620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19631 : List Nat := [1, 1, 2, 1, 2, 3, 5, 5]
def baseStart_19631 : Nat := 118140960795 + 19631 * 2 ^ 59
def prefixEnd_19631 : Nat := 4983230072969 + 3 ^ 40 * 19631 * 2
def baseEnd_19631 : Nat := 2986707771412719206585

theorem tailTrace_19631 : CollatzResearch.WordTrace tailWord_19631 prefixEnd_19631 2986707771412719206585 := by
  unfold tailWord_19631
  simp only [CollatzResearch.WordTrace]
  refine ⟨716001391887714552986747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 477334261258476368657831 716001391887714552986747)
  ·
    refine ⟨1074002087831571829480121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 716001391887714552986747 1074002087831571829480121)
    ·
      refine ⟨805501565873678872110091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1074002087831571829480121 805501565873678872110091)
      ·
        refine ⟨1208252348810518308165137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 805501565873678872110091 1208252348810518308165137)
        ·
          refine ⟨906189261607888731123853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1208252348810518308165137 906189261607888731123853)
          ·
            refine ⟨339820973102958274171445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 906189261607888731123853 339820973102958274171445)
            ·
              refine ⟨31858216228402338203573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 339820973102958274171445 31858216228402338203573)
              ·
                refine ⟨2986707771412719206585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31858216228402338203573 2986707771412719206585)
                ·
                  rfl

theorem cell20_19631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 5].length) (baseStart_19631 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_19631 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_19631 prefixEnd_19631 := by exact prefixLift 19631
  have htrace : WordTrace (prefixWord ++ tailWord_19631) baseStart_19631 baseEnd_19631 := by
    simpa [prefixWord, tailWord_19631, baseEnd_19631] using wordTrace_append hprefix tailTrace_19631
  have hstable : (prefixWord ++ tailWord_19631).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19631).length < 2 ^ (prefixWord ++ tailWord_19631).sum := by decide
  have hdescent : baseEnd_19631 < baseStart_19631 := by decide
  rcases family_descends (prefixWord ++ tailWord_19631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19658 : List Nat := [3, 1, 2, 1, 3, 3, 2, 3, 2]
def baseStart_19658 : Nat := 118140960795 + 19658 * 2 ^ 59
def prefixEnd_19658 : Nat := 4983230072969 + 3 ^ 40 * 19658 * 2
def baseEnd_19658 : Nat := 8972446849946063719645

theorem tailTrace_19658 : CollatzResearch.WordTrace tailWord_19658 prefixEnd_19658 8972446849946063719645 := by
  unfold tailWord_19658
  simp only [CollatzResearch.WordTrace]
  refine ⟨179246540697474541054907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 477990775193265442813085 179246540697474541054907)
  ·
    refine ⟨268869811046211811582361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179246540697474541054907 268869811046211811582361)
    ·
      refine ⟨201652358284658858686771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 268869811046211811582361 201652358284658858686771)
      ·
        refine ⟨302478537426988288030157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201652358284658858686771 302478537426988288030157)
        ·
          refine ⟨113429451535120608011309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 302478537426988288030157 113429451535120608011309)
          ·
            refine ⟨42536044325670228004241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 113429451535120608011309 42536044325670228004241)
            ·
              refine ⟨31902033244252671003181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42536044325670228004241 31902033244252671003181)
              ·
                refine ⟨11963262466594751626193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31902033244252671003181 11963262466594751626193)
                ·
                  refine ⟨8972446849946063719645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11963262466594751626193 8972446849946063719645)
                  ·
                    rfl

theorem cell20_19658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 3, 2].length) (baseStart_19658 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_19658 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_19658 prefixEnd_19658 := by exact prefixLift 19658
  have htrace : WordTrace (prefixWord ++ tailWord_19658) baseStart_19658 baseEnd_19658 := by
    simpa [prefixWord, tailWord_19658, baseEnd_19658] using wordTrace_append hprefix tailTrace_19658
  have hstable : (prefixWord ++ tailWord_19658).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19658).length < 2 ^ (prefixWord ++ tailWord_19658).sum := by decide
  have hdescent : baseEnd_19658 < baseStart_19658 := by decide
  rcases family_descends (prefixWord ++ tailWord_19658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19668 : List Nat := [2, 4, 1, 4, 1, 2, 1, 2, 3]
def baseStart_19668 : Nat := 118140960795 + 19668 * 2 ^ 59
def prefixEnd_19668 : Nat := 4983230072969 + 3 ^ 40 * 19668 * 2
def baseEnd_19668 : Nat := 8977011122430473386271

theorem tailTrace_19668 : CollatzResearch.WordTrace tailWord_19668 prefixEnd_19668 8977011122430473386271 := by
  unfold tailWord_19668
  simp only [CollatzResearch.WordTrace]
  refine ⟨358675446376834936041829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 478233928502446581389105 358675446376834936041829)
  ·
    refine ⟨67251646195656550507843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 358675446376834936041829 67251646195656550507843)
    ·
      refine ⟨100877469293484825761765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67251646195656550507843 100877469293484825761765)
      ·
        refine ⟨18914525492528404830331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 100877469293484825761765 18914525492528404830331)
        ·
          refine ⟨28371788238792607245497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18914525492528404830331 28371788238792607245497)
          ·
            refine ⟨21278841179094455434123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28371788238792607245497 21278841179094455434123)
            ·
              refine ⟨31918261768641683151185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21278841179094455434123 31918261768641683151185)
              ·
                refine ⟨23938696326481262363389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31918261768641683151185 23938696326481262363389)
                ·
                  refine ⟨8977011122430473386271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23938696326481262363389 8977011122430473386271)
                  ·
                    rfl

theorem cell20_19668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 2, 3].length) (baseStart_19668 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_19668 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_19668 prefixEnd_19668 := by exact prefixLift 19668
  have htrace : WordTrace (prefixWord ++ tailWord_19668) baseStart_19668 baseEnd_19668 := by
    simpa [prefixWord, tailWord_19668, baseEnd_19668] using wordTrace_append hprefix tailTrace_19668
  have hstable : (prefixWord ++ tailWord_19668).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19668).length < 2 ^ (prefixWord ++ tailWord_19668).sum := by decide
  have hdescent : baseEnd_19668 < baseStart_19668 := by decide
  rcases family_descends (prefixWord ++ tailWord_19668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19679 : List Nat := [1, 1, 2, 3, 2, 1, 4, 4, 2]
def baseStart_19679 : Nat := 118140960795 + 19679 * 2 ^ 59
def prefixEnd_19679 : Nat := 4983230072969 + 3 ^ 40 * 19679 * 2
def baseEnd_19679 : Nat := 8982031822163324019559

theorem tailTrace_19679 : CollatzResearch.WordTrace tailWord_19679 prefixEnd_19679 8982031822163324019559 := by
  unfold tailWord_19679
  simp only [CollatzResearch.WordTrace]
  refine ⟨717752095713818750734091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 478501397142545833822727 717752095713818750734091)
  ·
    refine ⟨1076628143570728126101137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 717752095713818750734091 1076628143570728126101137)
    ·
      refine ⟨807471107678046094575853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1076628143570728126101137 807471107678046094575853)
      ·
        refine ⟨302801665379267285465945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 807471107678046094575853 302801665379267285465945)
        ·
          refine ⟨227101249034450464099459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 302801665379267285465945 227101249034450464099459)
          ·
            refine ⟨340651873551675696149189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 227101249034450464099459 340651873551675696149189)
            ·
              refine ⟨63872226290939193027973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 340651873551675696149189 63872226290939193027973)
              ·
                refine ⟨11976042429551098692745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63872226290939193027973 11976042429551098692745)
                ·
                  refine ⟨8982031822163324019559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11976042429551098692745 8982031822163324019559)
                  ·
                    rfl

theorem cell20_19679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 4, 2].length) (baseStart_19679 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_19679 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_19679 prefixEnd_19679 := by exact prefixLift 19679
  have htrace : WordTrace (prefixWord ++ tailWord_19679) baseStart_19679 baseEnd_19679 := by
    simpa [prefixWord, tailWord_19679, baseEnd_19679] using wordTrace_append hprefix tailTrace_19679
  have hstable : (prefixWord ++ tailWord_19679).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19679).length < 2 ^ (prefixWord ++ tailWord_19679).sum := by decide
  have hdescent : baseEnd_19679 < baseStart_19679 := by decide
  rcases family_descends (prefixWord ++ tailWord_19679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19730 : List Nat := [3, 2, 4, 2, 2, 1, 1, 1, 4]
def baseStart_19730 : Nat := 118140960795 + 19730 * 2 ^ 59
def prefixEnd_19730 : Nat := 4983230072969 + 3 ^ 40 * 19730 * 2
def baseEnd_19730 : Nat := 9005309611833813319351

theorem tailTrace_19730 : CollatzResearch.WordTrace tailWord_19730 prefixEnd_19730 9005309611833813319351 := by
  unfold tailWord_19730
  simp only [CollatzResearch.WordTrace]
  refine ⟨179903054632263615210161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 479741479019369640560429 179903054632263615210161)
  ·
    refine ⟨134927290974197711407621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179903054632263615210161 134927290974197711407621)
    ·
      refine ⟨25298867057662070888929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 134927290974197711407621 25298867057662070888929)
      ·
        refine ⟨18974150293246553166697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25298867057662070888929 18974150293246553166697)
        ·
          refine ⟨14230612719934914875023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18974150293246553166697 14230612719934914875023)
          ·
            refine ⟨21345919079902372312535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14230612719934914875023 21345919079902372312535)
            ·
              refine ⟨32018878619853558468803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21345919079902372312535 32018878619853558468803)
              ·
                refine ⟨48028317929780337703205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32018878619853558468803 48028317929780337703205)
                ·
                  refine ⟨9005309611833813319351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48028317929780337703205 9005309611833813319351)
                  ·
                    rfl

theorem cell20_19730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 1, 4].length) (baseStart_19730 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_19730 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_19730 prefixEnd_19730 := by exact prefixLift 19730
  have htrace : WordTrace (prefixWord ++ tailWord_19730) baseStart_19730 baseEnd_19730 := by
    simpa [prefixWord, tailWord_19730, baseEnd_19730] using wordTrace_append hprefix tailTrace_19730
  have hstable : (prefixWord ++ tailWord_19730).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19730).length < 2 ^ (prefixWord ++ tailWord_19730).sum := by decide
  have hdescent : baseEnd_19730 < baseStart_19730 := by decide
  rcases family_descends (prefixWord ++ tailWord_19730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19744 : List Nat := [2, 1, 1, 5, 4, 1, 2, 1, 3]
def baseStart_19744 : Nat := 118140960795 + 19744 * 2 ^ 59
def prefixEnd_19744 : Nat := 4983230072969 + 3 ^ 40 * 19744 * 2
def baseEnd_19744 : Nat := 9011699593311986852627

theorem tailTrace_19744 : CollatzResearch.WordTrace tailWord_19744 prefixEnd_19744 9011699593311986852627 := by
  unfold tailWord_19744
  simp only [CollatzResearch.WordTrace]
  refine ⟨360061420239167425925143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 480081893652223234566857 360061420239167425925143)
  ·
    refine ⟨540092130358751138887715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 360061420239167425925143 540092130358751138887715)
    ·
      refine ⟨810138195538126708331573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 540092130358751138887715 810138195538126708331573)
      ·
        refine ⟨75950455831699378906085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 810138195538126708331573 75950455831699378906085)
        ·
          refine ⟨14240710468443633544891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75950455831699378906085 14240710468443633544891)
          ·
            refine ⟨21361065702665450317337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14240710468443633544891 21361065702665450317337)
            ·
              refine ⟨16020799276999087738003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21361065702665450317337 16020799276999087738003)
              ·
                refine ⟨24031198915498631607005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16020799276999087738003 24031198915498631607005)
                ·
                  refine ⟨9011699593311986852627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24031198915498631607005 9011699593311986852627)
                  ·
                    rfl

theorem cell20_19744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 2, 1, 3].length) (baseStart_19744 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_19744 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_19744 prefixEnd_19744 := by exact prefixLift 19744
  have htrace : WordTrace (prefixWord ++ tailWord_19744) baseStart_19744 baseEnd_19744 := by
    simpa [prefixWord, tailWord_19744, baseEnd_19744] using wordTrace_append hprefix tailTrace_19744
  have hstable : (prefixWord ++ tailWord_19744).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19744).length < 2 ^ (prefixWord ++ tailWord_19744).sum := by decide
  have hdescent : baseEnd_19744 < baseStart_19744 := by decide
  rcases family_descends (prefixWord ++ tailWord_19744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19759 : List Nat := [1, 1, 2, 1, 2, 1, 3, 3, 6]
def baseStart_19759 : Nat := 118140960795 + 19759 * 2 ^ 59
def prefixEnd_19759 : Nat := 4983230072969 + 3 ^ 40 * 19759 * 2
def baseEnd_19759 : Nat := 9018546002038601352565

theorem tailTrace_19759 : CollatzResearch.WordTrace tailWord_19759 prefixEnd_19759 9018546002038601352565 := by
  unfold tailWord_19759
  simp only [CollatzResearch.WordTrace]
  refine ⟨720669935423992413646331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 480446623615994942430887 720669935423992413646331)
  ·
    refine ⟨1081004903135988620469497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 720669935423992413646331 1081004903135988620469497)
    ·
      refine ⟨810753677351991465352123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1081004903135988620469497 810753677351991465352123)
      ·
        refine ⟨1216130516027987198028185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 810753677351991465352123 1216130516027987198028185)
        ·
          refine ⟨912097887020990398521139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1216130516027987198028185 912097887020990398521139)
          ·
            refine ⟨1368146830531485597781709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 912097887020990398521139 1368146830531485597781709)
            ·
              refine ⟨513055061449307099168141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1368146830531485597781709 513055061449307099168141)
              ·
                refine ⟨192395648043490162188053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 513055061449307099168141 192395648043490162188053)
                ·
                  refine ⟨9018546002038601352565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 192395648043490162188053 9018546002038601352565)
                  ·
                    rfl

theorem cell20_19759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 6].length) (baseStart_19759 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_19759 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_19759 prefixEnd_19759 := by exact prefixLift 19759
  have htrace : WordTrace (prefixWord ++ tailWord_19759) baseStart_19759 baseEnd_19759 := by
    simpa [prefixWord, tailWord_19759, baseEnd_19759] using wordTrace_append hprefix tailTrace_19759
  have hstable : (prefixWord ++ tailWord_19759).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19759).length < 2 ^ (prefixWord ++ tailWord_19759).sum := by decide
  have hdescent : baseEnd_19759 < baseStart_19759 := by decide
  rcases family_descends (prefixWord ++ tailWord_19759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19793 : List Nat := [1, 2, 2, 1, 4, 1, 3, 4, 2]
def baseStart_19793 : Nat := 118140960795 + 19793 * 2 ^ 59
def prefixEnd_19793 : Nat := 4983230072969 + 3 ^ 40 * 19793 * 2
def baseEnd_19793 : Nat := 9034064528485594219093

theorem tailTrace_19793 : CollatzResearch.WordTrace tailWord_19793 prefixEnd_19793 9034064528485594219093 := by
  unfold tailWord_19793
  simp only [CollatzResearch.WordTrace]
  refine ⟨721910017300816220384033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 481273344867210813589355 721910017300816220384033)
  ·
    refine ⟨541432512975612165288025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 721910017300816220384033 541432512975612165288025)
    ·
      refine ⟨406074384731709123966019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 541432512975612165288025 406074384731709123966019)
      ·
        refine ⟨609111577097563685949029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 406074384731709123966019 609111577097563685949029)
        ·
          refine ⟨114208420705793191115443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 609111577097563685949029 114208420705793191115443)
          ·
            refine ⟨171312631058689786673165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114208420705793191115443 171312631058689786673165)
            ·
              refine ⟨64242236647008670002437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 171312631058689786673165 64242236647008670002437)
              ·
                refine ⟨12045419371314125625457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64242236647008670002437 12045419371314125625457)
                ·
                  refine ⟨9034064528485594219093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12045419371314125625457 9034064528485594219093)
                  ·
                    rfl

theorem cell20_19793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 4, 2].length) (baseStart_19793 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_19793 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_19793 prefixEnd_19793 := by exact prefixLift 19793
  have htrace : WordTrace (prefixWord ++ tailWord_19793) baseStart_19793 baseEnd_19793 := by
    simpa [prefixWord, tailWord_19793, baseEnd_19793] using wordTrace_append hprefix tailTrace_19793
  have hstable : (prefixWord ++ tailWord_19793).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19793).length < 2 ^ (prefixWord ++ tailWord_19793).sum := by decide
  have hdescent : baseEnd_19793 < baseStart_19793 := by decide
  rcases family_descends (prefixWord ++ tailWord_19793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19831 : List Nat := [1, 1, 3, 1, 1, 2, 6, 3, 2]
def baseStart_19831 : Nat := 118140960795 + 19831 * 2 ^ 59
def prefixEnd_19831 : Nat := 4983230072969 + 3 ^ 40 * 19831 * 2
def baseEnd_19831 : Nat := 9051408763926350952271

theorem tailTrace_19831 : CollatzResearch.WordTrace tailWord_19831 prefixEnd_19831 9051408763926350952271 := by
  unfold tailWord_19831
  simp only [CollatzResearch.WordTrace]
  refine ⟨723295991163148710267347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 482197327442099140178231 723295991163148710267347)
  ·
    refine ⟨1084943986744723065401021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 723295991163148710267347 1084943986744723065401021)
    ·
      refine ⟨406853995029271149525383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1084943986744723065401021 406853995029271149525383)
      ·
        refine ⟨610280992543906724288075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 406853995029271149525383 610280992543906724288075)
        ·
          refine ⟨915421488815860086432113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 610280992543906724288075 915421488815860086432113)
          ·
            refine ⟨686566116611895064824085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 915421488815860086432113 686566116611895064824085)
            ·
              refine ⟨32182786716182581163629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 686566116611895064824085 32182786716182581163629)
              ·
                refine ⟨12068545018568467936361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32182786716182581163629 12068545018568467936361)
                ·
                  refine ⟨9051408763926350952271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12068545018568467936361 9051408763926350952271)
                  ·
                    rfl

theorem cell20_19831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 3, 2].length) (baseStart_19831 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_19831 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_19831 prefixEnd_19831 := by exact prefixLift 19831
  have htrace : WordTrace (prefixWord ++ tailWord_19831) baseStart_19831 baseEnd_19831 := by
    simpa [prefixWord, tailWord_19831, baseEnd_19831] using wordTrace_append hprefix tailTrace_19831
  have hstable : (prefixWord ++ tailWord_19831).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19831).length < 2 ^ (prefixWord ++ tailWord_19831).sum := by decide
  have hdescent : baseEnd_19831 < baseStart_19831 := by decide
  rcases family_descends (prefixWord ++ tailWord_19831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19835 : List Nat := [1, 1, 1, 1, 1, 6, 1, 2, 6]
def baseStart_19835 : Nat := 118140960795 + 19835 * 2 ^ 59
def prefixEnd_19835 : Nat := 4983230072969 + 3 ^ 40 * 19835 * 2
def baseEnd_19835 : Nat := 9053234472920114818921

theorem tailTrace_19835 : CollatzResearch.WordTrace tailWord_19835 prefixEnd_19835 9053234472920114818921 := by
  unfold tailWord_19835
  simp only [CollatzResearch.WordTrace]
  refine ⟨723441883148657393412959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 482294588765771595608639 723441883148657393412959)
  ·
    refine ⟨1085162824722986090119439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 723441883148657393412959 1085162824722986090119439)
    ·
      refine ⟨1627744237084479135179159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1085162824722986090119439 1627744237084479135179159)
      ·
        refine ⟨2441616355626718702768739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1627744237084479135179159 2441616355626718702768739)
        ·
          refine ⟨3662424533440078054153109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2441616355626718702768739 3662424533440078054153109)
          ·
            refine ⟨171676150005003658788427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 3662424533440078054153109 171676150005003658788427)
            ·
              refine ⟨257514225007505488182641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 171676150005003658788427 257514225007505488182641)
              ·
                refine ⟨193135668755629116136981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 257514225007505488182641 193135668755629116136981)
                ·
                  refine ⟨9053234472920114818921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 193135668755629116136981 9053234472920114818921)
                  ·
                    rfl

theorem cell20_19835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 6].length) (baseStart_19835 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_19835 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_19835 prefixEnd_19835 := by exact prefixLift 19835
  have htrace : WordTrace (prefixWord ++ tailWord_19835) baseStart_19835 baseEnd_19835 := by
    simpa [prefixWord, tailWord_19835, baseEnd_19835] using wordTrace_append hprefix tailTrace_19835
  have hstable : (prefixWord ++ tailWord_19835).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19835).length < 2 ^ (prefixWord ++ tailWord_19835).sum := by decide
  have hdescent : baseEnd_19835 < baseStart_19835 := by decide
  rcases family_descends (prefixWord ++ tailWord_19835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19841 : List Nat := [1, 2, 4, 3, 2, 2, 1, 2, 3]
def baseStart_19841 : Nat := 118140960795 + 19841 * 2 ^ 59
def prefixEnd_19841 : Nat := 4983230072969 + 3 ^ 40 * 19841 * 2
def baseEnd_19841 : Nat := 9055973036410760618897

theorem tailTrace_19841 : CollatzResearch.WordTrace tailWord_19841 prefixEnd_19841 9055973036410760618897 := by
  unfold tailWord_19841
  simp only [CollatzResearch.WordTrace]
  refine ⟨723660721126920418131377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 482440480751280278754251 723660721126920418131377)
  ·
    refine ⟨542745540845190313598533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 723660721126920418131377 542745540845190313598533)
    ·
      refine ⟨101764788908473183799725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 542745540845190313598533 101764788908473183799725)
      ·
        refine ⟨38161795840677443924897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101764788908473183799725 38161795840677443924897)
        ·
          refine ⟨28621346880508082943673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38161795840677443924897 28621346880508082943673)
          ·
            refine ⟨21466010160381062207755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28621346880508082943673 21466010160381062207755)
            ·
              refine ⟨32199015240571593311633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21466010160381062207755 32199015240571593311633)
              ·
                refine ⟨24149261430428694983725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32199015240571593311633 24149261430428694983725)
                ·
                  refine ⟨9055973036410760618897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24149261430428694983725 9055973036410760618897)
                  ·
                    rfl

theorem cell20_19841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 2, 3].length) (baseStart_19841 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_19841 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_19841 prefixEnd_19841 := by exact prefixLift 19841
  have htrace : WordTrace (prefixWord ++ tailWord_19841) baseStart_19841 baseEnd_19841 := by
    simpa [prefixWord, tailWord_19841, baseEnd_19841] using wordTrace_append hprefix tailTrace_19841
  have hstable : (prefixWord ++ tailWord_19841).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19841).length < 2 ^ (prefixWord ++ tailWord_19841).sum := by decide
  have hdescent : baseEnd_19841 < baseStart_19841 := by decide
  rcases family_descends (prefixWord ++ tailWord_19841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19845 : List Nat := [1, 3, 1, 1, 3, 1, 5, 2, 3]
def baseStart_19845 : Nat := 118140960795 + 19845 * 2 ^ 59
def prefixEnd_19845 : Nat := 4983230072969 + 3 ^ 40 * 19845 * 2
def baseEnd_19845 : Nat := 9057798745404524485547

theorem tailTrace_19845 : CollatzResearch.WordTrace tailWord_19845 prefixEnd_19845 9057798745404524485547 := by
  unfold tailWord_19845
  simp only [CollatzResearch.WordTrace]
  refine ⟨723806613112429101276989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 482537742074952734184659 723806613112429101276989)
  ·
    refine ⟨271427479917160912978871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 723806613112429101276989 271427479917160912978871)
    ·
      refine ⟨407141219875741369468307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 271427479917160912978871 407141219875741369468307)
      ·
        refine ⟨610711829813612054202461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 407141219875741369468307 610711829813612054202461)
        ·
          refine ⟨229016936180104520325923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 610711829813612054202461 229016936180104520325923)
          ·
            refine ⟨343525404270156780488885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 229016936180104520325923 343525404270156780488885)
            ·
              refine ⟨32205506650327198170833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 343525404270156780488885 32205506650327198170833)
              ·
                refine ⟨24154129987745398628125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32205506650327198170833 24154129987745398628125)
                ·
                  refine ⟨9057798745404524485547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24154129987745398628125 9057798745404524485547)
                  ·
                    rfl

theorem cell20_19845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 2, 3].length) (baseStart_19845 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_19845 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_19845 prefixEnd_19845 := by exact prefixLift 19845
  have htrace : WordTrace (prefixWord ++ tailWord_19845) baseStart_19845 baseEnd_19845 := by
    simpa [prefixWord, tailWord_19845, baseEnd_19845] using wordTrace_append hprefix tailTrace_19845
  have hstable : (prefixWord ++ tailWord_19845).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19845).length < 2 ^ (prefixWord ++ tailWord_19845).sum := by decide
  have hdescent : baseEnd_19845 < baseStart_19845 := by decide
  rcases family_descends (prefixWord ++ tailWord_19845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19852 : List Nat := [2, 2, 1, 2, 1, 3, 4, 1, 4]
def baseStart_19852 : Nat := 118140960795 + 19852 * 2 ^ 59
def prefixEnd_19852 : Nat := 4983230072969 + 3 ^ 40 * 19852 * 2
def baseEnd_19852 : Nat := 9060993736143611252185

theorem tailTrace_19852 : CollatzResearch.WordTrace tailWord_19852 prefixEnd_19852 9060993736143611252185 := by
  unfold tailWord_19852
  simp only [CollatzResearch.WordTrace]
  refine ⟨362030962043534648390905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 482707949391379531187873 362030962043534648390905)
  ·
    refine ⟨271523221532650986293179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 362030962043534648390905 271523221532650986293179)
    ·
      refine ⟨407284832298976479439769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 271523221532650986293179 407284832298976479439769)
      ·
        refine ⟨305463624224232359579827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 407284832298976479439769 305463624224232359579827)
        ·
          refine ⟨458195436336348539369741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 305463624224232359579827 458195436336348539369741)
          ·
            refine ⟨171823288626130702263653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 458195436336348539369741 171823288626130702263653)
            ·
              refine ⟨32216866617399506674435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 171823288626130702263653 32216866617399506674435)
              ·
                refine ⟨48325299926099260011653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32216866617399506674435 48325299926099260011653)
                ·
                  refine ⟨9060993736143611252185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48325299926099260011653 9060993736143611252185)
                  ·
                    rfl

theorem cell20_19852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 1, 4].length) (baseStart_19852 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_19852 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_19852 prefixEnd_19852 := by exact prefixLift 19852
  have htrace : WordTrace (prefixWord ++ tailWord_19852) baseStart_19852 baseEnd_19852 := by
    simpa [prefixWord, tailWord_19852, baseEnd_19852] using wordTrace_append hprefix tailTrace_19852
  have hstable : (prefixWord ++ tailWord_19852).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19852).length < 2 ^ (prefixWord ++ tailWord_19852).sum := by decide
  have hdescent : baseEnd_19852 < baseStart_19852 := by decide
  rcases family_descends (prefixWord ++ tailWord_19852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19858 : List Nat := [3, 2, 3, 3, 1, 1, 3, 1, 3]
def baseStart_19858 : Nat := 118140960795 + 19858 * 2 ^ 59
def prefixEnd_19858 : Nat := 4983230072969 + 3 ^ 40 * 19858 * 2
def baseEnd_19858 : Nat := 9063732299634257052161

theorem tailTrace_19858 : CollatzResearch.WordTrace tailWord_19858 prefixEnd_19858 9063732299634257052161 := by
  unfold tailWord_19858
  simp only [CollatzResearch.WordTrace]
  refine ⟨181070190516333080375057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 482853841376888214333485 181070190516333080375057)
  ·
    refine ⟨135802642887249810281293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181070190516333080375057 135802642887249810281293)
    ·
      refine ⟨50925991082718678855485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135802642887249810281293 50925991082718678855485)
      ·
        refine ⟨19097246656019504570807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50925991082718678855485 19097246656019504570807)
        ·
          refine ⟨28645869984029256856211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19097246656019504570807 28645869984029256856211)
          ·
            refine ⟨42968804976043885284317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28645869984029256856211 42968804976043885284317)
            ·
              refine ⟨16113301866016456981619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42968804976043885284317 16113301866016456981619)
              ·
                refine ⟨24169952799024685472429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16113301866016456981619 24169952799024685472429)
                ·
                  refine ⟨9063732299634257052161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24169952799024685472429 9063732299634257052161)
                  ·
                    rfl

theorem cell20_19858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 3, 1, 3].length) (baseStart_19858 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_19858 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_19858 prefixEnd_19858 := by exact prefixLift 19858
  have htrace : WordTrace (prefixWord ++ tailWord_19858) baseStart_19858 baseEnd_19858 := by
    simpa [prefixWord, tailWord_19858, baseEnd_19858] using wordTrace_append hprefix tailTrace_19858
  have hstable : (prefixWord ++ tailWord_19858).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19858).length < 2 ^ (prefixWord ++ tailWord_19858).sum := by decide
  have hdescent : baseEnd_19858 < baseStart_19858 := by decide
  rcases family_descends (prefixWord ++ tailWord_19858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19904 : List Nat := [2, 1, 1, 2, 3, 1, 4, 1, 5]
def baseStart_19904 : Nat := 118140960795 + 19904 * 2 ^ 59
def prefixEnd_19904 : Nat := 4983230072969 + 3 ^ 40 * 19904 * 2
def baseEnd_19904 : Nat := 9084727953062541518639

theorem tailTrace_19904 : CollatzResearch.WordTrace tailWord_19904 prefixEnd_19904 9084727953062541518639 := by
  unfold tailWord_19904
  simp only [CollatzResearch.WordTrace]
  refine ⟨362979259949341088837383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 483972346599121451783177 362979259949341088837383)
  ·
    refine ⟨544468889924011633256075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 362979259949341088837383 544468889924011633256075)
    ·
      refine ⟨816703334886017449884113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 544468889924011633256075 816703334886017449884113)
      ·
        refine ⟨612527501164513087413085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 816703334886017449884113 612527501164513087413085)
        ·
          refine ⟨229697812936692407779907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 612527501164513087413085 229697812936692407779907)
          ·
            refine ⟨344546719405038611669861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 229697812936692407779907 344546719405038611669861)
            ·
              refine ⟨64602509888444739688099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 344546719405038611669861 64602509888444739688099)
              ·
                refine ⟨96903764832667109532149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64602509888444739688099 96903764832667109532149)
                ·
                  refine ⟨9084727953062541518639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 96903764832667109532149 9084727953062541518639)
                  ·
                    rfl

theorem cell20_19904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 1, 5].length) (baseStart_19904 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_19904 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_19904 prefixEnd_19904 := by exact prefixLift 19904
  have htrace : WordTrace (prefixWord ++ tailWord_19904) baseStart_19904 baseEnd_19904 := by
    simpa [prefixWord, tailWord_19904, baseEnd_19904] using wordTrace_append hprefix tailTrace_19904
  have hstable : (prefixWord ++ tailWord_19904).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19904).length < 2 ^ (prefixWord ++ tailWord_19904).sum := by decide
  have hdescent : baseEnd_19904 < baseStart_19904 := by decide
  rcases family_descends (prefixWord ++ tailWord_19904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19969 : List Nat := [1, 2, 4, 1, 5, 1, 1, 5]
def baseStart_19969 : Nat := 118140960795 + 19969 * 2 ^ 59
def prefixEnd_19969 : Nat := 4983230072969 + 3 ^ 40 * 19969 * 2
def baseEnd_19969 : Nat := 3038131908070401450569

theorem tailTrace_19969 : CollatzResearch.WordTrace tailWord_19969 prefixEnd_19969 3038131908070401450569 := by
  unfold tailWord_19969
  simp only [CollatzResearch.WordTrace]
  refine ⟨728329264663198278790961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 485552843108798852527307 728329264663198278790961)
  ·
    refine ⟨546246948497398709093221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 728329264663198278790961 546246948497398709093221)
    ·
      refine ⟨102421302843262257954979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 546246948497398709093221 102421302843262257954979)
      ·
        refine ⟨153631954264893386932469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102421302843262257954979 153631954264893386932469)
        ·
          refine ⟨14402995712333755024919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 153631954264893386932469 14402995712333755024919)
          ·
            refine ⟨21604493568500632537379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14402995712333755024919 21604493568500632537379)
            ·
              refine ⟨32406740352750948806069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21604493568500632537379 32406740352750948806069)
              ·
                refine ⟨3038131908070401450569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32406740352750948806069 3038131908070401450569)
                ·
                  rfl

theorem cell20_19969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 5].length) (baseStart_19969 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_19969 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_19969 prefixEnd_19969 := by exact prefixLift 19969
  have htrace : WordTrace (prefixWord ++ tailWord_19969) baseStart_19969 baseEnd_19969 := by
    simpa [prefixWord, tailWord_19969, baseEnd_19969] using wordTrace_append hprefix tailTrace_19969
  have hstable : (prefixWord ++ tailWord_19969).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19969).length < 2 ^ (prefixWord ++ tailWord_19969).sum := by decide
  have hdescent : baseEnd_19969 < baseStart_19969 := by decide
  rcases family_descends (prefixWord ++ tailWord_19969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19987 : List Nat := [1, 1, 1, 2, 1, 6, 1, 1, 6]
def baseStart_19987 : Nat := 118140960795 + 19987 * 2 ^ 59
def prefixEnd_19987 : Nat := 4983230072969 + 3 ^ 40 * 19987 * 2
def baseEnd_19987 : Nat := 9122611414683141751633

theorem tailTrace_19987 : CollatzResearch.WordTrace tailWord_19987 prefixEnd_19987 9122611414683141751633 := by
  unfold tailWord_19987
  simp only [CollatzResearch.WordTrace]
  refine ⟨728985778597987352946215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 485990519065324901964143 728985778597987352946215)
  ·
    refine ⟨1093478667896981029419323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 728985778597987352946215 1093478667896981029419323)
    ·
      refine ⟨1640218001845471544128985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1093478667896981029419323 1640218001845471544128985)
      ·
        refine ⟨1230163501384103658096739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1640218001845471544128985 1230163501384103658096739)
        ·
          refine ⟨1845245252076155487145109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1230163501384103658096739 1845245252076155487145109)
          ·
            refine ⟨86495871191069788459927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1845245252076155487145109 86495871191069788459927)
            ·
              refine ⟨129743806786604682689891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86495871191069788459927 129743806786604682689891)
              ·
                refine ⟨194615710179907024034837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 129743806786604682689891 194615710179907024034837)
                ·
                  refine ⟨9122611414683141751633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 194615710179907024034837 9122611414683141751633)
                  ·
                    rfl

theorem cell20_19987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 6].length) (baseStart_19987 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_19987 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_19987 prefixEnd_19987 := by exact prefixLift 19987
  have htrace : WordTrace (prefixWord ++ tailWord_19987) baseStart_19987 baseEnd_19987 := by
    simpa [prefixWord, tailWord_19987, baseEnd_19987] using wordTrace_append hprefix tailTrace_19987
  have hstable : (prefixWord ++ tailWord_19987).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19987).length < 2 ^ (prefixWord ++ tailWord_19987).sum := by decide
  have hdescent : baseEnd_19987 < baseStart_19987 := by decide
  rcases family_descends (prefixWord ++ tailWord_19987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20000 : List Nat := [2, 1, 1, 6, 1, 2, 2, 3, 2]
def baseStart_20000 : Nat := 118140960795 + 20000 * 2 ^ 59
def prefixEnd_20000 : Nat := 4983230072969 + 3 ^ 40 * 20000 * 2
def baseEnd_20000 : Nat := 9128544968912874318247

theorem tailTrace_20000 : CollatzResearch.WordTrace tailWord_20000 prefixEnd_20000 9128544968912874318247 := by
  unfold tailWord_20000
  simp only [CollatzResearch.WordTrace]
  refine ⟨364729963775445286584727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 486306618367260382112969 364729963775445286584727)
  ·
    refine ⟨547094945663167929877091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 364729963775445286584727 547094945663167929877091)
    ·
      refine ⟨820642418494751894815637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 547094945663167929877091 820642418494751894815637)
      ·
        refine ⟨38467613366941495069483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 820642418494751894815637 38467613366941495069483)
        ·
          refine ⟨57701420050412242604225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38467613366941495069483 57701420050412242604225)
          ·
            refine ⟨43276065037809181953169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57701420050412242604225 43276065037809181953169)
            ·
              refine ⟨32457048778356886464877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43276065037809181953169 32457048778356886464877)
              ·
                refine ⟨12171393291883832424329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32457048778356886464877 12171393291883832424329)
                ·
                  refine ⟨9128544968912874318247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12171393291883832424329 9128544968912874318247)
                  ·
                    rfl

theorem cell20_20000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 3, 2].length) (baseStart_20000 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_20000 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_20000 prefixEnd_20000 := by exact prefixLift 20000
  have htrace : WordTrace (prefixWord ++ tailWord_20000) baseStart_20000 baseEnd_20000 := by
    simpa [prefixWord, tailWord_20000, baseEnd_20000] using wordTrace_append hprefix tailTrace_20000
  have hstable : (prefixWord ++ tailWord_20000).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20000).length < 2 ^ (prefixWord ++ tailWord_20000).sum := by decide
  have hdescent : baseEnd_20000 < baseStart_20000 := by decide
  rcases family_descends (prefixWord ++ tailWord_20000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20014 : List Nat := [4, 1, 3, 1, 2, 1, 3, 2, 3]
def baseStart_20014 : Nat := 118140960795 + 20014 * 2 ^ 59
def prefixEnd_20014 : Nat := 4983230072969 + 3 ^ 40 * 20014 * 2
def baseEnd_20014 : Nat := 9134934950391047851523

theorem tailTrace_20014 : CollatzResearch.WordTrace tailWord_20014 prefixEnd_20014 9134934950391047851523 := by
  unfold tailWord_20014
  simp only [CollatzResearch.WordTrace]
  refine ⟨91246318687521370522387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 486647033000113976119397 91246318687521370522387)
  ·
    refine ⟨136869478031282055783581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91246318687521370522387 136869478031282055783581)
    ·
      refine ⟨51326054261730770918843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136869478031282055783581 51326054261730770918843)
      ·
        refine ⟨76989081392596156378265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51326054261730770918843 76989081392596156378265)
        ·
          refine ⟨57741811044447117283699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76989081392596156378265 57741811044447117283699)
          ·
            refine ⟨86612716566670675925549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57741811044447117283699 86612716566670675925549)
            ·
              refine ⟨32479768712501503472081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86612716566670675925549 32479768712501503472081)
              ·
                refine ⟨24359826534376127604061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32479768712501503472081 24359826534376127604061)
                ·
                  refine ⟨9134934950391047851523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24359826534376127604061 9134934950391047851523)
                  ·
                    rfl

theorem cell20_20014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 2, 3].length) (baseStart_20014 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_20014 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_20014 prefixEnd_20014 := by exact prefixLift 20014
  have htrace : WordTrace (prefixWord ++ tailWord_20014) baseStart_20014 baseEnd_20014 := by
    simpa [prefixWord, tailWord_20014, baseEnd_20014] using wordTrace_append hprefix tailTrace_20014
  have hstable : (prefixWord ++ tailWord_20014).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20014).length < 2 ^ (prefixWord ++ tailWord_20014).sum := by decide
  have hdescent : baseEnd_20014 < baseStart_20014 := by decide
  rcases family_descends (prefixWord ++ tailWord_20014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20021 : List Nat := [1, 3, 3, 1, 1, 3, 2, 4, 2]
def baseStart_20021 : Nat := 118140960795 + 20021 * 2 ^ 59
def prefixEnd_20021 : Nat := 4983230072969 + 3 ^ 40 * 20021 * 2
def baseEnd_20021 : Nat := 9138129941130134618161

theorem tailTrace_20021 : CollatzResearch.WordTrace tailWord_20021 prefixEnd_20021 9138129941130134618161 := by
  unfold tailWord_20021
  simp only [CollatzResearch.WordTrace]
  refine ⟨730225860474811159683917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 486817240316540773122611 730225860474811159683917)
  ·
    refine ⟨273834697678054184881469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 730225860474811159683917 273834697678054184881469)
    ·
      refine ⟨102688011629270319330551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 273834697678054184881469 102688011629270319330551)
      ·
        refine ⟨154032017443905478995827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102688011629270319330551 154032017443905478995827)
        ·
          refine ⟨231048026165858218493741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154032017443905478995827 231048026165858218493741)
          ·
            refine ⟨86643009812196831935153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 231048026165858218493741 86643009812196831935153)
            ·
              refine ⟨64982257359147623951365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86643009812196831935153 64982257359147623951365)
              ·
                refine ⟨12184173254840179490881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64982257359147623951365 12184173254840179490881)
                ·
                  refine ⟨9138129941130134618161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12184173254840179490881 9138129941130134618161)
                  ·
                    rfl

theorem cell20_20021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 4, 2].length) (baseStart_20021 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_20021 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_20021 prefixEnd_20021 := by exact prefixLift 20021
  have htrace : WordTrace (prefixWord ++ tailWord_20021) baseStart_20021 baseEnd_20021 := by
    simpa [prefixWord, tailWord_20021, baseEnd_20021] using wordTrace_append hprefix tailTrace_20021
  have hstable : (prefixWord ++ tailWord_20021).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20021).length < 2 ^ (prefixWord ++ tailWord_20021).sum := by decide
  have hdescent : baseEnd_20021 < baseStart_20021 := by decide
  rcases family_descends (prefixWord ++ tailWord_20021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20032 : List Nat := [2, 1, 1, 2, 2, 2, 1, 9]
def baseStart_20032 : Nat := 118140960795 + 20032 * 2 ^ 59
def prefixEnd_20032 : Nat := 4983230072969 + 3 ^ 40 * 20032 * 2
def baseEnd_20032 : Nat := 3047716880287661750483

theorem tailTrace_20032 : CollatzResearch.WordTrace tailWord_20032 prefixEnd_20032 3047716880287661750483 := by
  unfold tailWord_20032
  simp only [CollatzResearch.WordTrace]
  refine ⟨365313531717480019167175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 487084708956640025556233 365313531717480019167175)
  ·
    refine ⟨547970297576220028750763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 365313531717480019167175 547970297576220028750763)
    ·
      refine ⟨821955446364330043126145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 547970297576220028750763 821955446364330043126145)
      ·
        refine ⟨616466584773247532344609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 821955446364330043126145 616466584773247532344609)
        ·
          refine ⟨462349938579935649258457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 616466584773247532344609 462349938579935649258457)
          ·
            refine ⟨346762453934951736943843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 462349938579935649258457 346762453934951736943843)
            ·
              refine ⟨520143680902427605415765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 346762453934951736943843 520143680902427605415765)
              ·
                refine ⟨3047716880287661750483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 520143680902427605415765 3047716880287661750483)
                ·
                  rfl

theorem cell20_20032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 9].length) (baseStart_20032 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_20032 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_20032 prefixEnd_20032 := by exact prefixLift 20032
  have htrace : WordTrace (prefixWord ++ tailWord_20032) baseStart_20032 baseEnd_20032 := by
    simpa [prefixWord, tailWord_20032, baseEnd_20032] using wordTrace_append hprefix tailTrace_20032
  have hstable : (prefixWord ++ tailWord_20032).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20032).length < 2 ^ (prefixWord ++ tailWord_20032).sum := by decide
  have hdescent : baseEnd_20032 < baseStart_20032 := by decide
  rcases family_descends (prefixWord ++ tailWord_20032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20080 : List Nat := [2, 1, 1, 1, 6, 1, 3, 1, 4]
def baseStart_20080 : Nat := 118140960795 + 20080 * 2 ^ 59
def prefixEnd_20080 : Nat := 4983230072969 + 3 ^ 40 * 20080 * 2
def baseEnd_20080 : Nat := 9165059148788151651253

theorem tailTrace_20080 : CollatzResearch.WordTrace tailWord_20080 prefixEnd_20080 9165059148788151651253 := by
  unfold tailWord_20080
  simp only [CollatzResearch.WordTrace]
  refine ⟨366188883630532118040847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 488251844840709490721129 366188883630532118040847)
  ·
    refine ⟨549283325445798177061271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 366188883630532118040847 549283325445798177061271)
    ·
      refine ⟨823924988168697265591907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 549283325445798177061271 823924988168697265591907)
      ·
        refine ⟨1235887482253045898387861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 823924988168697265591907 1235887482253045898387861)
        ·
          refine ⟨57932225730611526486931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 1235887482253045898387861 57932225730611526486931)
          ·
            refine ⟨86898338595917289730397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57932225730611526486931 86898338595917289730397)
            ·
              refine ⟨32586876973468983648899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86898338595917289730397 32586876973468983648899)
              ·
                refine ⟨48880315460203475473349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32586876973468983648899 48880315460203475473349)
                ·
                  refine ⟨9165059148788151651253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48880315460203475473349 9165059148788151651253)
                  ·
                    rfl

theorem cell20_20080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 1, 4].length) (baseStart_20080 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_20080 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_20080 prefixEnd_20080 := by exact prefixLift 20080
  have htrace : WordTrace (prefixWord ++ tailWord_20080) baseStart_20080 baseEnd_20080 := by
    simpa [prefixWord, tailWord_20080, baseEnd_20080] using wordTrace_append hprefix tailTrace_20080
  have hstable : (prefixWord ++ tailWord_20080).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20080).length < 2 ^ (prefixWord ++ tailWord_20080).sum := by decide
  have hdescent : baseEnd_20080 < baseStart_20080 := by decide
  rcases family_descends (prefixWord ++ tailWord_20080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20101 : List Nat := [1, 3, 1, 1, 4, 1, 2, 1, 6]
def baseStart_20101 : Nat := 118140960795 + 20101 * 2 ^ 59
def prefixEnd_20101 : Nat := 4983230072969 + 3 ^ 40 * 20101 * 2
def baseEnd_20101 : Nat := 9174644121005411951167

theorem tailTrace_20101 : CollatzResearch.WordTrace tailWord_20101 prefixEnd_20101 9174644121005411951167 := by
  unfold tailWord_20101
  simp only [CollatzResearch.WordTrace]
  refine ⟨733143700184984822596157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 488762466789989881730771 733143700184984822596157)
  ·
    refine ⟨274928887569369308473559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 733143700184984822596157 274928887569369308473559)
    ·
      refine ⟨412393331354053962710339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 274928887569369308473559 412393331354053962710339)
      ·
        refine ⟨618589997031080944065509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 412393331354053962710339 618589997031080944065509)
        ·
          refine ⟨115985624443327677012283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 618589997031080944065509 115985624443327677012283)
          ·
            refine ⟨173978436664991515518425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115985624443327677012283 173978436664991515518425)
            ·
              refine ⟨130483827498743636638819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 173978436664991515518425 130483827498743636638819)
              ·
                refine ⟨195725741248115454958229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130483827498743636638819 195725741248115454958229)
                ·
                  refine ⟨9174644121005411951167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 195725741248115454958229 9174644121005411951167)
                  ·
                    rfl

theorem cell20_20101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 6].length) (baseStart_20101 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_20101 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_20101 prefixEnd_20101 := by exact prefixLift 20101
  have htrace : WordTrace (prefixWord ++ tailWord_20101) baseStart_20101 baseEnd_20101 := by
    simpa [prefixWord, tailWord_20101, baseEnd_20101] using wordTrace_append hprefix tailTrace_20101
  have hstable : (prefixWord ++ tailWord_20101).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20101).length < 2 ^ (prefixWord ++ tailWord_20101).sum := by decide
  have hdescent : baseEnd_20101 < baseStart_20101 := by decide
  rcases family_descends (prefixWord ++ tailWord_20101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20108 : List Nat := [2, 2, 1, 2, 1, 1, 3, 8]
def baseStart_20108 : Nat := 118140960795 + 20108 * 2 ^ 59
def prefixEnd_20108 : Nat := 4983230072969 + 3 ^ 40 * 20108 * 2
def baseEnd_20108 : Nat := 3059279703914832905935

theorem tailTrace_20108 : CollatzResearch.WordTrace tailWord_20108 prefixEnd_20108 3059279703914832905935 := by
  unfold tailWord_20108
  simp only [CollatzResearch.WordTrace]
  refine ⟨366699505579812509050489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 488932674106416678733985 366699505579812509050489)
  ·
    refine ⟨275024629184859381787867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 366699505579812509050489 275024629184859381787867)
    ·
      refine ⟨412536943777289072681801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275024629184859381787867 412536943777289072681801)
      ·
        refine ⟨309402707832966804511351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 412536943777289072681801 309402707832966804511351)
        ·
          refine ⟨464104061749450206767027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 309402707832966804511351 464104061749450206767027)
          ·
            refine ⟨696156092624175310150541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 464104061749450206767027 696156092624175310150541)
            ·
              refine ⟨261058534734065741306453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 696156092624175310150541 261058534734065741306453)
              ·
                refine ⟨3059279703914832905935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 261058534734065741306453 3059279703914832905935)
                ·
                  rfl

theorem cell20_20108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 8].length) (baseStart_20108 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_20108 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_20108 prefixEnd_20108 := by exact prefixLift 20108
  have htrace : WordTrace (prefixWord ++ tailWord_20108) baseStart_20108 baseEnd_20108 := by
    simpa [prefixWord, tailWord_20108, baseEnd_20108] using wordTrace_append hprefix tailTrace_20108
  have hstable : (prefixWord ++ tailWord_20108).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20108).length < 2 ^ (prefixWord ++ tailWord_20108).sum := by decide
  have hdescent : baseEnd_20108 < baseStart_20108 := by decide
  rcases family_descends (prefixWord ++ tailWord_20108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20156 : List Nat := [2, 2, 2, 3, 1, 3, 1, 2, 4]
def baseStart_20156 : Nat := 118140960795 + 20156 * 2 ^ 59
def prefixEnd_20156 : Nat := 4983230072969 + 3 ^ 40 * 20156 * 2
def baseEnd_20156 : Nat := 9199747619669665117609

theorem tailTrace_20156 : CollatzResearch.WordTrace tailWord_20156 prefixEnd_20156 9199747619669665117609 := by
  unfold tailWord_20156
  simp only [CollatzResearch.WordTrace]
  refine ⟨367574857492864607924161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 490099809990486143898881 367574857492864607924161)
  ·
    refine ⟨275681143119648455943121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 367574857492864607924161 275681143119648455943121)
    ·
      refine ⟨206760857339736341957341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 275681143119648455943121 206760857339736341957341)
      ·
        refine ⟨77535321502401128234003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 206760857339736341957341 77535321502401128234003)
        ·
          refine ⟨116302982253601692351005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77535321502401128234003 116302982253601692351005)
          ·
            refine ⟨43613618345100634631627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116302982253601692351005 43613618345100634631627)
            ·
              refine ⟨65420427517650951947441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43613618345100634631627 65420427517650951947441)
              ·
                refine ⟨49065320638238213960581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65420427517650951947441 49065320638238213960581)
                ·
                  refine ⟨9199747619669665117609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49065320638238213960581 9199747619669665117609)
                  ·
                    rfl

theorem cell20_20156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 2, 4].length) (baseStart_20156 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_20156 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_20156 prefixEnd_20156 := by exact prefixLift 20156
  have htrace : WordTrace (prefixWord ++ tailWord_20156) baseStart_20156 baseEnd_20156 := by
    simpa [prefixWord, tailWord_20156, baseEnd_20156] using wordTrace_append hprefix tailTrace_20156
  have hstable : (prefixWord ++ tailWord_20156).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20156).length < 2 ^ (prefixWord ++ tailWord_20156).sum := by decide
  have hdescent : baseEnd_20156 < baseStart_20156 := by decide
  rcases family_descends (prefixWord ++ tailWord_20156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20184 : List Nat := [2, 1, 2, 2, 3, 1, 9]
def baseStart_20184 : Nat := 118140960795 + 20184 * 2 ^ 59
def prefixEnd_20184 : Nat := 4983230072969 + 3 ^ 40 * 20184 * 2
def baseEnd_20184 : Nat := 1023614175847334687129

theorem tailTrace_20184 : CollatzResearch.WordTrace tailWord_20184 prefixEnd_20184 1023614175847334687129 := by
  unfold tailWord_20184
  simp only [CollatzResearch.WordTrace]
  refine ⟨368085479442144998933803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 490780639256193331911737 368085479442144998933803)
  ·
    refine ⟨552128219163217498400705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 368085479442144998933803 552128219163217498400705)
    ·
      refine ⟨414096164372413123800529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 552128219163217498400705 414096164372413123800529)
      ·
        refine ⟨310572123279309842850397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 414096164372413123800529 310572123279309842850397)
        ·
          refine ⟨116464546229741191068899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 310572123279309842850397 116464546229741191068899)
          ·
            refine ⟨174696819344611786603349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116464546229741191068899 174696819344611786603349)
            ·
              refine ⟨1023614175847334687129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 174696819344611786603349 1023614175847334687129)
              ·
                rfl

theorem cell20_20184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 9].length) (baseStart_20184 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_20184 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_20184 prefixEnd_20184 := by exact prefixLift 20184
  have htrace : WordTrace (prefixWord ++ tailWord_20184) baseStart_20184 baseEnd_20184 := by
    simpa [prefixWord, tailWord_20184, baseEnd_20184] using wordTrace_append hprefix tailTrace_20184
  have hstable : (prefixWord ++ tailWord_20184).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20184).length < 2 ^ (prefixWord ++ tailWord_20184).sum := by decide
  have hdescent : baseEnd_20184 < baseStart_20184 := by decide
  rcases family_descends (prefixWord ++ tailWord_20184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20215 : List Nat := [1, 1, 3, 1, 1, 1, 6, 2, 4]
def baseStart_20215 : Nat := 118140960795 + 20215 * 2 ^ 59
def prefixEnd_20215 : Nat := 4983230072969 + 3 ^ 40 * 20215 * 2
def baseEnd_20215 : Nat := 9226676827327682150701

theorem tailTrace_20215 : CollatzResearch.WordTrace tailWord_20215 prefixEnd_20215 9226676827327682150701 := by
  unfold tailWord_20215
  simp only [CollatzResearch.WordTrace]
  refine ⟨737301621771982292246099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 491534414514654861497399 737301621771982292246099)
  ·
    refine ⟨1105952432657973438369149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 737301621771982292246099 1105952432657973438369149)
    ·
      refine ⟨414732162246740039388431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1105952432657973438369149 414732162246740039388431)
      ·
        refine ⟨622098243370110059082647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 414732162246740039388431 622098243370110059082647)
        ·
          refine ⟨933147365055165088623971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 622098243370110059082647 933147365055165088623971)
          ·
            refine ⟨1399721047582747632935957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 933147365055165088623971 1399721047582747632935957)
            ·
              refine ⟨65611924105441295293873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1399721047582747632935957 65611924105441295293873)
              ·
                refine ⟨49208943079080971470405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65611924105441295293873 49208943079080971470405)
                ·
                  refine ⟨9226676827327682150701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49208943079080971470405 9226676827327682150701)
                  ·
                    rfl

theorem cell20_20215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 2, 4].length) (baseStart_20215 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_20215 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_20215 prefixEnd_20215 := by exact prefixLift 20215
  have htrace : WordTrace (prefixWord ++ tailWord_20215) baseStart_20215 baseEnd_20215 := by
    simpa [prefixWord, tailWord_20215, baseEnd_20215] using wordTrace_append hprefix tailTrace_20215
  have hstable : (prefixWord ++ tailWord_20215).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20215).length < 2 ^ (prefixWord ++ tailWord_20215).sum := by decide
  have hdescent : baseEnd_20215 < baseStart_20215 := by decide
  rcases family_descends (prefixWord ++ tailWord_20215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20228 : List Nat := [2, 3, 2, 2, 1, 4, 1, 3, 2]
def baseStart_20228 : Nat := 118140960795 + 20228 * 2 ^ 59
def prefixEnd_20228 : Nat := 4983230072969 + 3 ^ 40 * 20228 * 2
def baseEnd_20228 : Nat := 9232610381557414717315

theorem tailTrace_20228 : CollatzResearch.WordTrace tailWord_20228 prefixEnd_20228 9232610381557414717315 := by
  unfold tailWord_20228
  simp only [CollatzResearch.WordTrace]
  refine ⟨368887885362442756234669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 491850513816590341646225 368887885362442756234669)
  ·
    refine ⟨138332957010916033588001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 368887885362442756234669 138332957010916033588001)
    ·
      refine ⟨103749717758187025191001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138332957010916033588001 103749717758187025191001)
      ·
        refine ⟨77812288318640268893251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103749717758187025191001 77812288318640268893251)
        ·
          refine ⟨116718432477960403339877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77812288318640268893251 116718432477960403339877)
          ·
            refine ⟨21884706089617575626227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 116718432477960403339877 21884706089617575626227)
            ·
              refine ⟨32827059134426363439341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21884706089617575626227 32827059134426363439341)
              ·
                refine ⟨12310147175409886289753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32827059134426363439341 12310147175409886289753)
                ·
                  refine ⟨9232610381557414717315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12310147175409886289753 9232610381557414717315)
                  ·
                    rfl

theorem cell20_20228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 3, 2].length) (baseStart_20228 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_20228 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_20228 prefixEnd_20228 := by exact prefixLift 20228
  have htrace : WordTrace (prefixWord ++ tailWord_20228) baseStart_20228 baseEnd_20228 := by
    simpa [prefixWord, tailWord_20228, baseEnd_20228] using wordTrace_append hprefix tailTrace_20228
  have hstable : (prefixWord ++ tailWord_20228).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20228).length < 2 ^ (prefixWord ++ tailWord_20228).sum := by decide
  have hdescent : baseEnd_20228 < baseStart_20228 := by decide
  rcases family_descends (prefixWord ++ tailWord_20228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20294 : List Nat := [6, 1, 1, 2, 1, 9]
def baseStart_20294 : Nat := 118140960795 + 20294 * 2 ^ 59
def prefixEnd_20294 : Nat := 4983230072969 + 3 ^ 40 * 20294 * 2
def baseEnd_20294 : Nat := 343064243702019204335

theorem tailTrace_20294 : CollatzResearch.WordTrace tailWord_20294 prefixEnd_20294 343064243702019204335 := by
  unfold tailWord_20294
  simp only [CollatzResearch.WordTrace]
  refine ⟨23130718390180587011623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 493455325657185856247957 23130718390180587011623)
  ·
    refine ⟨34696077585270880517435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23130718390180587011623 34696077585270880517435)
    ·
      refine ⟨52044116377906320776153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34696077585270880517435 52044116377906320776153)
      ·
        refine ⟨39033087283429740582115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52044116377906320776153 39033087283429740582115)
        ·
          refine ⟨58549630925144610873173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39033087283429740582115 58549630925144610873173)
          ·
            refine ⟨343064243702019204335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 58549630925144610873173 343064243702019204335)
            ·
              rfl

theorem cell20_20294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 9].length) (baseStart_20294 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_20294 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_20294 prefixEnd_20294 := by exact prefixLift 20294
  have htrace : WordTrace (prefixWord ++ tailWord_20294) baseStart_20294 baseEnd_20294 := by
    simpa [prefixWord, tailWord_20294, baseEnd_20294] using wordTrace_append hprefix tailTrace_20294
  have hstable : (prefixWord ++ tailWord_20294).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20294).length < 2 ^ (prefixWord ++ tailWord_20294).sum := by decide
  have hdescent : baseEnd_20294 < baseStart_20294 := by decide
  rcases family_descends (prefixWord ++ tailWord_20294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20346 : List Nat := [3, 1, 1, 1, 1, 1, 5, 5, 2]
def baseStart_20346 : Nat := 118140960795 + 20346 * 2 ^ 59
def prefixEnd_20346 : Nat := 4983230072969 + 3 ^ 40 * 20346 * 2
def baseEnd_20346 : Nat := 9286468796873448783499

theorem tailTrace_20346 : CollatzResearch.WordTrace tailWord_20346 prefixEnd_20346 9286468796873448783499 := by
  unfold tailWord_20346
  simp only [CollatzResearch.WordTrace]
  refine ⟨185519896074347916316223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 494719722864927776843261 185519896074347916316223)
  ·
    refine ⟨278279844111521874474335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185519896074347916316223 278279844111521874474335)
    ·
      refine ⟨417419766167282811711503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278279844111521874474335 417419766167282811711503)
      ·
        refine ⟨626129649250924217567255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 417419766167282811711503 626129649250924217567255)
        ·
          refine ⟨939194473876386326350883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 626129649250924217567255 939194473876386326350883)
          ·
            refine ⟨1408791710814579489526325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 939194473876386326350883 1408791710814579489526325)
            ·
              refine ⟨132074222888866827143093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1408791710814579489526325 132074222888866827143093)
              ·
                refine ⟨12381958395831265044665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 132074222888866827143093 12381958395831265044665)
                ·
                  refine ⟨9286468796873448783499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12381958395831265044665 9286468796873448783499)
                  ·
                    rfl

theorem cell20_20346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 5, 2].length) (baseStart_20346 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_20346 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_20346 prefixEnd_20346 := by exact prefixLift 20346
  have htrace : WordTrace (prefixWord ++ tailWord_20346) baseStart_20346 baseEnd_20346 := by
    simpa [prefixWord, tailWord_20346, baseEnd_20346] using wordTrace_append hprefix tailTrace_20346
  have hstable : (prefixWord ++ tailWord_20346).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20346).length < 2 ^ (prefixWord ++ tailWord_20346).sum := by decide
  have hdescent : baseEnd_20346 < baseStart_20346 := by decide
  rcases family_descends (prefixWord ++ tailWord_20346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20391 : List Nat := [1, 1, 6, 1, 2, 2, 1, 6]
def baseStart_20391 : Nat := 118140960795 + 20391 * 2 ^ 59
def prefixEnd_20391 : Nat := 4983230072969 + 3 ^ 40 * 20391 * 2
def baseEnd_20391 : Nat := 3102336007684430761105

theorem tailTrace_20391 : CollatzResearch.WordTrace tailWord_20391 prefixEnd_20391 3102336007684430761105 := by
  unfold tailWord_20391
  simp only [CollatzResearch.WordTrace]
  refine ⟨743720869134364350653027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 495813912756242900435351 743720869134364350653027)
  ·
    refine ⟨1115581303701546525979541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 743720869134364350653027 1115581303701546525979541)
    ·
      refine ⟨52292873611009993405291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 1115581303701546525979541 52292873611009993405291)
      ·
        refine ⟨78439310416514990107937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52292873611009993405291 78439310416514990107937)
        ·
          refine ⟨58829482812386242580953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78439310416514990107937 58829482812386242580953)
          ·
            refine ⟨44122112109289681935715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58829482812386242580953 44122112109289681935715)
            ·
              refine ⟨66183168163934522903573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44122112109289681935715 66183168163934522903573)
              ·
                refine ⟨3102336007684430761105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 66183168163934522903573 3102336007684430761105)
                ·
                  rfl

theorem cell20_20391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 6].length) (baseStart_20391 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_20391 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_20391 prefixEnd_20391 := by exact prefixLift 20391
  have htrace : WordTrace (prefixWord ++ tailWord_20391) baseStart_20391 baseEnd_20391 := by
    simpa [prefixWord, tailWord_20391, baseEnd_20391] using wordTrace_append hprefix tailTrace_20391
  have hstable : (prefixWord ++ tailWord_20391).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20391).length < 2 ^ (prefixWord ++ tailWord_20391).sum := by decide
  have hdescent : baseEnd_20391 < baseStart_20391 := by decide
  rcases family_descends (prefixWord ++ tailWord_20391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20401 : List Nat := [1, 2, 2, 4, 2, 1, 3, 3, 2]
def baseStart_20401 : Nat := 118140960795 + 20401 * 2 ^ 59
def prefixEnd_20401 : Nat := 4983230072969 + 3 ^ 40 * 20401 * 2
def baseEnd_20401 : Nat := 9311572295537701949941

theorem tailTrace_20401 : CollatzResearch.WordTrace tailWord_20401 prefixEnd_20401 9311572295537701949941 := by
  unfold tailWord_20401
  simp only [CollatzResearch.WordTrace]
  refine ⟨744085599098136058517057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 496057066065424039011371 744085599098136058517057)
  ·
    refine ⟨558064199323602043887793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 744085599098136058517057 558064199323602043887793)
    ·
      refine ⟨418548149492701532915845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 558064199323602043887793 418548149492701532915845)
      ·
        refine ⟨78477778029881537421721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 418548149492701532915845 78477778029881537421721)
        ·
          refine ⟨58858333522411153066291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78477778029881537421721 58858333522411153066291)
          ·
            refine ⟨88287500283616729599437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58858333522411153066291 88287500283616729599437)
            ·
              refine ⟨33107812606356273599789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88287500283616729599437 33107812606356273599789)
              ·
                refine ⟨12415429727383602599921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33107812606356273599789 12415429727383602599921)
                ·
                  refine ⟨9311572295537701949941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12415429727383602599921 9311572295537701949941)
                  ·
                    rfl

theorem cell20_20401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 3, 2].length) (baseStart_20401 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_20401 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_20401 prefixEnd_20401 := by exact prefixLift 20401
  have htrace : WordTrace (prefixWord ++ tailWord_20401) baseStart_20401 baseEnd_20401 := by
    simpa [prefixWord, tailWord_20401, baseEnd_20401] using wordTrace_append hprefix tailTrace_20401
  have hstable : (prefixWord ++ tailWord_20401).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20401).length < 2 ^ (prefixWord ++ tailWord_20401).sum := by decide
  have hdescent : baseEnd_20401 < baseStart_20401 := by decide
  rcases family_descends (prefixWord ++ tailWord_20401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20470 : List Nat := [5, 1, 1, 1, 4, 1, 2, 2, 3]
def baseStart_20470 : Nat := 118140960795 + 20470 * 2 ^ 59
def prefixEnd_20470 : Nat := 4983230072969 + 3 ^ 40 * 20470 * 2
def baseEnd_20470 : Nat := 9343065775680128649659

theorem tailTrace_20470 : CollatzResearch.WordTrace tailWord_20470 prefixEnd_20470 9343065775680128649659 := by
  unfold tailWord_20470
  simp only [CollatzResearch.WordTrace]
  refine ⟨46662639740510052673679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 497734823898773895185909 46662639740510052673679)
  ·
    refine ⟨69993959610765079010519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46662639740510052673679 69993959610765079010519)
    ·
      refine ⟨104990939416147618515779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69993959610765079010519 104990939416147618515779)
      ·
        refine ⟨157486409124221427773669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104990939416147618515779 157486409124221427773669)
        ·
          refine ⟨29528701710791517707563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 157486409124221427773669 29528701710791517707563)
          ·
            refine ⟨44293052566187276561345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29528701710791517707563 44293052566187276561345)
            ·
              refine ⟨33219789424640457421009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44293052566187276561345 33219789424640457421009)
              ·
                refine ⟨24914842068480343065757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33219789424640457421009 24914842068480343065757)
                ·
                  refine ⟨9343065775680128649659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24914842068480343065757 9343065775680128649659)
                  ·
                    rfl

theorem cell20_20470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_20470 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_20470 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_20470 prefixEnd_20470 := by exact prefixLift 20470
  have htrace : WordTrace (prefixWord ++ tailWord_20470) baseStart_20470 baseEnd_20470 := by
    simpa [prefixWord, tailWord_20470, baseEnd_20470] using wordTrace_append hprefix tailTrace_20470
  have hstable : (prefixWord ++ tailWord_20470).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20470).length < 2 ^ (prefixWord ++ tailWord_20470).sum := by decide
  have hdescent : baseEnd_20470 < baseStart_20470 := by decide
  rcases family_descends (prefixWord ++ tailWord_20470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20477 : List Nat := [1, 4, 1, 1, 1, 2, 6, 2, 2]
def baseStart_20477 : Nat := 118140960795 + 20477 * 2 ^ 59
def prefixEnd_20477 : Nat := 4983230072969 + 3 ^ 40 * 20477 * 2
def baseEnd_20477 : Nat := 9346260766419215416297

theorem tailTrace_20477 : CollatzResearch.WordTrace tailWord_20477 prefixEnd_20477 9346260766419215416297 := by
  unfold tailWord_20477
  simp only [CollatzResearch.WordTrace]
  refine ⟨746857546822801038283685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 497905031215200692189123 746857546822801038283685)
  ·
    refine ⟨140035790029275194678191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 746857546822801038283685 140035790029275194678191)
    ·
      refine ⟨210053685043912792017287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140035790029275194678191 210053685043912792017287)
      ·
        refine ⟨315080527565869188025931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210053685043912792017287 315080527565869188025931)
        ·
          refine ⟨472620791348803782038897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 315080527565869188025931 472620791348803782038897)
          ·
            refine ⟨354465593511602836529173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 472620791348803782038897 354465593511602836529173)
            ·
              refine ⟨16615574695856382962305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 354465593511602836529173 16615574695856382962305)
              ·
                refine ⟨12461681021892287221729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16615574695856382962305 12461681021892287221729)
                ·
                  refine ⟨9346260766419215416297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12461681021892287221729 9346260766419215416297)
                  ·
                    rfl

theorem cell20_20477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 6, 2, 2].length) (baseStart_20477 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_20477 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_20477 prefixEnd_20477 := by exact prefixLift 20477
  have htrace : WordTrace (prefixWord ++ tailWord_20477) baseStart_20477 baseEnd_20477 := by
    simpa [prefixWord, tailWord_20477, baseEnd_20477] using wordTrace_append hprefix tailTrace_20477
  have hstable : (prefixWord ++ tailWord_20477).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20477).length < 2 ^ (prefixWord ++ tailWord_20477).sum := by decide
  have hdescent : baseEnd_20477 < baseStart_20477 := by decide
  rcases family_descends (prefixWord ++ tailWord_20477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20481 : List Nat := [1, 2, 4, 1, 2, 1, 2, 3, 4]
def baseStart_20481 : Nat := 118140960795 + 20481 * 2 ^ 59
def prefixEnd_20481 : Nat := 4983230072969 + 3 ^ 40 * 20481 * 2
def baseEnd_20481 : Nat := 9348086475412979282947

theorem tailTrace_20481 : CollatzResearch.WordTrace tailWord_20481 prefixEnd_20481 9348086475412979282947 := by
  unfold tailWord_20481
  simp only [CollatzResearch.WordTrace]
  refine ⟨747003438808309721429297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 498002292538873147619531 747003438808309721429297)
  ·
    refine ⟨560252579106232291071973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 747003438808309721429297 560252579106232291071973)
    ·
      refine ⟨105047358582418554575995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 560252579106232291071973 105047358582418554575995)
      ·
        refine ⟨157571037873627831863993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105047358582418554575995 157571037873627831863993)
        ·
          refine ⟨118178278405220873897995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157571037873627831863993 118178278405220873897995)
          ·
            refine ⟨177267417607831310846993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118178278405220873897995 177267417607831310846993)
            ·
              refine ⟨132950563205873483135245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 177267417607831310846993 132950563205873483135245)
              ·
                refine ⟨49856461202202556175717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 132950563205873483135245 49856461202202556175717)
                ·
                  refine ⟨9348086475412979282947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49856461202202556175717 9348086475412979282947)
                  ·
                    rfl

theorem cell20_20481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 3, 4].length) (baseStart_20481 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_20481 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_20481 prefixEnd_20481 := by exact prefixLift 20481
  have htrace : WordTrace (prefixWord ++ tailWord_20481) baseStart_20481 baseEnd_20481 := by
    simpa [prefixWord, tailWord_20481, baseEnd_20481] using wordTrace_append hprefix tailTrace_20481
  have hstable : (prefixWord ++ tailWord_20481).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20481).length < 2 ^ (prefixWord ++ tailWord_20481).sum := by decide
  have hdescent : baseEnd_20481 < baseStart_20481 := by decide
  rcases family_descends (prefixWord ++ tailWord_20481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20529 : List Nat := [1, 2, 2, 3, 1, 5, 1, 2, 3]
def baseStart_20529 : Nat := 118140960795 + 20529 * 2 ^ 59
def prefixEnd_20529 : Nat := 4983230072969 + 3 ^ 40 * 20529 * 2
def baseEnd_20529 : Nat := 9369994983338145682751

theorem tailTrace_20529 : CollatzResearch.WordTrace tailWord_20529 prefixEnd_20529 9369994983338145682751 := by
  unfold tailWord_20529
  simp only [CollatzResearch.WordTrace]
  refine ⟨748754142634413919176641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 499169428422942612784427 748754142634413919176641)
  ·
    refine ⟨561565606975810439382481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 748754142634413919176641 561565606975810439382481)
    ·
      refine ⟨421174205231857829536861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 561565606975810439382481 421174205231857829536861)
      ·
        refine ⟨157940326961946686076323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 421174205231857829536861 157940326961946686076323)
        ·
          refine ⟨236910490442920029114485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157940326961946686076323 236910490442920029114485)
          ·
            refine ⟨22210358479023752729483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 236910490442920029114485 22210358479023752729483)
            ·
              refine ⟨33315537718535629094225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22210358479023752729483 33315537718535629094225)
              ·
                refine ⟨24986653288901721820669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33315537718535629094225 24986653288901721820669)
                ·
                  refine ⟨9369994983338145682751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24986653288901721820669 9369994983338145682751)
                  ·
                    rfl

theorem cell20_20529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 2, 3].length) (baseStart_20529 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_20529 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_20529 prefixEnd_20529 := by exact prefixLift 20529
  have htrace : WordTrace (prefixWord ++ tailWord_20529) baseStart_20529 baseEnd_20529 := by
    simpa [prefixWord, tailWord_20529, baseEnd_20529] using wordTrace_append hprefix tailTrace_20529
  have hstable : (prefixWord ++ tailWord_20529).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20529).length < 2 ^ (prefixWord ++ tailWord_20529).sum := by decide
  have hdescent : baseEnd_20529 < baseStart_20529 := by decide
  rcases family_descends (prefixWord ++ tailWord_20529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20536 : List Nat := [2, 1, 2, 1, 6, 1, 2, 1, 4]
def baseStart_20536 : Nat := 118140960795 + 20536 * 2 ^ 59
def prefixEnd_20536 : Nat := 4983230072969 + 3 ^ 40 * 20536 * 2
def baseEnd_20536 : Nat := 9373189974077232449389

theorem tailTrace_20536 : CollatzResearch.WordTrace tailWord_20536 prefixEnd_20536 9373189974077232449389 := by
  unfold tailWord_20536
  simp only [CollatzResearch.WordTrace]
  refine ⟨374504726804527057340731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 499339635739369409787641 374504726804527057340731)
  ·
    refine ⟨561757090206790586011097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 374504726804527057340731 561757090206790586011097)
    ·
      refine ⟨421317817655092939508323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 561757090206790586011097 421317817655092939508323)
      ·
        refine ⟨631976726482639409262485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 421317817655092939508323 631976726482639409262485)
        ·
          refine ⟨29623909053873722309179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 631976726482639409262485 29623909053873722309179)
          ·
            refine ⟨44435863580810583463769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29623909053873722309179 44435863580810583463769)
            ·
              refine ⟨33326897685607937597827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44435863580810583463769 33326897685607937597827)
              ·
                refine ⟨49990346528411906396741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33326897685607937597827 49990346528411906396741)
                ·
                  refine ⟨9373189974077232449389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49990346528411906396741 9373189974077232449389)
                  ·
                    rfl

theorem cell20_20536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 1, 4].length) (baseStart_20536 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_20536 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_20536 prefixEnd_20536 := by exact prefixLift 20536
  have htrace : WordTrace (prefixWord ++ tailWord_20536) baseStart_20536 baseEnd_20536 := by
    simpa [prefixWord, tailWord_20536, baseEnd_20536] using wordTrace_append hprefix tailTrace_20536
  have hstable : (prefixWord ++ tailWord_20536).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20536).length < 2 ^ (prefixWord ++ tailWord_20536).sum := by decide
  have hdescent : baseEnd_20536 < baseStart_20536 := by decide
  rcases family_descends (prefixWord ++ tailWord_20536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20591 : List Nat := [1, 1, 2, 1, 3, 5, 3, 2, 2]
def baseStart_20591 : Nat := 118140960795 + 20591 * 2 ^ 59
def prefixEnd_20591 : Nat := 4983230072969 + 3 ^ 40 * 20591 * 2
def baseEnd_20591 : Nat := 9398293472741485615831

theorem tailTrace_20591 : CollatzResearch.WordTrace tailWord_20591 prefixEnd_20591 9398293472741485615831 := by
  unfold tailWord_20591
  simp only [CollatzResearch.WordTrace]
  refine ⟨751015468409798507933627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 500676978939865671955751 751015468409798507933627)
  ·
    refine ⟨1126523202614697761900441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 751015468409798507933627 1126523202614697761900441)
    ·
      refine ⟨844892401961023321425331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1126523202614697761900441 844892401961023321425331)
      ·
        refine ⟨1267338602941534982137997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 844892401961023321425331 1267338602941534982137997)
        ·
          refine ⟨475251976103075618301749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1267338602941534982137997 475251976103075618301749)
          ·
            refine ⟨44554872759663339215789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 475251976103075618301749 44554872759663339215789)
            ·
              refine ⟨16708077284873752205921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44554872759663339215789 16708077284873752205921)
              ·
                refine ⟨12531057963655314154441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16708077284873752205921 12531057963655314154441)
                ·
                  refine ⟨9398293472741485615831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12531057963655314154441 9398293472741485615831)
                  ·
                    rfl

theorem cell20_20591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 3, 2, 2].length) (baseStart_20591 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_20591 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_20591 prefixEnd_20591 := by exact prefixLift 20591
  have htrace : WordTrace (prefixWord ++ tailWord_20591) baseStart_20591 baseEnd_20591 := by
    simpa [prefixWord, tailWord_20591, baseEnd_20591] using wordTrace_append hprefix tailTrace_20591
  have hstable : (prefixWord ++ tailWord_20591).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20591).length < 2 ^ (prefixWord ++ tailWord_20591).sum := by decide
  have hdescent : baseEnd_20591 < baseStart_20591 := by decide
  rcases family_descends (prefixWord ++ tailWord_20591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20605 : List Nat := [1, 4, 1, 1, 3, 2, 4, 1, 3]
def baseStart_20605 : Nat := 118140960795 + 20605 * 2 ^ 59
def prefixEnd_20605 : Nat := 4983230072969 + 3 ^ 40 * 20605 * 2
def baseEnd_20605 : Nat := 9404683454219659149107

theorem tailTrace_20605 : CollatzResearch.WordTrace tailWord_20605 prefixEnd_20605 9404683454219659149107 := by
  unfold tailWord_20605
  simp only [CollatzResearch.WordTrace]
  refine ⟨751526090359078898943269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 501017393572719265962179 751526090359078898943269)
  ·
    refine ⟨140911141942327293551863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 751526090359078898943269 140911141942327293551863)
    ·
      refine ⟨211366712913490940327795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140911141942327293551863 211366712913490940327795)
      ·
        refine ⟨317050069370236410491693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211366712913490940327795 317050069370236410491693)
        ·
          refine ⟨118893776013838653934385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 317050069370236410491693 118893776013838653934385)
          ·
            refine ⟨89170332010378990450789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118893776013838653934385 89170332010378990450789)
            ·
              refine ⟨16719437251946060709523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 89170332010378990450789 16719437251946060709523)
              ·
                refine ⟨25079155877919091064285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16719437251946060709523 25079155877919091064285)
                ·
                  refine ⟨9404683454219659149107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25079155877919091064285 9404683454219659149107)
                  ·
                    rfl

theorem cell20_20605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 4, 1, 3].length) (baseStart_20605 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_20605 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_20605 prefixEnd_20605 := by exact prefixLift 20605
  have htrace : WordTrace (prefixWord ++ tailWord_20605) baseStart_20605 baseEnd_20605 := by
    simpa [prefixWord, tailWord_20605, baseEnd_20605] using wordTrace_append hprefix tailTrace_20605
  have hstable : (prefixWord ++ tailWord_20605).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20605).length < 2 ^ (prefixWord ++ tailWord_20605).sum := by decide
  have hdescent : baseEnd_20605 < baseStart_20605 := by decide
  rcases family_descends (prefixWord ++ tailWord_20605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20684 : List Nat := [2, 2, 1, 6, 1, 1, 2, 3, 2]
def baseStart_20684 : Nat := 118140960795 + 20684 * 2 ^ 59
def prefixEnd_20684 : Nat := 4983230072969 + 3 ^ 40 * 20684 * 2
def baseEnd_20684 : Nat := 9440741206846495515451

theorem tailTrace_20684 : CollatzResearch.WordTrace tailWord_20684 prefixEnd_20684 9440741206846495515451 := by
  unfold tailWord_20684
  simp only [CollatzResearch.WordTrace]
  refine ⟨377203728536437695534553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 502938304715250260712737 377203728536437695534553)
  ·
    refine ⟨282902796402328271650915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 377203728536437695534553 282902796402328271650915)
    ·
      refine ⟨424354194603492407476373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282902796402328271650915 424354194603492407476373)
      ·
        refine ⟨19891602872038706600455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 424354194603492407476373 19891602872038706600455)
        ·
          refine ⟨29837404308058059900683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19891602872038706600455 29837404308058059900683)
          ·
            refine ⟨44756106462087089851025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29837404308058059900683 44756106462087089851025)
            ·
              refine ⟨33567079846565317388269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44756106462087089851025 33567079846565317388269)
              ·
                refine ⟨12587654942461994020601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33567079846565317388269 12587654942461994020601)
                ·
                  refine ⟨9440741206846495515451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12587654942461994020601 9440741206846495515451)
                  ·
                    rfl

theorem cell20_20684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 3, 2].length) (baseStart_20684 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_20684 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_20684 prefixEnd_20684 := by exact prefixLift 20684
  have htrace : WordTrace (prefixWord ++ tailWord_20684) baseStart_20684 baseEnd_20684 := by
    simpa [prefixWord, tailWord_20684, baseEnd_20684] using wordTrace_append hprefix tailTrace_20684
  have hstable : (prefixWord ++ tailWord_20684).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20684).length < 2 ^ (prefixWord ++ tailWord_20684).sum := by decide
  have hdescent : baseEnd_20684 < baseStart_20684 := by decide
  rcases family_descends (prefixWord ++ tailWord_20684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20709 : List Nat := [1, 3, 1, 4, 2, 1, 1, 3, 4]
def baseStart_20709 : Nat := 118140960795 + 20709 * 2 ^ 59
def prefixEnd_20709 : Nat := 4983230072969 + 3 ^ 40 * 20709 * 2
def baseEnd_20709 : Nat := 9452151888057519682015

theorem tailTrace_20709 : CollatzResearch.WordTrace tailWord_20709 prefixEnd_20709 9452151888057519682015 := by
  unfold tailWord_20709
  simp only [CollatzResearch.WordTrace]
  refine ⟨755319281982304660729181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 503546187988203107152787 755319281982304660729181)
  ·
    refine ⟨283244730743364247773443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 755319281982304660729181 283244730743364247773443)
    ·
      refine ⟨424867096115046371660165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283244730743364247773443 424867096115046371660165)
      ·
        refine ⟨79662580521571194686281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 424867096115046371660165 79662580521571194686281)
        ·
          refine ⟨59746935391178396014711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79662580521571194686281 59746935391178396014711)
          ·
            refine ⟨89620403086767594022067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59746935391178396014711 89620403086767594022067)
            ·
              refine ⟨134430604630151391033101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89620403086767594022067 134430604630151391033101)
              ·
                refine ⟨50411476736306771637413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 134430604630151391033101 50411476736306771637413)
                ·
                  refine ⟨9452151888057519682015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50411476736306771637413 9452151888057519682015)
                  ·
                    rfl

theorem cell20_20709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 3, 4].length) (baseStart_20709 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_20709 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_20709 prefixEnd_20709 := by exact prefixLift 20709
  have htrace : WordTrace (prefixWord ++ tailWord_20709) baseStart_20709 baseEnd_20709 := by
    simpa [prefixWord, tailWord_20709, baseEnd_20709] using wordTrace_append hprefix tailTrace_20709
  have hstable : (prefixWord ++ tailWord_20709).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20709).length < 2 ^ (prefixWord ++ tailWord_20709).sum := by decide
  have hdescent : baseEnd_20709 < baseStart_20709 := by decide
  rcases family_descends (prefixWord ++ tailWord_20709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20719 : List Nat := [1, 1, 2, 1, 6, 2, 3, 1, 3]
def baseStart_20719 : Nat := 118140960795 + 20719 * 2 ^ 59
def prefixEnd_20719 : Nat := 4983230072969 + 3 ^ 40 * 20719 * 2
def baseEnd_20719 : Nat := 9456716160541929348641

theorem tailTrace_20719 : CollatzResearch.WordTrace tailWord_20719 prefixEnd_20719 9456716160541929348641 := by
  unfold tailWord_20719
  simp only [CollatzResearch.WordTrace]
  refine ⟨755684011946076368593211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 503789341297384245728807 755684011946076368593211)
  ·
    refine ⟨1133526017919114552889817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 755684011946076368593211 1133526017919114552889817)
    ·
      refine ⟨850144513439335914667363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1133526017919114552889817 850144513439335914667363)
      ·
        refine ⟨1275216770159003872001045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 850144513439335914667363 1275216770159003872001045)
        ·
          refine ⟨59775786101203306500049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 1275216770159003872001045 59775786101203306500049)
          ·
            refine ⟨44831839575902479875037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59775786101203306500049 44831839575902479875037)
            ·
              refine ⟨16811939840963429953139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44831839575902479875037 16811939840963429953139)
              ·
                refine ⟨25217909761445144929709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16811939840963429953139 25217909761445144929709)
                ·
                  refine ⟨9456716160541929348641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25217909761445144929709 9456716160541929348641)
                  ·
                    rfl

theorem cell20_20719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 3, 1, 3].length) (baseStart_20719 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_20719 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_20719 prefixEnd_20719 := by exact prefixLift 20719
  have htrace : WordTrace (prefixWord ++ tailWord_20719) baseStart_20719 baseEnd_20719 := by
    simpa [prefixWord, tailWord_20719, baseEnd_20719] using wordTrace_append hprefix tailTrace_20719
  have hstable : (prefixWord ++ tailWord_20719).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20719).length < 2 ^ (prefixWord ++ tailWord_20719).sum := by decide
  have hdescent : baseEnd_20719 < baseStart_20719 := by decide
  rcases family_descends (prefixWord ++ tailWord_20719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20816 : List Nat := [2, 1, 1, 1, 1, 7, 2, 2, 3]
def baseStart_20816 : Nat := 118140960795 + 20816 * 2 ^ 59
def prefixEnd_20816 : Nat := 4983230072969 + 3 ^ 40 * 20816 * 2
def baseEnd_20816 : Nat := 9500989603640703114911

theorem tailTrace_20816 : CollatzResearch.WordTrace tailWord_20816 prefixEnd_20816 9500989603640703114911 := by
  unfold tailWord_20816
  simp only [CollatzResearch.WordTrace]
  refine ⟨379610946297330967437151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 506147928396441289916201 379610946297330967437151)
  ·
    refine ⟨569416419445996451155727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 379610946297330967437151 569416419445996451155727)
    ·
      refine ⟨854124629168994676733591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 569416419445996451155727 854124629168994676733591)
      ·
        refine ⟨1281186943753492015100387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 854124629168994676733591 1281186943753492015100387)
        ·
          refine ⟨1921780415630238022650581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1281186943753492015100387 1921780415630238022650581)
          ·
            refine ⟨45041728491333703655873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 1921780415630238022650581 45041728491333703655873)
            ·
              refine ⟨33781296368500277741905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45041728491333703655873 33781296368500277741905)
              ·
                refine ⟨25335972276375208306429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33781296368500277741905 25335972276375208306429)
                ·
                  refine ⟨9500989603640703114911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25335972276375208306429 9500989603640703114911)
                  ·
                    rfl

theorem cell20_20816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 2, 3].length) (baseStart_20816 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_20816 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_20816 prefixEnd_20816 := by exact prefixLift 20816
  have htrace : WordTrace (prefixWord ++ tailWord_20816) baseStart_20816 baseEnd_20816 := by
    simpa [prefixWord, tailWord_20816, baseEnd_20816] using wordTrace_append hprefix tailTrace_20816
  have hstable : (prefixWord ++ tailWord_20816).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20816).length < 2 ^ (prefixWord ++ tailWord_20816).sum := by decide
  have hdescent : baseEnd_20816 < baseStart_20816 := by decide
  rcases family_descends (prefixWord ++ tailWord_20816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20875 : List Nat := [1, 1, 1, 1, 4, 5, 1, 1, 5]
def baseStart_20875 : Nat := 118140960795 + 20875 * 2 ^ 59
def prefixEnd_20875 : Nat := 4983230072969 + 3 ^ 40 * 20875 * 2
def baseEnd_20875 : Nat := 9527918811298720148003

theorem tailTrace_20875 : CollatzResearch.WordTrace tailWord_20875 prefixEnd_20875 9527918811298720148003 := by
  unfold tailWord_20875
  simp only [CollatzResearch.WordTrace]
  refine ⟨761373799380915011272079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 507582532920610007514719 761373799380915011272079)
  ·
    refine ⟨1142060699071372516908119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 761373799380915011272079 1142060699071372516908119)
    ·
      refine ⟨1713091048607058775362179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1142060699071372516908119 1713091048607058775362179)
      ·
        refine ⟨2569636572910588163043269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1713091048607058775362179 2569636572910588163043269)
        ·
          refine ⟨481806857420735280570613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2569636572910588163043269 481806857420735280570613)
          ·
            refine ⟨45169392883193932553495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 481806857420735280570613 45169392883193932553495)
            ·
              refine ⟨67754089324790898830243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45169392883193932553495 67754089324790898830243)
              ·
                refine ⟨101631133987186348245365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67754089324790898830243 101631133987186348245365)
                ·
                  refine ⟨9527918811298720148003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 101631133987186348245365 9527918811298720148003)
                  ·
                    rfl

theorem cell20_20875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 1, 5].length) (baseStart_20875 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_20875 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_20875 prefixEnd_20875 := by exact prefixLift 20875
  have htrace : WordTrace (prefixWord ++ tailWord_20875) baseStart_20875 baseEnd_20875 := by
    simpa [prefixWord, tailWord_20875, baseEnd_20875] using wordTrace_append hprefix tailTrace_20875
  have hstable : (prefixWord ++ tailWord_20875).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20875).length < 2 ^ (prefixWord ++ tailWord_20875).sum := by decide
  have hdescent : baseEnd_20875 < baseStart_20875 := by decide
  rcases family_descends (prefixWord ++ tailWord_20875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20878 : List Nat := [4, 1, 1, 4, 1, 2, 2, 1, 4]
def baseStart_20878 : Nat := 118140960795 + 20878 * 2 ^ 59
def prefixEnd_20878 : Nat := 4983230072969 + 3 ^ 40 * 20878 * 2
def baseEnd_20878 : Nat := 9529288093044043047991

theorem tailTrace_20878 : CollatzResearch.WordTrace tailWord_20878 prefixEnd_20878 9529288093044043047991 := by
  unfold tailWord_20878
  simp only [CollatzResearch.WordTrace]
  refine ⟨95185402296255815453911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 507655478913364349087525 95185402296255815453911)
  ·
    refine ⟨142778103444383723180867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95185402296255815453911 142778103444383723180867)
    ·
      refine ⟨214167155166575584771301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142778103444383723180867 214167155166575584771301)
      ·
        refine ⟨40156341593732922144619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 214167155166575584771301 40156341593732922144619)
        ·
          refine ⟨60234512390599383216929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40156341593732922144619 60234512390599383216929)
          ·
            refine ⟨45175884292949537412697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60234512390599383216929 45175884292949537412697)
            ·
              refine ⟨33881913219712153059523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45175884292949537412697 33881913219712153059523)
              ·
                refine ⟨50822869829568229589285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33881913219712153059523 50822869829568229589285)
                ·
                  refine ⟨9529288093044043047991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50822869829568229589285 9529288093044043047991)
                  ·
                    rfl

theorem cell20_20878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 1, 4].length) (baseStart_20878 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_20878 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_20878 prefixEnd_20878 := by exact prefixLift 20878
  have htrace : WordTrace (prefixWord ++ tailWord_20878) baseStart_20878 baseEnd_20878 := by
    simpa [prefixWord, tailWord_20878, baseEnd_20878] using wordTrace_append hprefix tailTrace_20878
  have hstable : (prefixWord ++ tailWord_20878).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20878).length < 2 ^ (prefixWord ++ tailWord_20878).sum := by decide
  have hdescent : baseEnd_20878 < baseStart_20878 := by decide
  rcases family_descends (prefixWord ++ tailWord_20878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20889 : List Nat := [1, 2, 1, 2, 1, 4, 2, 7]
def baseStart_20889 : Nat := 118140960795 + 20889 * 2 ^ 59
def prefixEnd_20889 : Nat := 4983230072969 + 3 ^ 40 * 20889 * 2
def baseEnd_20889 : Nat := 3178102930925631227093

theorem tailTrace_20889 : CollatzResearch.WordTrace tailWord_20889 prefixEnd_20889 3178102930925631227093 := by
  unfold tailWord_20889
  simp only [CollatzResearch.WordTrace]
  refine ⟨761884421330195402281721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 507922947553463601521147 761884421330195402281721)
  ·
    refine ⟨571413315997646551711291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 761884421330195402281721 571413315997646551711291)
    ·
      refine ⟨857119973996469827566937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 571413315997646551711291 857119973996469827566937)
      ·
        refine ⟨642839980497352370675203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 857119973996469827566937 642839980497352370675203)
        ·
          refine ⟨964259970746028556012805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 642839980497352370675203 964259970746028556012805)
          ·
            refine ⟨180798744514880354252401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 964259970746028556012805 180798744514880354252401)
            ·
              refine ⟨135599058386160265689301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 180798744514880354252401 135599058386160265689301)
              ·
                refine ⟨3178102930925631227093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 135599058386160265689301 3178102930925631227093)
                ·
                  rfl

theorem cell20_20889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 7].length) (baseStart_20889 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_20889 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_20889 prefixEnd_20889 := by exact prefixLift 20889
  have htrace : WordTrace (prefixWord ++ tailWord_20889) baseStart_20889 baseEnd_20889 := by
    simpa [prefixWord, tailWord_20889, baseEnd_20889] using wordTrace_append hprefix tailTrace_20889
  have hstable : (prefixWord ++ tailWord_20889).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20889).length < 2 ^ (prefixWord ++ tailWord_20889).sum := by decide
  have hdescent : baseEnd_20889 < baseStart_20889 := by decide
  rcases family_descends (prefixWord ++ tailWord_20889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20913 : List Nat := [1, 2, 2, 4, 1, 2, 1, 2, 5]
def baseStart_20913 : Nat := 118140960795 + 20913 * 2 ^ 59
def prefixEnd_20913 : Nat := 4983230072969 + 3 ^ 40 * 20913 * 2
def baseEnd_20913 : Nat := 9545263046739476881181

theorem tailTrace_20913 : CollatzResearch.WordTrace tailWord_20913 prefixEnd_20913 9545263046739476881181 := by
  unfold tailWord_20913
  simp only [CollatzResearch.WordTrace]
  refine ⟨762759773243247501155393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 508506515495498334103595 762759773243247501155393)
  ·
    refine ⟨572069829932435625866545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 762759773243247501155393 572069829932435625866545)
    ·
      refine ⟨429052372449326719399909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 572069829932435625866545 429052372449326719399909)
      ·
        refine ⟨80447319834248759887483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 429052372449326719399909 80447319834248759887483)
        ·
          refine ⟨120670979751373139831225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80447319834248759887483 120670979751373139831225)
          ·
            refine ⟨90503234813529854873419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120670979751373139831225 90503234813529854873419)
            ·
              refine ⟨135754852220294782310129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90503234813529854873419 135754852220294782310129)
              ·
                refine ⟨101816139165221086732597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 135754852220294782310129 101816139165221086732597)
                ·
                  refine ⟨9545263046739476881181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 101816139165221086732597 9545263046739476881181)
                  ·
                    rfl

theorem cell20_20913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 2, 5].length) (baseStart_20913 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_20913 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_20913 prefixEnd_20913 := by exact prefixLift 20913
  have htrace : WordTrace (prefixWord ++ tailWord_20913) baseStart_20913 baseEnd_20913 := by
    simpa [prefixWord, tailWord_20913, baseEnd_20913] using wordTrace_append hprefix tailTrace_20913
  have hstable : (prefixWord ++ tailWord_20913).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20913).length < 2 ^ (prefixWord ++ tailWord_20913).sum := by decide
  have hdescent : baseEnd_20913 < baseStart_20913 := by decide
  rcases family_descends (prefixWord ++ tailWord_20913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20929 : List Nat := [1, 2, 7, 1, 2, 1, 1, 1, 4]
def baseStart_20929 : Nat := 118140960795 + 20929 * 2 ^ 59
def prefixEnd_20929 : Nat := 4983230072969 + 3 ^ 40 * 20929 * 2
def baseEnd_20929 : Nat := 9552565882714532347783

theorem tailTrace_20929 : CollatzResearch.WordTrace tailWord_20929 prefixEnd_20929 9552565882714532347783 := by
  unfold tailWord_20929
  simp only [CollatzResearch.WordTrace]
  refine ⟨763343341185282233737841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 508895560790188155825227 763343341185282233737841)
  ·
    refine ⟨572507505888961675303381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 763343341185282233737841 572507505888961675303381)
    ·
      refine ⟨13418144669272539264923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 572507505888961675303381 13418144669272539264923)
      ·
        refine ⟨20127217003908808897385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13418144669272539264923 20127217003908808897385)
        ·
          refine ⟨15095412752931606673039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20127217003908808897385 15095412752931606673039)
          ·
            refine ⟨22643119129397410009559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15095412752931606673039 22643119129397410009559)
            ·
              refine ⟨33964678694096115014339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22643119129397410009559 33964678694096115014339)
              ·
                refine ⟨50947018041144172521509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33964678694096115014339 50947018041144172521509)
                ·
                  refine ⟨9552565882714532347783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50947018041144172521509 9552565882714532347783)
                  ·
                    rfl

theorem cell20_20929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 1, 4].length) (baseStart_20929 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_20929 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_20929 prefixEnd_20929 := by exact prefixLift 20929
  have htrace : WordTrace (prefixWord ++ tailWord_20929) baseStart_20929 baseEnd_20929 := by
    simpa [prefixWord, tailWord_20929, baseEnd_20929] using wordTrace_append hprefix tailTrace_20929
  have hstable : (prefixWord ++ tailWord_20929).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20929).length < 2 ^ (prefixWord ++ tailWord_20929).sum := by decide
  have hdescent : baseEnd_20929 < baseStart_20929 := by decide
  rcases family_descends (prefixWord ++ tailWord_20929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20937 : List Nat := [1, 2, 1, 1, 2, 1, 4, 6, 2]
def baseStart_20937 : Nat := 118140960795 + 20937 * 2 ^ 59
def prefixEnd_20937 : Nat := 4983230072969 + 3 ^ 40 * 20937 * 2
def baseEnd_20937 : Nat := 9556217300702060081083

theorem tailTrace_20937 : CollatzResearch.WordTrace tailWord_20937 prefixEnd_20937 9556217300702060081083 := by
  unfold tailWord_20937
  simp only [CollatzResearch.WordTrace]
  refine ⟨763635125156299600029065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 509090083437533066686043 763635125156299600029065)
  ·
    refine ⟨572726343867224700021799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 763635125156299600029065 572726343867224700021799)
    ·
      refine ⟨859089515800837050032699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 572726343867224700021799 859089515800837050032699)
      ·
        refine ⟨1288634273701255575049049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 859089515800837050032699 1288634273701255575049049)
        ·
          refine ⟨966475705275941681286787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1288634273701255575049049 966475705275941681286787)
          ·
            refine ⟨1449713557913912521930181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 966475705275941681286787 1449713557913912521930181)
            ·
              refine ⟨271821292108858597861909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1449713557913912521930181 271821292108858597861909)
              ·
                refine ⟨12741623067602746774777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 271821292108858597861909 12741623067602746774777)
                ·
                  refine ⟨9556217300702060081083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12741623067602746774777 9556217300702060081083)
                  ·
                    rfl

theorem cell20_20937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 6, 2].length) (baseStart_20937 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_20937 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_20937 prefixEnd_20937 := by exact prefixLift 20937
  have htrace : WordTrace (prefixWord ++ tailWord_20937) baseStart_20937 baseEnd_20937 := by
    simpa [prefixWord, tailWord_20937, baseEnd_20937] using wordTrace_append hprefix tailTrace_20937
  have hstable : (prefixWord ++ tailWord_20937).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20937).length < 2 ^ (prefixWord ++ tailWord_20937).sum := by decide
  have hdescent : baseEnd_20937 < baseStart_20937 := by decide
  rcases family_descends (prefixWord ++ tailWord_20937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20975 : List Nat := [1, 1, 2, 1, 4, 1, 1, 7, 2]
def baseStart_20975 : Nat := 118140960795 + 20975 * 2 ^ 59
def prefixEnd_20975 : Nat := 4983230072969 + 3 ^ 40 * 20975 * 2
def baseEnd_20975 : Nat := 9573561536142816814261

theorem tailTrace_20975 : CollatzResearch.WordTrace tailWord_20975 prefixEnd_20975 9573561536142816814261 := by
  unfold tailWord_20975
  simp only [CollatzResearch.WordTrace]
  refine ⟨765021099018632089912379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 510014066012421393274919 765021099018632089912379)
  ·
    refine ⟨1147531648527948134868569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 765021099018632089912379 1147531648527948134868569)
    ·
      refine ⟨860648736395961101151427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1147531648527948134868569 860648736395961101151427)
      ·
        refine ⟨1290973104593941651727141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 860648736395961101151427 1290973104593941651727141)
        ·
          refine ⟨242057457111364059698839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1290973104593941651727141 242057457111364059698839)
          ·
            refine ⟨363086185667046089548259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 242057457111364059698839 363086185667046089548259)
            ·
              refine ⟨544629278500569134322389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 363086185667046089548259 544629278500569134322389)
              ·
                refine ⟨12764748714857089085681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 544629278500569134322389 12764748714857089085681)
                ·
                  refine ⟨9573561536142816814261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12764748714857089085681 9573561536142816814261)
                  ·
                    rfl

theorem cell20_20975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 7, 2].length) (baseStart_20975 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_20975 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_20975 prefixEnd_20975 := by exact prefixLift 20975
  have htrace : WordTrace (prefixWord ++ tailWord_20975) baseStart_20975 baseEnd_20975 := by
    simpa [prefixWord, tailWord_20975, baseEnd_20975] using wordTrace_append hprefix tailTrace_20975
  have hstable : (prefixWord ++ tailWord_20975).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20975).length < 2 ^ (prefixWord ++ tailWord_20975).sum := by decide
  have hdescent : baseEnd_20975 < baseStart_20975 := by decide
  rcases family_descends (prefixWord ++ tailWord_20975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20999 : List Nat := [1, 1, 4, 3, 3, 2, 1, 5]
def baseStart_20999 : Nat := 118140960795 + 20999 * 2 ^ 59
def prefixEnd_20999 : Nat := 4983230072969 + 3 ^ 40 * 20999 * 2
def baseEnd_20999 : Nat := 3194838596701800004721

theorem tailTrace_20999 : CollatzResearch.WordTrace tailWord_20999 prefixEnd_20999 3194838596701800004721 := by
  unfold tailWord_20999
  simp only [CollatzResearch.WordTrace]
  refine ⟨765896450931684188786051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 510597633954456125857367 765896450931684188786051)
  ·
    refine ⟨1148844676397526283179077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 765896450931684188786051 1148844676397526283179077)
    ·
      refine ⟨215408376824536178096077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1148844676397526283179077 215408376824536178096077)
      ·
        refine ⟨80778141309201066786029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 215408376824536178096077 80778141309201066786029)
        ·
          refine ⟨30291802990950400044761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80778141309201066786029 30291802990950400044761)
          ·
            refine ⟨22718852243212800033571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30291802990950400044761 22718852243212800033571)
            ·
              refine ⟨34078278364819200050357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22718852243212800033571 34078278364819200050357)
              ·
                refine ⟨3194838596701800004721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34078278364819200050357 3194838596701800004721)
                ·
                  rfl

theorem cell20_20999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 5].length) (baseStart_20999 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_20999 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_20999 prefixEnd_20999 := by exact prefixLift 20999
  have htrace : WordTrace (prefixWord ++ tailWord_20999) baseStart_20999 baseEnd_20999 := by
    simpa [prefixWord, tailWord_20999, baseEnd_20999] using wordTrace_append hprefix tailTrace_20999
  have hstable : (prefixWord ++ tailWord_20999).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20999).length < 2 ^ (prefixWord ++ tailWord_20999).sum := by decide
  have hdescent : baseEnd_20999 < baseStart_20999 := by decide
  rcases family_descends (prefixWord ++ tailWord_20999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21006 : List Nat := [4, 1, 1, 2, 3, 1, 2, 3, 3]
def baseStart_21006 : Nat := 118140960795 + 21006 * 2 ^ 59
def prefixEnd_21006 : Nat := 4983230072969 + 3 ^ 40 * 21006 * 2
def baseEnd_21006 : Nat := 9587710780844486780801

theorem tailTrace_21006 : CollatzResearch.WordTrace tailWord_21006 prefixEnd_21006 9587710780844486780801 := by
  unfold tailWord_21006
  simp only [CollatzResearch.WordTrace]
  refine ⟨95768970238290548036359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 510767841270882922860581 95768970238290548036359)
  ·
    refine ⟨143653455357435822054539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95768970238290548036359 143653455357435822054539)
    ·
      refine ⟨215480183036153733081809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143653455357435822054539 215480183036153733081809)
      ·
        refine ⟨161610137277115299811357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 215480183036153733081809 161610137277115299811357)
        ·
          refine ⟨60603801478918237429259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 161610137277115299811357 60603801478918237429259)
          ·
            refine ⟨90905702218377356143889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60603801478918237429259 90905702218377356143889)
            ·
              refine ⟨68179276663783017107917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90905702218377356143889 68179276663783017107917)
              ·
                refine ⟨25567228748918631415469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68179276663783017107917 25567228748918631415469)
                ·
                  refine ⟨9587710780844486780801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25567228748918631415469 9587710780844486780801)
                  ·
                    rfl

theorem cell20_21006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 3, 3].length) (baseStart_21006 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_21006 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_21006 prefixEnd_21006 := by exact prefixLift 21006
  have htrace : WordTrace (prefixWord ++ tailWord_21006) baseStart_21006 baseEnd_21006 := by
    simpa [prefixWord, tailWord_21006, baseEnd_21006] using wordTrace_append hprefix tailTrace_21006
  have hstable : (prefixWord ++ tailWord_21006).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21006).length < 2 ^ (prefixWord ++ tailWord_21006).sum := by decide
  have hdescent : baseEnd_21006 < baseStart_21006 := by decide
  rcases family_descends (prefixWord ++ tailWord_21006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21079 : List Nat := [1, 1, 3, 2, 2, 2, 3, 6]
def baseStart_21079 : Nat := 118140960795 + 21079 * 2 ^ 59
def prefixEnd_21079 : Nat := 4983230072969 + 3 ^ 40 * 21079 * 2
def baseEnd_21079 : Nat := 3207009989993559115723

theorem tailTrace_21079 : CollatzResearch.WordTrace tailWord_21079 prefixEnd_21079 3207009989993559115723 := by
  unfold tailWord_21079
  simp only [CollatzResearch.WordTrace]
  refine ⟨768814290641857851698291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 512542860427905234465527 768814290641857851698291)
  ·
    refine ⟨1153221435962786777547437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 768814290641857851698291 1153221435962786777547437)
    ·
      refine ⟨432458038486045041580289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1153221435962786777547437 432458038486045041580289)
      ·
        refine ⟨324343528864533781185217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 432458038486045041580289 324343528864533781185217)
        ·
          refine ⟨243257646648400335888913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 324343528864533781185217 243257646648400335888913)
          ·
            refine ⟨182443234986300251916685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 243257646648400335888913 182443234986300251916685)
            ·
              refine ⟨68416213119862594468757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 182443234986300251916685 68416213119862594468757)
              ·
                refine ⟨3207009989993559115723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 68416213119862594468757 3207009989993559115723)
                ·
                  rfl

theorem cell20_21079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 6].length) (baseStart_21079 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_21079 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_21079 prefixEnd_21079 := by exact prefixLift 21079
  have htrace : WordTrace (prefixWord ++ tailWord_21079) baseStart_21079 baseEnd_21079 := by
    simpa [prefixWord, tailWord_21079, baseEnd_21079] using wordTrace_append hprefix tailTrace_21079
  have hstable : (prefixWord ++ tailWord_21079).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21079).length < 2 ^ (prefixWord ++ tailWord_21079).sum := by decide
  have hdescent : baseEnd_21079 < baseStart_21079 := by decide
  rcases family_descends (prefixWord ++ tailWord_21079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21106 : List Nat := [3, 2, 1, 2, 4, 2, 1, 1, 4]
def baseStart_21106 : Nat := 118140960795 + 21106 * 2 ^ 59
def prefixEnd_21106 : Nat := 4983230072969 + 3 ^ 40 * 21106 * 2
def baseEnd_21106 : Nat := 9633353505688583447059

theorem tailTrace_21106 : CollatzResearch.WordTrace tailWord_21106 prefixEnd_21106 9633353505688583447059 := by
  unfold tailWord_21106
  simp only [CollatzResearch.WordTrace]
  refine ⟨192449765386010365732793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 513199374362694308620781 192449765386010365732793)
  ·
    refine ⟨144337324039507774299595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192449765386010365732793 144337324039507774299595)
    ·
      refine ⟨216505986059261661449393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144337324039507774299595 216505986059261661449393)
      ·
        refine ⟨162379489544446246087045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 216505986059261661449393 162379489544446246087045)
        ·
          refine ⟨30446154289583671141321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 162379489544446246087045 30446154289583671141321)
          ·
            refine ⟨22834615717187753355991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30446154289583671141321 22834615717187753355991)
            ·
              refine ⟨34251923575781630033987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22834615717187753355991 34251923575781630033987)
              ·
                refine ⟨51377885363672445050981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34251923575781630033987 51377885363672445050981)
                ·
                  refine ⟨9633353505688583447059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51377885363672445050981 9633353505688583447059)
                  ·
                    rfl

theorem cell20_21106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 1, 4].length) (baseStart_21106 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_21106 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_21106 prefixEnd_21106 := by exact prefixLift 21106
  have htrace : WordTrace (prefixWord ++ tailWord_21106) baseStart_21106 baseEnd_21106 := by
    simpa [prefixWord, tailWord_21106, baseEnd_21106] using wordTrace_append hprefix tailTrace_21106
  have hstable : (prefixWord ++ tailWord_21106).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21106).length < 2 ^ (prefixWord ++ tailWord_21106).sum := by decide
  have hdescent : baseEnd_21106 < baseStart_21106 := by decide
  rcases family_descends (prefixWord ++ tailWord_21106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21120 : List Nat := [2, 1, 1, 2, 1, 5, 4, 1, 3]
def baseStart_21120 : Nat := 118140960795 + 21120 * 2 ^ 59
def prefixEnd_21120 : Nat := 4983230072969 + 3 ^ 40 * 21120 * 2
def baseEnd_21120 : Nat := 9639743487166756980335

theorem tailTrace_21120 : CollatzResearch.WordTrace tailWord_21120 prefixEnd_21120 9639743487166756980335 := by
  unfold tailWord_21120
  simp only [CollatzResearch.WordTrace]
  refine ⟨385154841746660926970407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 513539788995547902627209 385154841746660926970407)
  ·
    refine ⟨577732262619991390455611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 385154841746660926970407 577732262619991390455611)
    ·
      refine ⟨866598393929987085683417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 577732262619991390455611 866598393929987085683417)
      ·
        refine ⟨649948795447490314262563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 866598393929987085683417 649948795447490314262563)
        ·
          refine ⟨974923193171235471393845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 649948795447490314262563 974923193171235471393845)
          ·
            refine ⟨91399049359803325443173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 974923193171235471393845 91399049359803325443173)
            ·
              refine ⟨17137321754963123520595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91399049359803325443173 17137321754963123520595)
              ·
                refine ⟨25705982632444685280893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17137321754963123520595 25705982632444685280893)
                ·
                  refine ⟨9639743487166756980335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25705982632444685280893 9639743487166756980335)
                  ·
                    rfl

theorem cell20_21120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 4, 1, 3].length) (baseStart_21120 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_21120 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_21120 prefixEnd_21120 := by exact prefixLift 21120
  have htrace : WordTrace (prefixWord ++ tailWord_21120) baseStart_21120 baseEnd_21120 := by
    simpa [prefixWord, tailWord_21120, baseEnd_21120] using wordTrace_append hprefix tailTrace_21120
  have hstable : (prefixWord ++ tailWord_21120).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21120).length < 2 ^ (prefixWord ++ tailWord_21120).sum := by decide
  have hdescent : baseEnd_21120 < baseStart_21120 := by decide
  rcases family_descends (prefixWord ++ tailWord_21120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21217 : List Nat := [1, 2, 3, 1, 4, 2, 1, 1, 5]
def baseStart_21217 : Nat := 118140960795 + 21217 * 2 ^ 59
def prefixEnd_21217 : Nat := 4983230072969 + 3 ^ 40 * 21217 * 2
def baseEnd_21217 : Nat := 9684016930265530746605

theorem tailTrace_21217 : CollatzResearch.WordTrace tailWord_21217 prefixEnd_21217 9684016930265530746605 := by
  unfold tailWord_21217
  simp only [CollatzResearch.WordTrace]
  refine ⟨773847564141907420221905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 515898376094604946814603 773847564141907420221905)
  ·
    refine ⟨580385673106430565166429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 773847564141907420221905 580385673106430565166429)
    ·
      refine ⟨217644627414911461937411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 580385673106430565166429 217644627414911461937411)
      ·
        refine ⟨326466941122367192906117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217644627414911461937411 326466941122367192906117)
        ·
          refine ⟨61212551460443848669897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 326466941122367192906117 61212551460443848669897)
          ·
            refine ⟨45909413595332886502423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61212551460443848669897 45909413595332886502423)
            ·
              refine ⟨68864120392999329753635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45909413595332886502423 68864120392999329753635)
              ·
                refine ⟨103296180589498994630453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68864120392999329753635 103296180589498994630453)
                ·
                  refine ⟨9684016930265530746605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 103296180589498994630453 9684016930265530746605)
                  ·
                    rfl

theorem cell20_21217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 1, 5].length) (baseStart_21217 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_21217 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_21217 prefixEnd_21217 := by exact prefixLift 21217
  have htrace : WordTrace (prefixWord ++ tailWord_21217) baseStart_21217 baseEnd_21217 := by
    simpa [prefixWord, tailWord_21217, baseEnd_21217] using wordTrace_append hprefix tailTrace_21217
  have hstable : (prefixWord ++ tailWord_21217).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21217).length < 2 ^ (prefixWord ++ tailWord_21217).sum := by decide
  have hdescent : baseEnd_21217 < baseStart_21217 := by decide
  rcases family_descends (prefixWord ++ tailWord_21217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21255 : List Nat := [1, 1, 4, 4, 1, 1, 1, 2, 5]
def baseStart_21255 : Nat := 118140960795 + 21255 * 2 ^ 59
def prefixEnd_21255 : Nat := 4983230072969 + 3 ^ 40 * 21255 * 2
def baseEnd_21255 : Nat := 9701361165706287479783

theorem tailTrace_21255 : CollatzResearch.WordTrace tailWord_21255 prefixEnd_21255 9701361165706287479783 := by
  unfold tailWord_21255
  simp only [CollatzResearch.WordTrace]
  refine ⟨775233538004239910105219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 516822358669493273403479 775233538004239910105219)
  ·
    refine ⟨1162850307006359865157829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 775233538004239910105219 1162850307006359865157829)
    ·
      refine ⟨218034432563692474717093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1162850307006359865157829 218034432563692474717093)
      ·
        refine ⟨40881456105692339009455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 218034432563692474717093 40881456105692339009455)
        ·
          refine ⟨61322184158538508514183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40881456105692339009455 61322184158538508514183)
          ·
            refine ⟨91983276237807762771275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61322184158538508514183 91983276237807762771275)
            ·
              refine ⟨137974914356711644156913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91983276237807762771275 137974914356711644156913)
              ·
                refine ⟨103481185767533733117685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 137974914356711644156913 103481185767533733117685)
                ·
                  refine ⟨9701361165706287479783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 103481185767533733117685 9701361165706287479783)
                  ·
                    rfl

theorem cell20_21255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 2, 5].length) (baseStart_21255 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_21255 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_21255 prefixEnd_21255 := by exact prefixLift 21255
  have htrace : WordTrace (prefixWord ++ tailWord_21255) baseStart_21255 baseEnd_21255 := by
    simpa [prefixWord, tailWord_21255, baseEnd_21255] using wordTrace_append hprefix tailTrace_21255
  have hstable : (prefixWord ++ tailWord_21255).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21255).length < 2 ^ (prefixWord ++ tailWord_21255).sum := by decide
  have hdescent : baseEnd_21255 < baseStart_21255 := by decide
  rcases family_descends (prefixWord ++ tailWord_21255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21279 : List Nat := [1, 1, 2, 4, 2, 4, 1, 1, 4]
def baseStart_21279 : Nat := 118140960795 + 21279 * 2 ^ 59
def prefixEnd_21279 : Nat := 4983230072969 + 3 ^ 40 * 21279 * 2
def baseEnd_21279 : Nat := 9712315419668870679685

theorem tailTrace_21279 : CollatzResearch.WordTrace tailWord_21279 prefixEnd_21279 9712315419668870679685 := by
  unfold tailWord_21279
  simp only [CollatzResearch.WordTrace]
  refine ⟨776108889917292008978891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 517405926611528005985927 776108889917292008978891)
  ·
    refine ⟨1164163334875938013468337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 776108889917292008978891 1164163334875938013468337)
    ·
      refine ⟨873122501156953510101253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1164163334875938013468337 873122501156953510101253)
      ·
        refine ⟨163710468966928783143985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 873122501156953510101253 163710468966928783143985)
        ·
          refine ⟨122782851725196587357989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163710468966928783143985 122782851725196587357989)
          ·
            refine ⟨23021784698474360129623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 122782851725196587357989 23021784698474360129623)
            ·
              refine ⟨34532677047711540194435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23021784698474360129623 34532677047711540194435)
              ·
                refine ⟨51799015571567310291653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34532677047711540194435 51799015571567310291653)
                ·
                  refine ⟨9712315419668870679685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51799015571567310291653 9712315419668870679685)
                  ·
                    rfl

theorem cell20_21279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 1, 4].length) (baseStart_21279 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_21279 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_21279 prefixEnd_21279 := by exact prefixLift 21279
  have htrace : WordTrace (prefixWord ++ tailWord_21279) baseStart_21279 baseEnd_21279 := by
    simpa [prefixWord, tailWord_21279, baseEnd_21279] using wordTrace_append hprefix tailTrace_21279
  have hstable : (prefixWord ++ tailWord_21279).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21279).length < 2 ^ (prefixWord ++ tailWord_21279).sum := by decide
  have hdescent : baseEnd_21279 < baseStart_21279 := by decide
  rcases family_descends (prefixWord ++ tailWord_21279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21383 : List Nat := [1, 1, 4, 2, 3, 2, 7]
def baseStart_21383 : Nat := 118140960795 + 21383 * 2 ^ 59
def prefixEnd_21383 : Nat := 4983230072969 + 3 ^ 40 * 21383 * 2
def baseEnd_21383 : Nat := 1084420428167414579177

theorem tailTrace_21383 : CollatzResearch.WordTrace tailWord_21383 prefixEnd_21383 1084420428167414579177 := by
  unfold tailWord_21383
  simp only [CollatzResearch.WordTrace]
  refine ⟨779902081540517770764803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 519934721027011847176535 779902081540517770764803)
  ·
    refine ⟨1169853122310776656147205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 779902081540517770764803 1169853122310776656147205)
    ·
      refine ⟨219347460433270623027601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1169853122310776656147205 219347460433270623027601)
      ·
        refine ⟨164510595324952967270701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 219347460433270623027601 164510595324952967270701)
        ·
          refine ⟨61691473246857362726513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 164510595324952967270701 61691473246857362726513)
          ·
            refine ⟨46268604935143022044885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61691473246857362726513 46268604935143022044885)
            ·
              refine ⟨1084420428167414579177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 46268604935143022044885 1084420428167414579177)
              ·
                rfl

theorem cell20_21383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 7].length) (baseStart_21383 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_21383 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_21383 prefixEnd_21383 := by exact prefixLift 21383
  have htrace : WordTrace (prefixWord ++ tailWord_21383) baseStart_21383 baseEnd_21383 := by
    simpa [prefixWord, tailWord_21383, baseEnd_21383] using wordTrace_append hprefix tailTrace_21383
  have hstable : (prefixWord ++ tailWord_21383).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21383).length < 2 ^ (prefixWord ++ tailWord_21383).sum := by decide
  have hdescent : baseEnd_21383 < baseStart_21383 := by decide
  rcases family_descends (prefixWord ++ tailWord_21383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21386 : List Nat := [3, 1, 2, 4, 1, 1, 3, 2, 3]
def baseStart_21386 : Nat := 118140960795 + 21386 * 2 ^ 59
def prefixEnd_21386 : Nat := 4983230072969 + 3 ^ 40 * 21386 * 2
def baseEnd_21386 : Nat := 9761153135252054112581

theorem tailTrace_21386 : CollatzResearch.WordTrace tailWord_21386 prefixEnd_21386 9761153135252054112581 := by
  unfold tailWord_21386
  simp only [CollatzResearch.WordTrace]
  refine ⟨195002875132412320781003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 520007667019766188749341 195002875132412320781003)
  ·
    refine ⟨292504312698618481171505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195002875132412320781003 292504312698618481171505)
    ·
      refine ⟨219378234523963860878629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 292504312698618481171505 219378234523963860878629)
      ·
        refine ⟨41133418973243223914743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 219378234523963860878629 41133418973243223914743)
        ·
          refine ⟨61700128459864835872115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41133418973243223914743 61700128459864835872115)
          ·
            refine ⟨92550192689797253808173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61700128459864835872115 92550192689797253808173)
            ·
              refine ⟨34706322258673970178065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92550192689797253808173 34706322258673970178065)
              ·
                refine ⟨26029741694005477633549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34706322258673970178065 26029741694005477633549)
                ·
                  refine ⟨9761153135252054112581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26029741694005477633549 9761153135252054112581)
                  ·
                    rfl

theorem cell20_21386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 2, 3].length) (baseStart_21386 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_21386 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_21386 prefixEnd_21386 := by exact prefixLift 21386
  have htrace : WordTrace (prefixWord ++ tailWord_21386) baseStart_21386 baseEnd_21386 := by
    simpa [prefixWord, tailWord_21386, baseEnd_21386] using wordTrace_append hprefix tailTrace_21386
  have hstable : (prefixWord ++ tailWord_21386).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21386).length < 2 ^ (prefixWord ++ tailWord_21386).sum := by decide
  have hdescent : baseEnd_21386 < baseStart_21386 := by decide
  rcases family_descends (prefixWord ++ tailWord_21386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21431 : List Nat := [1, 1, 3, 1, 3, 1, 5, 3, 2]
def baseStart_21431 : Nat := 118140960795 + 21431 * 2 ^ 59
def prefixEnd_21431 : Nat := 4983230072969 + 3 ^ 40 * 21431 * 2
def baseEnd_21431 : Nat := 9781692361431897612397

theorem tailTrace_21431 : CollatzResearch.WordTrace tailWord_21431 prefixEnd_21431 9781692361431897612397 := by
  unfold tailWord_21431
  simp only [CollatzResearch.WordTrace]
  refine ⟨781652785366621968512147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 521101856911081312341431 781652785366621968512147)
  ·
    refine ⟨1172479178049932952768221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 781652785366621968512147 1172479178049932952768221)
    ·
      refine ⟨439679691768724857288083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1172479178049932952768221 439679691768724857288083)
      ·
        refine ⟨659519537653087285932125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 439679691768724857288083 659519537653087285932125)
        ·
          refine ⟨247319826619907732224547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 659519537653087285932125 247319826619907732224547)
          ·
            refine ⟨370979739929861598336821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 247319826619907732224547 370979739929861598336821)
            ·
              refine ⟨34779350618424524844077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 370979739929861598336821 34779350618424524844077)
              ·
                refine ⟨13042256481909196816529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34779350618424524844077 13042256481909196816529)
                ·
                  refine ⟨9781692361431897612397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13042256481909196816529 9781692361431897612397)
                  ·
                    rfl

theorem cell20_21431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 3, 2].length) (baseStart_21431 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_21431 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_21431 prefixEnd_21431 := by exact prefixLift 21431
  have htrace : WordTrace (prefixWord ++ tailWord_21431) baseStart_21431 baseEnd_21431 := by
    simpa [prefixWord, tailWord_21431, baseEnd_21431] using wordTrace_append hprefix tailTrace_21431
  have hstable : (prefixWord ++ tailWord_21431).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21431).length < 2 ^ (prefixWord ++ tailWord_21431).sum := by decide
  have hdescent : baseEnd_21431 < baseStart_21431 := by decide
  rcases family_descends (prefixWord ++ tailWord_21431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21444 : List Nat := [2, 3, 3, 3, 1, 1, 3, 2, 2]
def baseStart_21444 : Nat := 118140960795 + 21444 * 2 ^ 59
def prefixEnd_21444 : Nat := 4983230072969 + 3 ^ 40 * 21444 * 2
def baseEnd_21444 : Nat := 9787625915661630179011

theorem tailTrace_21444 : CollatzResearch.WordTrace tailWord_21444 prefixEnd_21444 9787625915661630179011 := by
  unfold tailWord_21444
  simp only [CollatzResearch.WordTrace]
  refine ⟨391063467159762594367693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 521417956213016792490257 391063467159762594367693)
  ·
    refine ⟨146648800184910972887885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 391063467159762594367693 146648800184910972887885)
    ·
      refine ⟨54993300069341614832957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146648800184910972887885 54993300069341614832957)
      ·
        refine ⟨20622487526003105562359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54993300069341614832957 20622487526003105562359)
        ·
          refine ⟨30933731289004658343539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20622487526003105562359 30933731289004658343539)
          ·
            refine ⟨46400596933506987515309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30933731289004658343539 46400596933506987515309)
            ·
              refine ⟨17400223850065120318241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46400596933506987515309 17400223850065120318241)
              ·
                refine ⟨13050167887548840238681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17400223850065120318241 13050167887548840238681)
                ·
                  refine ⟨9787625915661630179011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13050167887548840238681 9787625915661630179011)
                  ·
                    rfl

theorem cell20_21444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 3, 2, 2].length) (baseStart_21444 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_21444 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_21444 prefixEnd_21444 := by exact prefixLift 21444
  have htrace : WordTrace (prefixWord ++ tailWord_21444) baseStart_21444 baseEnd_21444 := by
    simpa [prefixWord, tailWord_21444, baseEnd_21444] using wordTrace_append hprefix tailTrace_21444
  have hstable : (prefixWord ++ tailWord_21444).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21444).length < 2 ^ (prefixWord ++ tailWord_21444).sum := by decide
  have hdescent : baseEnd_21444 < baseStart_21444 := by decide
  rcases family_descends (prefixWord ++ tailWord_21444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21448 : List Nat := [2, 1, 3, 1, 6, 1, 1, 1, 4]
def baseStart_21448 : Nat := 118140960795 + 21448 * 2 ^ 59
def prefixEnd_21448 : Nat := 4983230072969 + 3 ^ 40 * 21448 * 2
def baseEnd_21448 : Nat := 9789451624655394045661

theorem tailTrace_21448 : CollatzResearch.WordTrace tailWord_21448 prefixEnd_21448 9789451624655394045661 := by
  unfold tailWord_21448
  simp only [CollatzResearch.WordTrace]
  refine ⟨391136413152516935940499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 521515217536689247920665 391136413152516935940499)
  ·
    refine ⟨586704619728775403910749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 391136413152516935940499 586704619728775403910749)
    ·
      refine ⟨220014232398290776466531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 586704619728775403910749 220014232398290776466531)
      ·
        refine ⟨330021348597436164699797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220014232398290776466531 330021348597436164699797)
        ·
          refine ⟨15469750715504820220303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 330021348597436164699797 15469750715504820220303)
          ·
            refine ⟨23204626073257230330455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15469750715504820220303 23204626073257230330455)
            ·
              refine ⟨34806939109885845495683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23204626073257230330455 34806939109885845495683)
              ·
                refine ⟨52210408664828768243525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34806939109885845495683 52210408664828768243525)
                ·
                  refine ⟨9789451624655394045661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52210408664828768243525 9789451624655394045661)
                  ·
                    rfl

theorem cell20_21448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 1, 4].length) (baseStart_21448 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_21448 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_21448 prefixEnd_21448 := by exact prefixLift 21448
  have htrace : WordTrace (prefixWord ++ tailWord_21448) baseStart_21448 baseEnd_21448 := by
    simpa [prefixWord, tailWord_21448, baseEnd_21448] using wordTrace_append hprefix tailTrace_21448
  have hstable : (prefixWord ++ tailWord_21448).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21448).length < 2 ^ (prefixWord ++ tailWord_21448).sum := by decide
  have hdescent : baseEnd_21448 < baseStart_21448 := by decide
  rcases family_descends (prefixWord ++ tailWord_21448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21473 : List Nat := [1, 2, 3, 1, 2, 1, 1, 3, 6]
def baseStart_21473 : Nat := 118140960795 + 21473 * 2 ^ 59
def prefixEnd_21473 : Nat := 4983230072969 + 3 ^ 40 * 21473 * 2
def baseEnd_21473 : Nat := 9800862305866418212225

theorem tailTrace_21473 : CollatzResearch.WordTrace tailWord_21473 prefixEnd_21473 9800862305866418212225 := by
  unfold tailWord_21473
  simp only [CollatzResearch.WordTrace]
  refine ⟨783184651214463141541073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 522123100809642094360715 783184651214463141541073)
  ·
    refine ⟨587388488410847356155805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 783184651214463141541073 587388488410847356155805)
    ·
      refine ⟨220270683154067758558427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 587388488410847356155805 220270683154067758558427)
      ·
        refine ⟨330406024731101637837641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220270683154067758558427 330406024731101637837641)
        ·
          refine ⟨247804518548326228378231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 330406024731101637837641 247804518548326228378231)
          ·
            refine ⟨371706777822489342567347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 247804518548326228378231 371706777822489342567347)
            ·
              refine ⟨557560166733734013851021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 371706777822489342567347 557560166733734013851021)
              ·
                refine ⟨209085062525150255194133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 557560166733734013851021 209085062525150255194133)
                ·
                  refine ⟨9800862305866418212225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 209085062525150255194133 9800862305866418212225)
                  ·
                    rfl

theorem cell20_21473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 6].length) (baseStart_21473 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_21473 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_21473 prefixEnd_21473 := by exact prefixLift 21473
  have htrace : WordTrace (prefixWord ++ tailWord_21473) baseStart_21473 baseEnd_21473 := by
    simpa [prefixWord, tailWord_21473, baseEnd_21473] using wordTrace_append hprefix tailTrace_21473
  have hstable : (prefixWord ++ tailWord_21473).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21473).length < 2 ^ (prefixWord ++ tailWord_21473).sum := by decide
  have hdescent : baseEnd_21473 < baseStart_21473 := by decide
  rcases family_descends (prefixWord ++ tailWord_21473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21493 : List Nat := [1, 3, 5, 2, 2, 7]
def baseStart_21493 : Nat := 118140960795 + 21493 * 2 ^ 59
def prefixEnd_21493 : Nat := 4983230072969 + 3 ^ 40 * 21493 * 2
def baseEnd_21493 : Nat := 363332994475379168351

theorem tailTrace_21493 : CollatzResearch.WordTrace tailWord_21493 prefixEnd_21493 363332994475379168351 := by
  unfold tailWord_21493
  simp only [CollatzResearch.WordTrace]
  refine ⟨783914111142006557269133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 522609407428004371512755 783914111142006557269133)
  ·
    refine ⟨293967791678252458975925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 783914111142006557269133 293967791678252458975925)
    ·
      refine ⟨27559480469836168028993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 293967791678252458975925 27559480469836168028993)
      ·
        refine ⟨20669610352377126021745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27559480469836168028993 20669610352377126021745)
        ·
          refine ⟨15502207764282844516309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20669610352377126021745 15502207764282844516309)
          ·
            refine ⟨363332994475379168351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 15502207764282844516309 363332994475379168351)
            ·
              rfl

theorem cell20_21493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 7].length) (baseStart_21493 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_21493 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_21493 prefixEnd_21493 := by exact prefixLift 21493
  have htrace : WordTrace (prefixWord ++ tailWord_21493) baseStart_21493 baseEnd_21493 := by
    simpa [prefixWord, tailWord_21493, baseEnd_21493] using wordTrace_append hprefix tailTrace_21493
  have hstable : (prefixWord ++ tailWord_21493).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21493).length < 2 ^ (prefixWord ++ tailWord_21493).sum := by decide
  have hdescent : baseEnd_21493 < baseStart_21493 := by decide
  rcases family_descends (prefixWord ++ tailWord_21493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21514 : List Nat := [3, 1, 2, 2, 3, 3, 1, 5]
def baseStart_21514 : Nat := 118140960795 + 21514 * 2 ^ 59
def prefixEnd_21514 : Nat := 4983230072969 + 3 ^ 40 * 21514 * 2
def baseEnd_21514 : Nat := 3273191941017499281797

theorem tailTrace_21514 : CollatzResearch.WordTrace tailWord_21514 prefixEnd_21514 3273191941017499281797 := by
  unfold tailWord_21514
  simp only [CollatzResearch.WordTrace]
  refine ⟨196170011016481785945899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 523120029377284762522397 196170011016481785945899)
  ·
    refine ⟨294255016524722678918849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196170011016481785945899 294255016524722678918849)
    ·
      refine ⟨220691262393542009189137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 294255016524722678918849 220691262393542009189137)
      ·
        refine ⟨165518446795156506891853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 220691262393542009189137 165518446795156506891853)
        ·
          refine ⟨62069417548183690084445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 165518446795156506891853 62069417548183690084445)
          ·
            refine ⟨23276031580568883781667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62069417548183690084445 23276031580568883781667)
            ·
              refine ⟨34914047370853325672501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23276031580568883781667 34914047370853325672501)
              ·
                refine ⟨3273191941017499281797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34914047370853325672501 3273191941017499281797)
                ·
                  rfl

theorem cell20_21514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 5].length) (baseStart_21514 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_21514 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_21514 prefixEnd_21514 := by exact prefixLift 21514
  have htrace : WordTrace (prefixWord ++ tailWord_21514) baseStart_21514 baseEnd_21514 := by
    simpa [prefixWord, tailWord_21514, baseEnd_21514] using wordTrace_append hprefix tailTrace_21514
  have hstable : (prefixWord ++ tailWord_21514).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21514).length < 2 ^ (prefixWord ++ tailWord_21514).sum := by decide
  have hdescent : baseEnd_21514 < baseStart_21514 := by decide
  rcases family_descends (prefixWord ++ tailWord_21514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21528 : List Nat := [2, 1, 2, 3, 2, 3, 1, 2, 4]
def baseStart_21528 : Nat := 118140960795 + 21528 * 2 ^ 59
def prefixEnd_21528 : Nat := 4983230072969 + 3 ^ 40 * 21528 * 2
def baseEnd_21528 : Nat := 9825965804530671378667

theorem tailTrace_21528 : CollatzResearch.WordTrace tailWord_21528 prefixEnd_21528 9825965804530671378667 := by
  unfold tailWord_21528
  simp only [CollatzResearch.WordTrace]
  refine ⟨392595333007603767396619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 523460444010138356528825 392595333007603767396619)
  ·
    refine ⟨588892999511405651094929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 392595333007603767396619 588892999511405651094929)
    ·
      refine ⟨441669749633554238321197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 588892999511405651094929 441669749633554238321197)
      ·
        refine ⟨165626156112582839370449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 441669749633554238321197 165626156112582839370449)
        ·
          refine ⟨124219617084437129527837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165626156112582839370449 124219617084437129527837)
          ·
            refine ⟨46582356406663923572939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 124219617084437129527837 46582356406663923572939)
            ·
              refine ⟨69873534609995885359409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46582356406663923572939 69873534609995885359409)
              ·
                refine ⟨52405150957496914019557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69873534609995885359409 52405150957496914019557)
                ·
                  refine ⟨9825965804530671378667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52405150957496914019557 9825965804530671378667)
                  ·
                    rfl

theorem cell20_21528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 2, 4].length) (baseStart_21528 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_21528 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_21528 prefixEnd_21528 := by exact prefixLift 21528
  have htrace : WordTrace (prefixWord ++ tailWord_21528) baseStart_21528 baseEnd_21528 := by
    simpa [prefixWord, tailWord_21528, baseEnd_21528] using wordTrace_append hprefix tailTrace_21528
  have hstable : (prefixWord ++ tailWord_21528).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21528).length < 2 ^ (prefixWord ++ tailWord_21528).sum := by decide
  have hdescent : baseEnd_21528 < baseStart_21528 := by decide
  rcases family_descends (prefixWord ++ tailWord_21528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21618 : List Nat := [3, 2, 1, 2, 2, 1, 1, 3, 5]
def baseStart_21618 : Nat := 118140960795 + 21618 * 2 ^ 59
def prefixEnd_21618 : Nat := 4983230072969 + 3 ^ 40 * 21618 * 2
def baseEnd_21618 : Nat := 9867044256890358378299

theorem tailTrace_21618 : CollatzResearch.WordTrace tailWord_21618 prefixEnd_21618 9867044256890358378299 := by
  unfold tailWord_21618
  simp only [CollatzResearch.WordTrace]
  refine ⟨197118308922288226392377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 525648823792768603713005 197118308922288226392377)
  ·
    refine ⟨147838731691716169794283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197118308922288226392377 147838731691716169794283)
    ·
      refine ⟨221758097537574254691425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147838731691716169794283 221758097537574254691425)
      ·
        refine ⟨166318573153180691018569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 221758097537574254691425 166318573153180691018569)
        ·
          refine ⟨124738929864885518263927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166318573153180691018569 124738929864885518263927)
          ·
            refine ⟨187108394797328277395891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124738929864885518263927 187108394797328277395891)
            ·
              refine ⟨280662592195992416093837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 187108394797328277395891 280662592195992416093837)
              ·
                refine ⟨105248472073497156035189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 280662592195992416093837 105248472073497156035189)
                ·
                  refine ⟨9867044256890358378299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 105248472073497156035189 9867044256890358378299)
                  ·
                    rfl

theorem cell20_21618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_21618 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_21618 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_21618 prefixEnd_21618 := by exact prefixLift 21618
  have htrace : WordTrace (prefixWord ++ tailWord_21618) baseStart_21618 baseEnd_21618 := by
    simpa [prefixWord, tailWord_21618, baseEnd_21618] using wordTrace_append hprefix tailTrace_21618
  have hstable : (prefixWord ++ tailWord_21618).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21618).length < 2 ^ (prefixWord ++ tailWord_21618).sum := by decide
  have hdescent : baseEnd_21618 < baseStart_21618 := by decide
  rcases family_descends (prefixWord ++ tailWord_21618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21632 : List Nat := [2, 1, 1, 2, 1, 3, 3, 7]
def baseStart_21632 : Nat := 118140960795 + 21632 * 2 ^ 59
def prefixEnd_21632 : Nat := 4983230072969 + 3 ^ 40 * 21632 * 2
def baseEnd_21632 : Nat := 3291144746122843970525

theorem tailTrace_21632 : CollatzResearch.WordTrace tailWord_21632 prefixEnd_21632 3291144746122843970525 := by
  unfold tailWord_21632
  simp only [CollatzResearch.WordTrace]
  refine ⟨394491928819216648289575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 525989238425622197719433 394491928819216648289575)
  ·
    refine ⟨591737893228824972434363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 394491928819216648289575 591737893228824972434363)
    ·
      refine ⟨887606839843237458651545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 591737893228824972434363 887606839843237458651545)
      ·
        refine ⟨665705129882428093988659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 887606839843237458651545 665705129882428093988659)
        ·
          refine ⟨998557694823642140982989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 665705129882428093988659 998557694823642140982989)
          ·
            refine ⟨374459135558865802868621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 998557694823642140982989 374459135558865802868621)
            ·
              refine ⟨140422175834574676075733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 374459135558865802868621 140422175834574676075733)
              ·
                refine ⟨3291144746122843970525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 140422175834574676075733 3291144746122843970525)
                ·
                  rfl

theorem cell20_21632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 7].length) (baseStart_21632 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_21632 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_21632 prefixEnd_21632 := by exact prefixLift 21632
  have htrace : WordTrace (prefixWord ++ tailWord_21632) baseStart_21632 baseEnd_21632 := by
    simpa [prefixWord, tailWord_21632, baseEnd_21632] using wordTrace_append hprefix tailTrace_21632
  have hstable : (prefixWord ++ tailWord_21632).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21632).length < 2 ^ (prefixWord ++ tailWord_21632).sum := by decide
  have hdescent : baseEnd_21632 < baseStart_21632 := by decide
  rcases family_descends (prefixWord ++ tailWord_21632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21666 : List Nat := [3, 3, 1, 3, 3, 7]
def baseStart_21666 : Nat := 118140960795 + 21666 * 2 ^ 59
def prefixEnd_21666 : Nat := 4983230072969 + 3 ^ 40 * 21666 * 2
def baseEnd_21666 : Nat := 366257509807982399189

theorem tailTrace_21666 : CollatzResearch.WordTrace tailWord_21666 prefixEnd_21666 366257509807982399189 := by
  unfold tailWord_21666
  simp only [CollatzResearch.WordTrace]
  refine ⟨197555984878814275829213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 526815959676838068877901 197555984878814275829213)
  ·
    refine ⟨74083494329555353435955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197555984878814275829213 74083494329555353435955)
    ·
      refine ⟨111125241494333030153933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74083494329555353435955 111125241494333030153933)
      ·
        refine ⟨41671965560374886307725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111125241494333030153933 41671965560374886307725)
        ·
          refine ⟨15626987085140582365397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41671965560374886307725 15626987085140582365397)
          ·
            refine ⟨366257509807982399189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 15626987085140582365397 366257509807982399189)
            ·
              rfl

theorem cell20_21666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 7].length) (baseStart_21666 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_21666 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_21666 prefixEnd_21666 := by exact prefixLift 21666
  have htrace : WordTrace (prefixWord ++ tailWord_21666) baseStart_21666 baseEnd_21666 := by
    simpa [prefixWord, tailWord_21666, baseEnd_21666] using wordTrace_append hprefix tailTrace_21666
  have hstable : (prefixWord ++ tailWord_21666).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21666).length < 2 ^ (prefixWord ++ tailWord_21666).sum := by decide
  have hdescent : baseEnd_21666 < baseStart_21666 := by decide
  rcases family_descends (prefixWord ++ tailWord_21666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21680 : List Nat := [2, 1, 1, 1, 2, 1, 2, 8, 2]
def baseStart_21680 : Nat := 118140960795 + 21680 * 2 ^ 59
def prefixEnd_21680 : Nat := 4983230072969 + 3 ^ 40 * 21680 * 2
def baseEnd_21680 : Nat := 9895342746293698311379

theorem tailTrace_21680 : CollatzResearch.WordTrace tailWord_21680 prefixEnd_21680 9895342746293698311379 := by
  unfold tailWord_21680
  simp only [CollatzResearch.WordTrace]
  refine ⟨395367280732268747163247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 527156374309691662884329 395367280732268747163247)
  ·
    refine ⟨593050921098403120744871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 395367280732268747163247 593050921098403120744871)
    ·
      refine ⟨889576381647604681117307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 593050921098403120744871 889576381647604681117307)
      ·
        refine ⟨1334364572471407021675961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 889576381647604681117307 1334364572471407021675961)
        ·
          refine ⟨1000773429353555266256971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1334364572471407021675961 1000773429353555266256971)
          ·
            refine ⟨1501160144030332899385457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1000773429353555266256971 1501160144030332899385457)
            ·
              refine ⟨1125870108022749674539093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1501160144030332899385457 1125870108022749674539093)
              ·
                refine ⟨13193790328391597748505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1125870108022749674539093 13193790328391597748505)
                ·
                  refine ⟨9895342746293698311379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13193790328391597748505 9895342746293698311379)
                  ·
                    rfl

theorem cell20_21680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 8, 2].length) (baseStart_21680 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_21680 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_21680 prefixEnd_21680 := by exact prefixLift 21680
  have htrace : WordTrace (prefixWord ++ tailWord_21680) baseStart_21680 baseEnd_21680 := by
    simpa [prefixWord, tailWord_21680, baseEnd_21680] using wordTrace_append hprefix tailTrace_21680
  have hstable : (prefixWord ++ tailWord_21680).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21680).length < 2 ^ (prefixWord ++ tailWord_21680).sum := by decide
  have hdescent : baseEnd_21680 < baseStart_21680 := by decide
  rcases family_descends (prefixWord ++ tailWord_21680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21697 : List Nat := [1, 2, 6, 1, 1, 2, 1, 2, 4]
def baseStart_21697 : Nat := 118140960795 + 21697 * 2 ^ 59
def prefixEnd_21697 : Nat := 4983230072969 + 3 ^ 40 * 21697 * 2
def baseEnd_21697 : Nat := 9903102009517194744643

theorem tailTrace_21697 : CollatzResearch.WordTrace tailWord_21697 prefixEnd_21697 9903102009517194744643 := by
  unfold tailWord_21697
  simp only [CollatzResearch.WordTrace]
  refine ⟨791354602402949397695345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 527569734935299598463563 791354602402949397695345)
  ·
    refine ⟨593515951802212048271509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 791354602402949397695345 593515951802212048271509)
    ·
      refine ⟨27821060240728689762727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 593515951802212048271509 27821060240728689762727)
      ·
        refine ⟨41731590361093034644091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27821060240728689762727 41731590361093034644091)
        ·
          refine ⟨62597385541639551966137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41731590361093034644091 62597385541639551966137)
          ·
            refine ⟨46948039156229663974603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62597385541639551966137 46948039156229663974603)
            ·
              refine ⟨70422058734344495961905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46948039156229663974603 70422058734344495961905)
              ·
                refine ⟨52816544050758371971429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70422058734344495961905 52816544050758371971429)
                ·
                  refine ⟨9903102009517194744643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52816544050758371971429 9903102009517194744643)
                  ·
                    rfl

theorem cell20_21697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 2, 4].length) (baseStart_21697 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_21697 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_21697 prefixEnd_21697 := by exact prefixLift 21697
  have htrace : WordTrace (prefixWord ++ tailWord_21697) baseStart_21697 baseEnd_21697 := by
    simpa [prefixWord, tailWord_21697, baseEnd_21697] using wordTrace_append hprefix tailTrace_21697
  have hstable : (prefixWord ++ tailWord_21697).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21697).length < 2 ^ (prefixWord ++ tailWord_21697).sum := by decide
  have hdescent : baseEnd_21697 < baseStart_21697 := by decide
  rcases family_descends (prefixWord ++ tailWord_21697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21715 : List Nat := [1, 1, 1, 2, 1, 1, 1, 5, 7]
def baseStart_21715 : Nat := 118140960795 + 21715 * 2 ^ 59
def prefixEnd_21715 : Nat := 4983230072969 + 3 ^ 40 * 21715 * 2
def baseEnd_21715 : Nat := 9911317699989132144569

theorem tailTrace_21715 : CollatzResearch.WordTrace tailWord_21715 prefixEnd_21715 9911317699989132144569 := by
  unfold tailWord_21715
  simp only [CollatzResearch.WordTrace]
  refine ⟨792011116337738471850599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 528007410891825647900399 792011116337738471850599)
  ·
    refine ⟨1188016674506607707775899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 792011116337738471850599 1188016674506607707775899)
    ·
      refine ⟨1782025011759911561663849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1188016674506607707775899 1782025011759911561663849)
      ·
        refine ⟨1336518758819933671247887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1782025011759911561663849 1336518758819933671247887)
        ·
          refine ⟨2004778138229900506871831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1336518758819933671247887 2004778138229900506871831)
          ·
            refine ⟨3007167207344850760307747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2004778138229900506871831 3007167207344850760307747)
            ·
              refine ⟨4510750811017276140461621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3007167207344850760307747 4510750811017276140461621)
              ·
                refine ⟨422882888532869638168277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4510750811017276140461621 422882888532869638168277)
                ·
                  refine ⟨9911317699989132144569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 422882888532869638168277 9911317699989132144569)
                  ·
                    rfl

theorem cell20_21715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 7].length) (baseStart_21715 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_21715 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_21715 prefixEnd_21715 := by exact prefixLift 21715
  have htrace : WordTrace (prefixWord ++ tailWord_21715) baseStart_21715 baseEnd_21715 := by
    simpa [prefixWord, tailWord_21715, baseEnd_21715] using wordTrace_append hprefix tailTrace_21715
  have hstable : (prefixWord ++ tailWord_21715).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21715).length < 2 ^ (prefixWord ++ tailWord_21715).sum := by decide
  have hdescent : baseEnd_21715 < baseStart_21715 := by decide
  rcases family_descends (prefixWord ++ tailWord_21715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21735 : List Nat := [1, 1, 5, 3, 2, 1, 2, 1, 4]
def baseStart_21735 : Nat := 118140960795 + 21735 * 2 ^ 59
def prefixEnd_21735 : Nat := 4983230072969 + 3 ^ 40 * 21735 * 2
def baseEnd_21735 : Nat := 9920446244957951477821

theorem tailTrace_21735 : CollatzResearch.WordTrace tailWord_21735 prefixEnd_21735 9920446244957951477821 := by
  unfold tailWord_21735
  simp only [CollatzResearch.WordTrace]
  refine ⟨792740576265281887578659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 528493717510187925052439 792740576265281887578659)
  ·
    refine ⟨1189110864397922831367989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 792740576265281887578659 1189110864397922831367989)
    ·
      refine ⟨111479143537305265440749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1189110864397922831367989 111479143537305265440749)
      ·
        refine ⟨41804678826489474540281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111479143537305265440749 41804678826489474540281)
        ·
          refine ⟨31353509119867105905211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41804678826489474540281 31353509119867105905211)
          ·
            refine ⟨47030263679800658857817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31353509119867105905211 47030263679800658857817)
            ·
              refine ⟨35272697759850494143363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47030263679800658857817 35272697759850494143363)
              ·
                refine ⟨52909046639775741215045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35272697759850494143363 52909046639775741215045)
                ·
                  refine ⟨9920446244957951477821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52909046639775741215045 9920446244957951477821)
                  ·
                    rfl

theorem cell20_21735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 1, 4].length) (baseStart_21735 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_21735 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_21735 prefixEnd_21735 := by exact prefixLift 21735
  have htrace : WordTrace (prefixWord ++ tailWord_21735) baseStart_21735 baseEnd_21735 := by
    simpa [prefixWord, tailWord_21735, baseEnd_21735] using wordTrace_append hprefix tailTrace_21735
  have hstable : (prefixWord ++ tailWord_21735).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21735).length < 2 ^ (prefixWord ++ tailWord_21735).sum := by decide
  have hdescent : baseEnd_21735 < baseStart_21735 := by decide
  rcases family_descends (prefixWord ++ tailWord_21735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21739 : List Nat := [1, 1, 1, 1, 2, 6, 1, 3, 4]
def baseStart_21739 : Nat := 118140960795 + 21739 * 2 ^ 59
def prefixEnd_21739 : Nat := 4983230072969 + 3 ^ 40 * 21739 * 2
def baseEnd_21739 : Nat := 9922271953951715344471

theorem tailTrace_21739 : CollatzResearch.WordTrace tailWord_21739 prefixEnd_21739 9922271953951715344471 := by
  unfold tailWord_21739
  simp only [CollatzResearch.WordTrace]
  refine ⟨792886468250790570724271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 528590978833860380482847 792886468250790570724271)
  ·
    refine ⟨1189329702376185856086407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 792886468250790570724271 1189329702376185856086407)
    ·
      refine ⟨1783994553564278784129611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1189329702376185856086407 1783994553564278784129611)
      ·
        refine ⟨2675991830346418176194417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1783994553564278784129611 2675991830346418176194417)
        ·
          refine ⟨2006993872759813632145813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2675991830346418176194417 2006993872759813632145813)
          ·
            refine ⟨94077837785616264006835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 2006993872759813632145813 94077837785616264006835)
            ·
              refine ⟨141116756678424396010253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94077837785616264006835 141116756678424396010253)
              ·
                refine ⟨52918783754409148503845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 141116756678424396010253 52918783754409148503845)
                ·
                  refine ⟨9922271953951715344471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52918783754409148503845 9922271953951715344471)
                  ·
                    rfl

theorem cell20_21739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 3, 4].length) (baseStart_21739 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_21739 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_21739 prefixEnd_21739 := by exact prefixLift 21739
  have htrace : WordTrace (prefixWord ++ tailWord_21739) baseStart_21739 baseEnd_21739 := by
    simpa [prefixWord, tailWord_21739, baseEnd_21739] using wordTrace_append hprefix tailTrace_21739
  have hstable : (prefixWord ++ tailWord_21739).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21739).length < 2 ^ (prefixWord ++ tailWord_21739).sum := by decide
  have hdescent : baseEnd_21739 < baseStart_21739 := by decide
  rcases family_descends (prefixWord ++ tailWord_21739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21763 : List Nat := [1, 1, 1, 3, 2, 4, 4, 4]
def baseStart_21763 : Nat := 118140960795 + 21763 * 2 ^ 59
def prefixEnd_21763 : Nat := 4983230072969 + 3 ^ 40 * 21763 * 2
def baseEnd_21763 : Nat := 3311075402638099514791

theorem tailTrace_21763 : CollatzResearch.WordTrace tailWord_21763 prefixEnd_21763 3311075402638099514791 := by
  unfold tailWord_21763
  simp only [CollatzResearch.WordTrace]
  refine ⟨793761820163842669597943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 529174546775895113065295 793761820163842669597943)
  ·
    refine ⟨1190642730245764004396915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 793761820163842669597943 1190642730245764004396915)
    ·
      refine ⟨1785964095368646006595373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1190642730245764004396915 1785964095368646006595373)
      ·
        refine ⟨669736535763242252473265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1785964095368646006595373 669736535763242252473265)
        ·
          refine ⟨502302401822431689354949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 669736535763242252473265 502302401822431689354949)
          ·
            refine ⟨94181700341705941754053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 502302401822431689354949 94181700341705941754053)
            ·
              refine ⟨17659068814069864078885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 94181700341705941754053 17659068814069864078885)
              ·
                refine ⟨3311075402638099514791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17659068814069864078885 3311075402638099514791)
                ·
                  rfl

theorem cell20_21763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 4, 4].length) (baseStart_21763 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_21763 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_21763 prefixEnd_21763 := by exact prefixLift 21763
  have htrace : WordTrace (prefixWord ++ tailWord_21763) baseStart_21763 baseEnd_21763 := by
    simpa [prefixWord, tailWord_21763, baseEnd_21763] using wordTrace_append hprefix tailTrace_21763
  have hstable : (prefixWord ++ tailWord_21763).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21763).length < 2 ^ (prefixWord ++ tailWord_21763).sum := by decide
  have hdescent : baseEnd_21763 < baseStart_21763 := by decide
  rcases family_descends (prefixWord ++ tailWord_21763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21784 : List Nat := [2, 1, 2, 3, 1, 3, 8]
def baseStart_21784 : Nat := 118140960795 + 21784 * 2 ^ 59
def prefixEnd_21784 : Nat := 4983230072969 + 3 ^ 40 * 21784 * 2
def baseEnd_21784 : Nat := 1104756797792395427143

theorem tailTrace_21784 : CollatzResearch.WordTrace tailWord_21784 prefixEnd_21784 1104756797792395427143 := by
  unfold tailWord_21784
  simp only [CollatzResearch.WordTrace]
  refine ⟨397263876543881628056203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 529685168725175504074937 397263876543881628056203)
  ·
    refine ⟨595895814815822442084305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 397263876543881628056203 595895814815822442084305)
    ·
      refine ⟨446921861111866831563229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 595895814815822442084305 446921861111866831563229)
      ·
        refine ⟨167595697916950061836211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 446921861111866831563229 167595697916950061836211)
        ·
          refine ⟨251393546875425092754317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167595697916950061836211 251393546875425092754317)
          ·
            refine ⟨94272580078284409782869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 251393546875425092754317 94272580078284409782869)
            ·
              refine ⟨1104756797792395427143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 94272580078284409782869 1104756797792395427143)
              ·
                rfl

theorem cell20_21784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 8].length) (baseStart_21784 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_21784 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_21784 prefixEnd_21784 := by exact prefixLift 21784
  have htrace : WordTrace (prefixWord ++ tailWord_21784) baseStart_21784 baseEnd_21784 := by
    simpa [prefixWord, tailWord_21784, baseEnd_21784] using wordTrace_append hprefix tailTrace_21784
  have hstable : (prefixWord ++ tailWord_21784).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21784).length < 2 ^ (prefixWord ++ tailWord_21784).sum := by decide
  have hdescent : baseEnd_21784 < baseStart_21784 := by decide
  rcases family_descends (prefixWord ++ tailWord_21784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21808 : List Nat := [2, 1, 1, 1, 2, 2, 5, 3, 3]
def baseStart_21808 : Nat := 118140960795 + 21808 * 2 ^ 59
def prefixEnd_21808 : Nat := 4983230072969 + 3 ^ 40 * 21808 * 2
def baseEnd_21808 : Nat := 9953765434094142044189

theorem tailTrace_21808 : CollatzResearch.WordTrace tailWord_21808 prefixEnd_21808 9953765434094142044189 := by
  unfold tailWord_21808
  simp only [CollatzResearch.WordTrace]
  refine ⟨397701552500407677493039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 530268736667210236657385 397701552500407677493039)
  ·
    refine ⟨596552328750611516239559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 397701552500407677493039 596552328750611516239559)
    ·
      refine ⟨894828493125917274359339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 596552328750611516239559 894828493125917274359339)
      ·
        refine ⟨1342242739688875911539009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 894828493125917274359339 1342242739688875911539009)
        ·
          refine ⟨1006682054766656933654257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1342242739688875911539009 1006682054766656933654257)
          ·
            refine ⟨755011541074992700240693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1006682054766656933654257 755011541074992700240693)
            ·
              refine ⟨70782331975780565647565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 755011541074992700240693 70782331975780565647565)
              ·
                refine ⟨26543374490917712117837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70782331975780565647565 26543374490917712117837)
                ·
                  refine ⟨9953765434094142044189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26543374490917712117837 9953765434094142044189)
                  ·
                    rfl

theorem cell20_21808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 3, 3].length) (baseStart_21808 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_21808 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_21808 prefixEnd_21808 := by exact prefixLift 21808
  have htrace : WordTrace (prefixWord ++ tailWord_21808) baseStart_21808 baseEnd_21808 := by
    simpa [prefixWord, tailWord_21808, baseEnd_21808] using wordTrace_append hprefix tailTrace_21808
  have hstable : (prefixWord ++ tailWord_21808).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21808).length < 2 ^ (prefixWord ++ tailWord_21808).sum := by decide
  have hdescent : baseEnd_21808 < baseStart_21808 := by decide
  rcases family_descends (prefixWord ++ tailWord_21808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21829 : List Nat := [1, 3, 1, 1, 1, 2, 1, 3, 7]
def baseStart_21829 : Nat := 118140960795 + 21829 * 2 ^ 59
def prefixEnd_21829 : Nat := 4983230072969 + 3 ^ 40 * 21829 * 2
def baseEnd_21829 : Nat := 9963350406311402344103

theorem tailTrace_21829 : CollatzResearch.WordTrace tailWord_21829 prefixEnd_21829 9963350406311402344103 := by
  unfold tailWord_21829
  simp only [CollatzResearch.WordTrace]
  refine ⟨796169037924735941500541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 530779358616490627667027 796169037924735941500541)
  ·
    refine ⟨298563389221775978062703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 796169037924735941500541 298563389221775978062703)
    ·
      refine ⟨447845083832663967094055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298563389221775978062703 447845083832663967094055)
      ·
        refine ⟨671767625748995950641083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 447845083832663967094055 671767625748995950641083)
        ·
          refine ⟨1007651438623493925961625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 671767625748995950641083 1007651438623493925961625)
          ·
            refine ⟨755738578967620444471219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1007651438623493925961625 755738578967620444471219)
            ·
              refine ⟨1133607868451430666706829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 755738578967620444471219 1133607868451430666706829)
              ·
                refine ⟨425102950669286500015061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1133607868451430666706829 425102950669286500015061)
                ·
                  refine ⟨9963350406311402344103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 425102950669286500015061 9963350406311402344103)
                  ·
                    rfl

theorem cell20_21829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 7].length) (baseStart_21829 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_21829 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_21829 prefixEnd_21829 := by exact prefixLift 21829
  have htrace : WordTrace (prefixWord ++ tailWord_21829) baseStart_21829 baseEnd_21829 := by
    simpa [prefixWord, tailWord_21829, baseEnd_21829] using wordTrace_append hprefix tailTrace_21829
  have hstable : (prefixWord ++ tailWord_21829).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21829).length < 2 ^ (prefixWord ++ tailWord_21829).sum := by decide
  have hdescent : baseEnd_21829 < baseStart_21829 := by decide
  rcases family_descends (prefixWord ++ tailWord_21829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21832 : List Nat := [2, 1, 3, 1, 1, 2, 1, 7, 2]
def baseStart_21832 : Nat := 118140960795 + 21832 * 2 ^ 59
def prefixEnd_21832 : Nat := 4983230072969 + 3 ^ 40 * 21832 * 2
def baseEnd_21832 : Nat := 9964719688056725244091

theorem tailTrace_21832 : CollatzResearch.WordTrace tailWord_21832 prefixEnd_21832 9964719688056725244091 := by
  unfold tailWord_21832
  simp only [CollatzResearch.WordTrace]
  refine ⟨398139228456933726929875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 530852304609244969239833 398139228456933726929875)
  ·
    refine ⟨597208842685400590394813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 398139228456933726929875 597208842685400590394813)
    ·
      refine ⟨223953316007025221398055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 597208842685400590394813 223953316007025221398055)
      ·
        refine ⟨335929974010537832097083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223953316007025221398055 335929974010537832097083)
        ·
          refine ⟨503894961015806748145625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 335929974010537832097083 503894961015806748145625)
          ·
            refine ⟨377921220761855061109219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 503894961015806748145625 377921220761855061109219)
            ·
              refine ⟨566881831142782591663829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 377921220761855061109219 566881831142782591663829)
              ·
                refine ⟨13286292917408966992121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 566881831142782591663829 13286292917408966992121)
                ·
                  refine ⟨9964719688056725244091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13286292917408966992121 9964719688056725244091)
                  ·
                    rfl

theorem cell20_21832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 7, 2].length) (baseStart_21832 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_21832 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_21832 prefixEnd_21832 := by exact prefixLift 21832
  have htrace : WordTrace (prefixWord ++ tailWord_21832) baseStart_21832 baseEnd_21832 := by
    simpa [prefixWord, tailWord_21832, baseEnd_21832] using wordTrace_append hprefix tailTrace_21832
  have hstable : (prefixWord ++ tailWord_21832).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21832).length < 2 ^ (prefixWord ++ tailWord_21832).sum := by decide
  have hdescent : baseEnd_21832 < baseStart_21832 := by decide
  rcases family_descends (prefixWord ++ tailWord_21832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21849 : List Nat := [1, 2, 1, 2, 2, 2, 6, 2, 2]
def baseStart_21849 : Nat := 118140960795 + 21849 * 2 ^ 59
def prefixEnd_21849 : Nat := 4983230072969 + 3 ^ 40 * 21849 * 2
def baseEnd_21849 : Nat := 9972478951280221677355

theorem tailTrace_21849 : CollatzResearch.WordTrace tailWord_21849 prefixEnd_21849 9972478951280221677355 := by
  unfold tailWord_21849
  simp only [CollatzResearch.WordTrace]
  refine ⟨796898497852279357228601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 531265665234852904819067 796898497852279357228601)
  ·
    refine ⟨597673873389209517921451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 796898497852279357228601 597673873389209517921451)
    ·
      refine ⟨896510810083814276882177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 597673873389209517921451 896510810083814276882177)
      ·
        refine ⟨672383107562860707661633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 896510810083814276882177 672383107562860707661633)
        ·
          refine ⟨504287330672145530746225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 672383107562860707661633 504287330672145530746225)
          ·
            refine ⟨378215498004109148059669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 504287330672145530746225 378215498004109148059669)
            ·
              refine ⟨17728851468942616315297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 378215498004109148059669 17728851468942616315297)
              ·
                refine ⟨13296638601706962236473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17728851468942616315297 13296638601706962236473)
                ·
                  refine ⟨9972478951280221677355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13296638601706962236473 9972478951280221677355)
                  ·
                    rfl

theorem cell20_21849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 6, 2, 2].length) (baseStart_21849 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_21849 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_21849 prefixEnd_21849 := by exact prefixLift 21849
  have htrace : WordTrace (prefixWord ++ tailWord_21849) baseStart_21849 baseEnd_21849 := by
    simpa [prefixWord, tailWord_21849, baseEnd_21849] using wordTrace_append hprefix tailTrace_21849
  have hstable : (prefixWord ++ tailWord_21849).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21849).length < 2 ^ (prefixWord ++ tailWord_21849).sum := by decide
  have hdescent : baseEnd_21849 < baseStart_21849 := by decide
  rcases family_descends (prefixWord ++ tailWord_21849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21905 : List Nat := [1, 2, 2, 1, 1, 1, 2, 5, 5]
def baseStart_21905 : Nat := 118140960795 + 21905 * 2 ^ 59
def prefixEnd_21905 : Nat := 4983230072969 + 3 ^ 40 * 21905 * 2
def baseEnd_21905 : Nat := 9998038877192915810459

theorem tailTrace_21905 : CollatzResearch.WordTrace tailWord_21905 prefixEnd_21905 9998038877192915810459 := by
  unfold tailWord_21905
  simp only [CollatzResearch.WordTrace]
  refine ⟨798940985649400921267169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 532627323766267280844779 798940985649400921267169)
  ·
    refine ⟨599205739237050690950377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 798940985649400921267169 599205739237050690950377)
    ·
      refine ⟨449404304427788018212783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 599205739237050690950377 449404304427788018212783)
      ·
        refine ⟨674106456641682027319175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 449404304427788018212783 674106456641682027319175)
        ·
          refine ⟨1011159684962523040978763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 674106456641682027319175 1011159684962523040978763)
          ·
            refine ⟨1516739527443784561468145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1011159684962523040978763 1516739527443784561468145)
            ·
              refine ⟨1137554645582838421101109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1516739527443784561468145 1137554645582838421101109)
              ·
                refine ⟨106645748023391101978229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1137554645582838421101109 106645748023391101978229)
                ·
                  refine ⟨9998038877192915810459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 106645748023391101978229 9998038877192915810459)
                  ·
                    rfl

theorem cell20_21905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 5, 5].length) (baseStart_21905 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_21905 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_21905 prefixEnd_21905 := by exact prefixLift 21905
  have htrace : WordTrace (prefixWord ++ tailWord_21905) baseStart_21905 baseEnd_21905 := by
    simpa [prefixWord, tailWord_21905, baseEnd_21905] using wordTrace_append hprefix tailTrace_21905
  have hstable : (prefixWord ++ tailWord_21905).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21905).length < 2 ^ (prefixWord ++ tailWord_21905).sum := by decide
  have hdescent : baseEnd_21905 < baseStart_21905 := by decide
  rcases family_descends (prefixWord ++ tailWord_21905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21908 : List Nat := [2, 4, 2, 1, 2, 1, 1, 3, 4]
def baseStart_21908 : Nat := 118140960795 + 21908 * 2 ^ 59
def prefixEnd_21908 : Nat := 4983230072969 + 3 ^ 40 * 21908 * 2
def baseEnd_21908 : Nat := 9999408158938238710447

theorem tailTrace_21908 : CollatzResearch.WordTrace tailWord_21908 prefixEnd_21908 9999408158938238710447 := by
  unfold tailWord_21908
  simp only [CollatzResearch.WordTrace]
  refine ⟨399525202319266216813189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 532700269759021622417585 399525202319266216813189)
  ·
    refine ⟨74910975434862415652473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 399525202319266216813189 74910975434862415652473)
    ·
      refine ⟨56183231576146811739355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74910975434862415652473 56183231576146811739355)
      ·
        refine ⟨84274847364220217609033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56183231576146811739355 84274847364220217609033)
        ·
          refine ⟨63206135523165163206775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84274847364220217609033 63206135523165163206775)
          ·
            refine ⟨94809203284747744810163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63206135523165163206775 94809203284747744810163)
            ·
              refine ⟨142213804927121617215245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94809203284747744810163 142213804927121617215245)
              ·
                refine ⟨53330176847670606455717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 142213804927121617215245 53330176847670606455717)
                ·
                  refine ⟨9999408158938238710447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53330176847670606455717 9999408158938238710447)
                  ·
                    rfl

theorem cell20_21908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_21908 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_21908 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_21908 prefixEnd_21908 := by exact prefixLift 21908
  have htrace : WordTrace (prefixWord ++ tailWord_21908) baseStart_21908 baseEnd_21908 := by
    simpa [prefixWord, tailWord_21908, baseEnd_21908] using wordTrace_append hprefix tailTrace_21908
  have hstable : (prefixWord ++ tailWord_21908).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21908).length < 2 ^ (prefixWord ++ tailWord_21908).sum := by decide
  have hdescent : baseEnd_21908 < baseStart_21908 := by decide
  rcases family_descends (prefixWord ++ tailWord_21908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21928 : List Nat := [2, 1, 6, 1, 3, 1, 2, 4]
def baseStart_21928 : Nat := 118140960795 + 21928 * 2 ^ 59
def prefixEnd_21928 : Nat := 4983230072969 + 3 ^ 40 * 21928 * 2
def baseEnd_21928 : Nat := 3336178901302352681233

theorem tailTrace_21928 : CollatzResearch.WordTrace tailWord_21928 prefixEnd_21928 3336178901302352681233 := by
  unfold tailWord_21928
  simp only [CollatzResearch.WordTrace]
  refine ⟨399889932283037924677219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 533186576377383899569625 399889932283037924677219)
  ·
    refine ⟨599834898424556887015829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 399889932283037924677219 599834898424556887015829)
    ·
      refine ⟨28117260863651104078867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 599834898424556887015829 28117260863651104078867)
      ·
        refine ⟨42175891295476656118301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28117260863651104078867 42175891295476656118301)
        ·
          refine ⟨15815959235803746044363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42175891295476656118301 15815959235803746044363)
          ·
            refine ⟨23723938853705619066545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15815959235803746044363 23723938853705619066545)
            ·
              refine ⟨17792954140279214299909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23723938853705619066545 17792954140279214299909)
              ·
                refine ⟨3336178901302352681233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17792954140279214299909 3336178901302352681233)
                ·
                  rfl

theorem cell20_21928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 2, 4].length) (baseStart_21928 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_21928 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_21928 prefixEnd_21928 := by exact prefixLift 21928
  have htrace : WordTrace (prefixWord ++ tailWord_21928) baseStart_21928 baseEnd_21928 := by
    simpa [prefixWord, tailWord_21928, baseEnd_21928] using wordTrace_append hprefix tailTrace_21928
  have hstable : (prefixWord ++ tailWord_21928).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21928).length < 2 ^ (prefixWord ++ tailWord_21928).sum := by decide
  have hdescent : baseEnd_21928 < baseStart_21928 := by decide
  rcases family_descends (prefixWord ++ tailWord_21928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21943 : List Nat := [1, 1, 3, 1, 3, 2, 1, 1, 7]
def baseStart_21943 : Nat := 118140960795 + 21943 * 2 ^ 59
def prefixEnd_21943 : Nat := 4983230072969 + 3 ^ 40 * 21943 * 2
def baseEnd_21943 : Nat := 10015383112633672543637

theorem tailTrace_21943 : CollatzResearch.WordTrace tailWord_21943 prefixEnd_21943 10015383112633672543637 := by
  unfold tailWord_21943
  simp only [CollatzResearch.WordTrace]
  refine ⟨800326959511733411150483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 533551306341155607433655 800326959511733411150483)
  ·
    refine ⟨1200490439267600116725725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 800326959511733411150483 1200490439267600116725725)
    ·
      refine ⟨450183914725350043772147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1200490439267600116725725 450183914725350043772147)
      ·
        refine ⟨675275872088025065658221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 450183914725350043772147 675275872088025065658221)
        ·
          refine ⟨253228452033009399621833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 675275872088025065658221 253228452033009399621833)
          ·
            refine ⟨189921339024757049716375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 253228452033009399621833 189921339024757049716375)
            ·
              refine ⟨284882008537135574574563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 189921339024757049716375 284882008537135574574563)
              ·
                refine ⟨427323012805703361861845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 284882008537135574574563 427323012805703361861845)
                ·
                  refine ⟨10015383112633672543637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 427323012805703361861845 10015383112633672543637)
                  ·
                    rfl

theorem cell20_21943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 7].length) (baseStart_21943 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_21943 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_21943 prefixEnd_21943 := by exact prefixLift 21943
  have htrace : WordTrace (prefixWord ++ tailWord_21943) baseStart_21943 baseEnd_21943 := by
    simpa [prefixWord, tailWord_21943, baseEnd_21943] using wordTrace_append hprefix tailTrace_21943
  have hstable : (prefixWord ++ tailWord_21943).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21943).length < 2 ^ (prefixWord ++ tailWord_21943).sum := by decide
  have hdescent : baseEnd_21943 < baseStart_21943 := by decide
  rcases family_descends (prefixWord ++ tailWord_21943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21960 : List Nat := [2, 1, 3, 1, 3, 1, 2, 4, 3]
def baseStart_21960 : Nat := 118140960795 + 21960 * 2 ^ 59
def prefixEnd_21960 : Nat := 4983230072969 + 3 ^ 40 * 21960 * 2
def baseEnd_21960 : Nat := 10023142375857168976901

theorem tailTrace_21960 : CollatzResearch.WordTrace tailWord_21960 prefixEnd_21960 10023142375857168976901 := by
  unfold tailWord_21960
  simp only [CollatzResearch.WordTrace]
  refine ⟨400473500225072657259667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 533964666966763543012889 400473500225072657259667)
  ·
    refine ⟨600710250337608985889501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 400473500225072657259667 600710250337608985889501)
    ·
      refine ⟨225266343876603369708563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 600710250337608985889501 225266343876603369708563)
      ·
        refine ⟨337899515814905054562845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225266343876603369708563 337899515814905054562845)
        ·
          refine ⟨126712318430589395461067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 337899515814905054562845 126712318430589395461067)
          ·
            refine ⟨190068477645884093191601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126712318430589395461067 190068477645884093191601)
            ·
              refine ⟨142551358234413069893701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 190068477645884093191601 142551358234413069893701)
              ·
                refine ⟨26728379668952450605069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 142551358234413069893701 26728379668952450605069)
                ·
                  refine ⟨10023142375857168976901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26728379668952450605069 10023142375857168976901)
                  ·
                    rfl

theorem cell20_21960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 4, 3].length) (baseStart_21960 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_21960 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_21960 prefixEnd_21960 := by exact prefixLift 21960
  have htrace : WordTrace (prefixWord ++ tailWord_21960) baseStart_21960 baseEnd_21960 := by
    simpa [prefixWord, tailWord_21960, baseEnd_21960] using wordTrace_append hprefix tailTrace_21960
  have hstable : (prefixWord ++ tailWord_21960).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21960).length < 2 ^ (prefixWord ++ tailWord_21960).sum := by decide
  have hdescent : baseEnd_21960 < baseStart_21960 := by decide
  rcases family_descends (prefixWord ++ tailWord_21960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21967 : List Nat := [1, 1, 2, 1, 1, 4, 5, 1, 4]
def baseStart_21967 : Nat := 118140960795 + 21967 * 2 ^ 59
def prefixEnd_21967 : Nat := 4983230072969 + 3 ^ 40 * 21967 * 2
def baseEnd_21967 : Nat := 10026337366596255743539

theorem tailTrace_21967 : CollatzResearch.WordTrace tailWord_21967 prefixEnd_21967 10026337366596255743539 := by
  unfold tailWord_21967
  simp only [CollatzResearch.WordTrace]
  refine ⟨801202311424785510024155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 534134874283190340016103 801202311424785510024155)
  ·
    refine ⟨1201803467137178265036233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 801202311424785510024155 1201803467137178265036233)
    ·
      refine ⟨901352600352883698777175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1201803467137178265036233 901352600352883698777175)
      ·
        refine ⟨1352028900529325548165763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 901352600352883698777175 1352028900529325548165763)
        ·
          refine ⟨2028043350793988322248645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1352028900529325548165763 2028043350793988322248645)
          ·
            refine ⟨380258128273872810421621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2028043350793988322248645 380258128273872810421621)
            ·
              refine ⟨35649199525675575977027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 380258128273872810421621 35649199525675575977027)
              ·
                refine ⟨53473799288513363965541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35649199525675575977027 53473799288513363965541)
                ·
                  refine ⟨10026337366596255743539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53473799288513363965541 10026337366596255743539)
                  ·
                    rfl

theorem cell20_21967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 1, 4].length) (baseStart_21967 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_21967 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_21967 prefixEnd_21967 := by exact prefixLift 21967
  have htrace : WordTrace (prefixWord ++ tailWord_21967) baseStart_21967 baseEnd_21967 := by
    simpa [prefixWord, tailWord_21967, baseEnd_21967] using wordTrace_append hprefix tailTrace_21967
  have hstable : (prefixWord ++ tailWord_21967).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21967).length < 2 ^ (prefixWord ++ tailWord_21967).sum := by decide
  have hdescent : baseEnd_21967 < baseStart_21967 := by decide
  rcases family_descends (prefixWord ++ tailWord_21967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21977 : List Nat := [1, 2, 1, 2, 4, 2, 4, 1, 3]
def baseStart_21977 : Nat := 118140960795 + 21977 * 2 ^ 59
def prefixEnd_21977 : Nat := 4983230072969 + 3 ^ 40 * 21977 * 2
def baseEnd_21977 : Nat := 10030901639080665410165

theorem tailTrace_21977 : CollatzResearch.WordTrace tailWord_21977 prefixEnd_21977 10030901639080665410165 := by
  unfold tailWord_21977
  simp only [CollatzResearch.WordTrace]
  refine ⟨801567041388557217888185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 534378027592371478592123 801567041388557217888185)
  ·
    refine ⟨601175281041417913416139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 801567041388557217888185 601175281041417913416139)
    ·
      refine ⟨901762921562126870124209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 601175281041417913416139 901762921562126870124209)
      ·
        refine ⟨676322191171595152593157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 901762921562126870124209 676322191171595152593157)
        ·
          refine ⟨126810410844674091111217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 676322191171595152593157 126810410844674091111217)
          ·
            refine ⟨95107808133505568333413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126810410844674091111217 95107808133505568333413)
            ·
              refine ⟨17832714025032294062515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 95107808133505568333413 17832714025032294062515)
              ·
                refine ⟨26749071037548441093773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17832714025032294062515 26749071037548441093773)
                ·
                  refine ⟨10030901639080665410165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26749071037548441093773 10030901639080665410165)
                  ·
                    rfl

theorem cell20_21977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 4, 1, 3].length) (baseStart_21977 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_21977 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_21977 prefixEnd_21977 := by exact prefixLift 21977
  have htrace : WordTrace (prefixWord ++ tailWord_21977) baseStart_21977 baseEnd_21977 := by
    simpa [prefixWord, tailWord_21977, baseEnd_21977] using wordTrace_append hprefix tailTrace_21977
  have hstable : (prefixWord ++ tailWord_21977).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21977).length < 2 ^ (prefixWord ++ tailWord_21977).sum := by decide
  have hdescent : baseEnd_21977 < baseStart_21977 := by decide
  rcases family_descends (prefixWord ++ tailWord_21977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22014 : List Nat := [4, 2, 2, 3, 1, 2, 2, 2, 2]
def baseStart_22014 : Nat := 118140960795 + 22014 * 2 ^ 59
def prefixEnd_22014 : Nat := 4983230072969 + 3 ^ 40 * 22014 * 2
def baseEnd_22014 : Nat := 10047789447272981176681

theorem tailTrace_22014 : CollatzResearch.WordTrace tailWord_22014 prefixEnd_22014 10047789447272981176681 := by
  unfold tailWord_22014
  simp only [CollatzResearch.WordTrace]
  refine ⟨100364567781814067123137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 535277694836341691323397 100364567781814067123137)
  ·
    refine ⟨75273425836360550342353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100364567781814067123137 75273425836360550342353)
    ·
      refine ⟨56455069377270412756765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75273425836360550342353 56455069377270412756765)
      ·
        refine ⟨21170651016476404783787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56455069377270412756765 21170651016476404783787)
        ·
          refine ⟨31755976524714607175681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21170651016476404783787 31755976524714607175681)
          ·
            refine ⟨23816982393535955381761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31755976524714607175681 23816982393535955381761)
            ·
              refine ⟨17862736795151966536321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23816982393535955381761 17862736795151966536321)
              ·
                refine ⟨13397052596363974902241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17862736795151966536321 13397052596363974902241)
                ·
                  refine ⟨10047789447272981176681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13397052596363974902241 10047789447272981176681)
                  ·
                    rfl

theorem cell20_22014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 2, 2, 2].length) (baseStart_22014 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_22014 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_22014 prefixEnd_22014 := by exact prefixLift 22014
  have htrace : WordTrace (prefixWord ++ tailWord_22014) baseStart_22014 baseEnd_22014 := by
    simpa [prefixWord, tailWord_22014, baseEnd_22014] using wordTrace_append hprefix tailTrace_22014
  have hstable : (prefixWord ++ tailWord_22014).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22014).length < 2 ^ (prefixWord ++ tailWord_22014).sum := by decide
  have hdescent : baseEnd_22014 < baseStart_22014 := by decide
  rcases family_descends (prefixWord ++ tailWord_22014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22018 : List Nat := [3, 4, 1, 2, 1, 2, 1, 4, 2]
def baseStart_22018 : Nat := 118140960795 + 22018 * 2 ^ 59
def prefixEnd_22018 : Nat := 4983230072969 + 3 ^ 40 * 22018 * 2
def baseEnd_22018 : Nat := 10049615156266745043331

theorem tailTrace_22018 : CollatzResearch.WordTrace tailWord_22018 prefixEnd_22018 10049615156266745043331 := by
  unfold tailWord_22018
  simp only [CollatzResearch.WordTrace]
  refine ⟨200765608560005305032677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 535374956160014146753805 200765608560005305032677)
  ·
    refine ⟨37643551605000994693627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 200765608560005305032677 37643551605000994693627)
    ·
      refine ⟨56465327407501492040441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37643551605000994693627 56465327407501492040441)
      ·
        refine ⟨42348995555626119030331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56465327407501492040441 42348995555626119030331)
        ·
          refine ⟨63523493333439178545497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42348995555626119030331 63523493333439178545497)
          ·
            refine ⟨47642620000079383909123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63523493333439178545497 47642620000079383909123)
            ·
              refine ⟨71463930000119075863685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47642620000079383909123 71463930000119075863685)
              ·
                refine ⟨13399486875022326724441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71463930000119075863685 13399486875022326724441)
                ·
                  refine ⟨10049615156266745043331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13399486875022326724441 10049615156266745043331)
                  ·
                    rfl

theorem cell20_22018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_22018 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_22018 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_22018 prefixEnd_22018 := by exact prefixLift 22018
  have htrace : WordTrace (prefixWord ++ tailWord_22018) baseStart_22018 baseEnd_22018 := by
    simpa [prefixWord, tailWord_22018, baseEnd_22018] using wordTrace_append hprefix tailTrace_22018
  have hstable : (prefixWord ++ tailWord_22018).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22018).length < 2 ^ (prefixWord ++ tailWord_22018).sum := by decide
  have hdescent : baseEnd_22018 < baseStart_22018 := by decide
  rcases family_descends (prefixWord ++ tailWord_22018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22050 : List Nat := [3, 3, 1, 1, 1, 1, 2, 8]
def baseStart_22050 : Nat := 118140960795 + 22050 * 2 ^ 59
def prefixEnd_22050 : Nat := 4983230072969 + 3 ^ 40 * 22050 * 2
def baseEnd_22050 : Nat := 3354740276072285325511

theorem tailTrace_22050 : CollatzResearch.WordTrace tailWord_22050 prefixEnd_22050 3354740276072285325511 := by
  unfold tailWord_22050
  simp only [CollatzResearch.WordTrace]
  refine ⟨201057392531022671323901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 536153046749393790197069 201057392531022671323901)
  ·
    refine ⟨75396522199133501746463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201057392531022671323901 75396522199133501746463)
    ·
      refine ⟨113094783298700252619695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75396522199133501746463 113094783298700252619695)
      ·
        refine ⟨169642174948050378929543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113094783298700252619695 169642174948050378929543)
        ·
          refine ⟨254463262422075568394315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169642174948050378929543 254463262422075568394315)
          ·
            refine ⟨381694893633113352591473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 254463262422075568394315 381694893633113352591473)
            ·
              refine ⟨286271170224835014443605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 381694893633113352591473 286271170224835014443605)
              ·
                refine ⟨3354740276072285325511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 286271170224835014443605 3354740276072285325511)
                ·
                  rfl

theorem cell20_22050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 8].length) (baseStart_22050 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_22050 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_22050 prefixEnd_22050 := by exact prefixLift 22050
  have htrace : WordTrace (prefixWord ++ tailWord_22050) baseStart_22050 baseEnd_22050 := by
    simpa [prefixWord, tailWord_22050, baseEnd_22050] using wordTrace_append hprefix tailTrace_22050
  have hstable : (prefixWord ++ tailWord_22050).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22050).length < 2 ^ (prefixWord ++ tailWord_22050).sum := by decide
  have hdescent : baseEnd_22050 < baseStart_22050 := by decide
  rcases family_descends (prefixWord ++ tailWord_22050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22056 : List Nat := [2, 1, 5, 2, 2, 1, 2, 3, 2]
def baseStart_22056 : Nat := 118140960795 + 22056 * 2 ^ 59
def prefixEnd_22056 : Nat := 4983230072969 + 3 ^ 40 * 22056 * 2
def baseEnd_22056 : Nat := 10066959391707501776509

theorem tailTrace_22056 : CollatzResearch.WordTrace tailWord_22056 prefixEnd_22056 10066959391707501776509 := by
  unfold tailWord_22056
  simp only [CollatzResearch.WordTrace]
  refine ⟨402224204051176855007011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 536298938734902473342681 402224204051176855007011)
  ·
    refine ⟨603336306076765282510517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 402224204051176855007011 603336306076765282510517)
    ·
      refine ⟨56562778694696745235361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 603336306076765282510517 56562778694696745235361)
      ·
        refine ⟨42422084021022558926521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56562778694696745235361 42422084021022558926521)
        ·
          refine ⟨31816563015766919194891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42422084021022558926521 31816563015766919194891)
          ·
            refine ⟨47724844523650378792337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31816563015766919194891 47724844523650378792337)
            ·
              refine ⟨35793633392737784094253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47724844523650378792337 35793633392737784094253)
              ·
                refine ⟨13422612522276669035345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35793633392737784094253 13422612522276669035345)
                ·
                  refine ⟨10066959391707501776509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13422612522276669035345 10066959391707501776509)
                  ·
                    rfl

theorem cell20_22056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 3, 2].length) (baseStart_22056 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_22056 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_22056 prefixEnd_22056 := by exact prefixLift 22056
  have htrace : WordTrace (prefixWord ++ tailWord_22056) baseStart_22056 baseEnd_22056 := by
    simpa [prefixWord, tailWord_22056, baseEnd_22056] using wordTrace_append hprefix tailTrace_22056
  have hstable : (prefixWord ++ tailWord_22056).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22056).length < 2 ^ (prefixWord ++ tailWord_22056).sum := by decide
  have hdescent : baseEnd_22056 < baseStart_22056 := by decide
  rcases family_descends (prefixWord ++ tailWord_22056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22064 : List Nat := [2, 1, 1, 1, 2, 3, 1, 1, 8]
def baseStart_22064 : Nat := 118140960795 + 22064 * 2 ^ 59
def prefixEnd_22064 : Nat := 4983230072969 + 3 ^ 40 * 22064 * 2
def baseEnd_22064 : Nat := 10070610809695029509809

theorem tailTrace_22064 : CollatzResearch.WordTrace tailWord_22064 prefixEnd_22064 10070610809695029509809 := by
  unfold tailWord_22064
  simp only [CollatzResearch.WordTrace]
  refine ⟨402370096036685538152623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 536493461382247384203497 402370096036685538152623)
  ·
    refine ⟨603555144055028307228935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 402370096036685538152623 603555144055028307228935)
    ·
      refine ⟨905332716082542460843403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 603555144055028307228935 905332716082542460843403)
      ·
        refine ⟨1357999074123813691265105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 905332716082542460843403 1357999074123813691265105)
        ·
          refine ⟨1018499305592860268448829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1357999074123813691265105 1018499305592860268448829)
          ·
            refine ⟨381937239597322600668311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1018499305592860268448829 381937239597322600668311)
            ·
              refine ⟨572905859395983901002467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 381937239597322600668311 572905859395983901002467)
              ·
                refine ⟨859358789093975851503701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 572905859395983901002467 859358789093975851503701)
                ·
                  refine ⟨10070610809695029509809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 859358789093975851503701 10070610809695029509809)
                  ·
                    rfl

theorem cell20_22064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 8].length) (baseStart_22064 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_22064 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_22064 prefixEnd_22064 := by exact prefixLift 22064
  have htrace : WordTrace (prefixWord ++ tailWord_22064) baseStart_22064 baseEnd_22064 := by
    simpa [prefixWord, tailWord_22064, baseEnd_22064] using wordTrace_append hprefix tailTrace_22064
  have hstable : (prefixWord ++ tailWord_22064).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22064).length < 2 ^ (prefixWord ++ tailWord_22064).sum := by decide
  have hdescent : baseEnd_22064 < baseStart_22064 := by decide
  rcases family_descends (prefixWord ++ tailWord_22064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22115 : List Nat := [1, 1, 1, 5, 1, 5, 1, 3, 2]
def baseStart_22115 : Nat := 118140960795 + 22115 * 2 ^ 59
def prefixEnd_22115 : Nat := 4983230072969 + 3 ^ 40 * 22115 * 2
def baseEnd_22115 : Nat := 10093888599365518809601

theorem tailTrace_22115 : CollatzResearch.WordTrace tailWord_22115 prefixEnd_22115 10093888599365518809601 := by
  unfold tailWord_22115
  simp only [CollatzResearch.WordTrace]
  refine ⟨806600314888606786411799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 537733543259071190941199 806600314888606786411799)
  ·
    refine ⟨1209900472332910179617699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 806600314888606786411799 1209900472332910179617699)
    ·
      refine ⟨1814850708499365269426549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1209900472332910179617699 1814850708499365269426549)
      ·
        refine ⟨170142253921815494008739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1814850708499365269426549 170142253921815494008739)
        ·
          refine ⟨255213380882723241013109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170142253921815494008739 255213380882723241013109)
          ·
            refine ⟨23926254457755303844979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 255213380882723241013109 23926254457755303844979)
            ·
              refine ⟨35889381686632955767469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23926254457755303844979 35889381686632955767469)
              ·
                refine ⟨13458518132487358412801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35889381686632955767469 13458518132487358412801)
                ·
                  refine ⟨10093888599365518809601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13458518132487358412801 10093888599365518809601)
                  ·
                    rfl

theorem cell20_22115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 3, 2].length) (baseStart_22115 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_22115 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_22115 prefixEnd_22115 := by exact prefixLift 22115
  have htrace : WordTrace (prefixWord ++ tailWord_22115) baseStart_22115 baseEnd_22115 := by
    simpa [prefixWord, tailWord_22115, baseEnd_22115] using wordTrace_append hprefix tailTrace_22115
  have hstable : (prefixWord ++ tailWord_22115).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22115).length < 2 ^ (prefixWord ++ tailWord_22115).sum := by decide
  have hdescent : baseEnd_22115 < baseStart_22115 := by decide
  rcases family_descends (prefixWord ++ tailWord_22115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22198 : List Nat := [5, 1, 3, 1, 1, 1, 3, 5]
def baseStart_22198 : Nat := 118140960795 + 22198 * 2 ^ 59
def prefixEnd_22198 : Nat := 4983230072969 + 3 ^ 40 * 22198 * 2
def baseEnd_22198 : Nat := 3377257353662039680865

theorem tailTrace_22198 : CollatzResearch.WordTrace tailWord_22198 prefixEnd_22198 3377257353662039680865 := by
  unfold tailWord_22198
  simp only [CollatzResearch.WordTrace]
  refine ⟨50601723349244497605203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 539751715725274641122165 50601723349244497605203)
  ·
    refine ⟨75902585023866746407805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50601723349244497605203 75902585023866746407805)
    ·
      refine ⟨28463469383950029902927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75902585023866746407805 28463469383950029902927)
      ·
        refine ⟨42695204075925044854391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28463469383950029902927 42695204075925044854391)
        ·
          refine ⟨64042806113887567281587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42695204075925044854391 64042806113887567281587)
          ·
            refine ⟨96064209170831350922381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64042806113887567281587 96064209170831350922381)
            ·
              refine ⟨36024078439061756595893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96064209170831350922381 36024078439061756595893)
              ·
                refine ⟨3377257353662039680865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36024078439061756595893 3377257353662039680865)
                ·
                  rfl

theorem cell20_22198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_22198 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_22198 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_22198 prefixEnd_22198 := by exact prefixLift 22198
  have htrace : WordTrace (prefixWord ++ tailWord_22198) baseStart_22198 baseEnd_22198 := by
    simpa [prefixWord, tailWord_22198, baseEnd_22198] using wordTrace_append hprefix tailTrace_22198
  have hstable : (prefixWord ++ tailWord_22198).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22198).length < 2 ^ (prefixWord ++ tailWord_22198).sum := by decide
  have hdescent : baseEnd_22198 < baseStart_22198 := by decide
  rcases family_descends (prefixWord ++ tailWord_22198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22202 : List Nat := [3, 1, 1, 1, 2, 4, 3, 5]
def baseStart_22202 : Nat := 118140960795 + 22202 * 2 ^ 59
def prefixEnd_22202 : Nat := 4983230072969 + 3 ^ 40 * 22202 * 2
def baseEnd_22202 : Nat := 3377865923326627636415

theorem tailTrace_22202 : CollatzResearch.WordTrace tailWord_22202 prefixEnd_22202 3377865923326627636415 := by
  unfold tailWord_22202
  simp only [CollatzResearch.WordTrace]
  refine ⟨202443366393355161207215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 539848977048947096552573 202443366393355161207215)
  ·
    refine ⟨303665049590032741810823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202443366393355161207215 303665049590032741810823)
    ·
      refine ⟨455497574385049112716235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303665049590032741810823 455497574385049112716235)
      ·
        refine ⟨683246361577573669074353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 455497574385049112716235 683246361577573669074353)
        ·
          refine ⟨512434771183180251805765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 683246361577573669074353 512434771183180251805765)
          ·
            refine ⟨96081519596846297213581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 512434771183180251805765 96081519596846297213581)
            ·
              refine ⟨36030569848817361455093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96081519596846297213581 36030569848817361455093)
              ·
                refine ⟨3377865923326627636415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36030569848817361455093 3377865923326627636415)
                ·
                  rfl

theorem cell20_22202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 5].length) (baseStart_22202 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_22202 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_22202 prefixEnd_22202 := by exact prefixLift 22202
  have htrace : WordTrace (prefixWord ++ tailWord_22202) baseStart_22202 baseEnd_22202 := by
    simpa [prefixWord, tailWord_22202, baseEnd_22202] using wordTrace_append hprefix tailTrace_22202
  have hstable : (prefixWord ++ tailWord_22202).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22202).length < 2 ^ (prefixWord ++ tailWord_22202).sum := by decide
  have hdescent : baseEnd_22202 < baseStart_22202 := by decide
  rcases family_descends (prefixWord ++ tailWord_22202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22223 : List Nat := [1, 1, 2, 1, 1, 3, 1, 10]
def baseStart_22223 : Nat := 118140960795 + 22223 * 2 ^ 59
def prefixEnd_22223 : Nat := 4983230072969 + 3 ^ 40 * 22223 * 2
def baseEnd_22223 : Nat := 3381060914065714403053

theorem tailTrace_22223 : CollatzResearch.WordTrace tailWord_22223 prefixEnd_22223 3381060914065714403053 := by
  unfold tailWord_22223
  simp only [CollatzResearch.WordTrace]
  refine ⟨810539398497341231343323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 540359598998227487562215 810539398497341231343323)
  ·
    refine ⟨1215809097746011847014985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 810539398497341231343323 1215809097746011847014985)
    ·
      refine ⟨911856823309508885261239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1215809097746011847014985 911856823309508885261239)
      ·
        refine ⟨1367785234964263327891859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 911856823309508885261239 1367785234964263327891859)
        ·
          refine ⟨2051677852446394991837789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1367785234964263327891859 2051677852446394991837789)
          ·
            refine ⟨769379194667398121939171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2051677852446394991837789 769379194667398121939171)
            ·
              refine ⟨1154068792001097182908757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 769379194667398121939171 1154068792001097182908757)
              ·
                refine ⟨3381060914065714403053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 1154068792001097182908757 3381060914065714403053)
                ·
                  rfl

theorem cell20_22223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 10].length) (baseStart_22223 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_22223 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_22223 prefixEnd_22223 := by exact prefixLift 22223
  have htrace : WordTrace (prefixWord ++ tailWord_22223) baseStart_22223 baseEnd_22223 := by
    simpa [prefixWord, tailWord_22223, baseEnd_22223] using wordTrace_append hprefix tailTrace_22223
  have hstable : (prefixWord ++ tailWord_22223).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22223).length < 2 ^ (prefixWord ++ tailWord_22223).sum := by decide
  have hdescent : baseEnd_22223 < baseStart_22223 := by decide
  rcases family_descends (prefixWord ++ tailWord_22223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22250 : List Nat := [3, 1, 3, 1, 1, 1, 4, 4, 2]
def baseStart_22250 : Nat := 118140960795 + 22250 * 2 ^ 59
def prefixEnd_22250 : Nat := 4983230072969 + 3 ^ 40 * 22250 * 2
def baseEnd_22250 : Nat := 10155506277905049309049

theorem tailTrace_22250 : CollatzResearch.WordTrace tailWord_22250 prefixEnd_22250 10155506277905049309049 := by
  unfold tailWord_22250
  simp only [CollatzResearch.WordTrace]
  refine ⟨202881042349881210644051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 541016112933016561717469 202881042349881210644051)
  ·
    refine ⟨304321563524821815966077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202881042349881210644051 304321563524821815966077)
    ·
      refine ⟨114120586321808180987279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 304321563524821815966077 114120586321808180987279)
      ·
        refine ⟨171180879482712271480919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114120586321808180987279 171180879482712271480919)
        ·
          refine ⟨256771319224068407221379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171180879482712271480919 256771319224068407221379)
          ·
            refine ⟨385156978836102610832069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 256771319224068407221379 385156978836102610832069)
            ·
              refine ⟨72216933531769239531013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 385156978836102610832069 72216933531769239531013)
              ·
                refine ⟨13540675037206732412065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72216933531769239531013 13540675037206732412065)
                ·
                  refine ⟨10155506277905049309049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13540675037206732412065 10155506277905049309049)
                  ·
                    rfl

theorem cell20_22250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 4, 2].length) (baseStart_22250 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_22250 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_22250 prefixEnd_22250 := by exact prefixLift 22250
  have htrace : WordTrace (prefixWord ++ tailWord_22250) baseStart_22250 baseEnd_22250 := by
    simpa [prefixWord, tailWord_22250, baseEnd_22250] using wordTrace_append hprefix tailTrace_22250
  have hstable : (prefixWord ++ tailWord_22250).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22250).length < 2 ^ (prefixWord ++ tailWord_22250).sum := by decide
  have hdescent : baseEnd_22250 < baseStart_22250 := by decide
  rcases family_descends (prefixWord ++ tailWord_22250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22305 : List Nat := [1, 2, 3, 2, 1, 4, 3, 2, 2]
def baseStart_22305 : Nat := 118140960795 + 22305 * 2 ^ 59
def prefixEnd_22305 : Nat := 4983230072969 + 3 ^ 40 * 22305 * 2
def baseEnd_22305 : Nat := 10180609776569302475491

theorem tailTrace_22305 : CollatzResearch.WordTrace tailWord_22305 prefixEnd_22305 10180609776569302475491 := by
  unfold tailWord_22305
  simp only [CollatzResearch.WordTrace]
  refine ⟨813530184200269235828369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 542353456133512823885579 813530184200269235828369)
  ·
    refine ⟨610147638150201926871277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 813530184200269235828369 610147638150201926871277)
    ·
      refine ⟨228805364306325722576729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 610147638150201926871277 228805364306325722576729)
      ·
        refine ⟨171604023229744291932547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 228805364306325722576729 171604023229744291932547)
        ·
          refine ⟨257406034844616437898821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171604023229744291932547 257406034844616437898821)
          ·
            refine ⟨48263631533365582106029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 257406034844616437898821 48263631533365582106029)
            ·
              refine ⟨18098861825012093289761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48263631533365582106029 18098861825012093289761)
              ·
                refine ⟨13574146368759069967321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18098861825012093289761 13574146368759069967321)
                ·
                  refine ⟨10180609776569302475491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13574146368759069967321 10180609776569302475491)
                  ·
                    rfl

theorem cell20_22305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 3, 2, 2].length) (baseStart_22305 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_22305 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_22305 prefixEnd_22305 := by exact prefixLift 22305
  have htrace : WordTrace (prefixWord ++ tailWord_22305) baseStart_22305 baseEnd_22305 := by
    simpa [prefixWord, tailWord_22305, baseEnd_22305] using wordTrace_append hprefix tailTrace_22305
  have hstable : (prefixWord ++ tailWord_22305).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22305).length < 2 ^ (prefixWord ++ tailWord_22305).sum := by decide
  have hdescent : baseEnd_22305 < baseStart_22305 := by decide
  rcases family_descends (prefixWord ++ tailWord_22305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22309 : List Nat := [1, 3, 1, 2, 3, 2, 3, 1, 4]
def baseStart_22309 : Nat := 118140960795 + 22309 * 2 ^ 59
def prefixEnd_22309 : Nat := 4983230072969 + 3 ^ 40 * 22309 * 2
def baseEnd_22309 : Nat := 10182435485563066342141

theorem tailTrace_22309 : CollatzResearch.WordTrace tailWord_22309 prefixEnd_22309 10182435485563066342141 := by
  unfold tailWord_22309
  simp only [CollatzResearch.WordTrace]
  refine ⟨813676076185777918973981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 542450717457185279315987 813676076185777918973981)
  ·
    refine ⟨305128528569666719615243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 813676076185777918973981 305128528569666719615243)
    ·
      refine ⟨457692792854500079422865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305128528569666719615243 457692792854500079422865)
      ·
        refine ⟨343269594640875059567149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 457692792854500079422865 343269594640875059567149)
        ·
          refine ⟨128726097990328147337681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 343269594640875059567149 128726097990328147337681)
          ·
            refine ⟨96544573492746110503261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128726097990328147337681 96544573492746110503261)
            ·
              refine ⟨36204215059779791438723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96544573492746110503261 36204215059779791438723)
              ·
                refine ⟨54306322589669687158085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36204215059779791438723 54306322589669687158085)
                ·
                  refine ⟨10182435485563066342141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54306322589669687158085 10182435485563066342141)
                  ·
                    rfl

theorem cell20_22309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 1, 4].length) (baseStart_22309 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_22309 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_22309 prefixEnd_22309 := by exact prefixLift 22309
  have htrace : WordTrace (prefixWord ++ tailWord_22309) baseStart_22309 baseEnd_22309 := by
    simpa [prefixWord, tailWord_22309, baseEnd_22309] using wordTrace_append hprefix tailTrace_22309
  have hstable : (prefixWord ++ tailWord_22309).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22309).length < 2 ^ (prefixWord ++ tailWord_22309).sum := by decide
  have hdescent : baseEnd_22309 < baseStart_22309 := by decide
  rcases family_descends (prefixWord ++ tailWord_22309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22316 : List Nat := [2, 2, 1, 1, 1, 6, 2, 5]
def baseStart_22316 : Nat := 118140960795 + 22316 * 2 ^ 59
def prefixEnd_22316 : Nat := 4983230072969 + 3 ^ 40 * 22316 * 2
def baseEnd_22316 : Nat := 3395210158767384369593

theorem tailTrace_22316 : CollatzResearch.WordTrace tailWord_22316 prefixEnd_22316 3395210158767384369593 := by
  unfold tailWord_22316
  simp only [CollatzResearch.WordTrace]
  refine ⟨406965693580209057239401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 542620924773612076319201 406965693580209057239401)
  ·
    refine ⟨305224270185156792929551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 406965693580209057239401 305224270185156792929551)
    ·
      refine ⟨457836405277735189394327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305224270185156792929551 457836405277735189394327)
      ·
        refine ⟨686754607916602784091491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 457836405277735189394327 686754607916602784091491)
        ·
          refine ⟨1030131911874904176137237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 686754607916602784091491 1030131911874904176137237)
          ·
            refine ⟨48287433369136133256433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1030131911874904176137237 48287433369136133256433)
            ·
              refine ⟨36215575026852099942325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48287433369136133256433 36215575026852099942325)
              ·
                refine ⟨3395210158767384369593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36215575026852099942325 3395210158767384369593)
                ·
                  rfl

theorem cell20_22316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 5].length) (baseStart_22316 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_22316 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_22316 prefixEnd_22316 := by exact prefixLift 22316
  have htrace : WordTrace (prefixWord ++ tailWord_22316) baseStart_22316 baseEnd_22316 := by
    simpa [prefixWord, tailWord_22316, baseEnd_22316] using wordTrace_append hprefix tailTrace_22316
  have hstable : (prefixWord ++ tailWord_22316).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22316).length < 2 ^ (prefixWord ++ tailWord_22316).sum := by decide
  have hdescent : baseEnd_22316 < baseStart_22316 := by decide
  rcases family_descends (prefixWord ++ tailWord_22316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22371 : List Nat := [1, 1, 1, 5, 4, 2, 1, 5]
def baseStart_22371 : Nat := 118140960795 + 22371 * 2 ^ 59
def prefixEnd_22371 : Nat := 4983230072969 + 3 ^ 40 * 22371 * 2
def baseEnd_22371 : Nat := 3403577991655468758407

theorem tailTrace_22371 : CollatzResearch.WordTrace tailWord_22371 prefixEnd_22371 3403577991655468758407 := by
  unfold tailWord_22371
  simp only [CollatzResearch.WordTrace]
  refine ⟨815937401961162507730967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 543958267974108338487311 815937401961162507730967)
  ·
    refine ⟨1223906102941743761596451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 815937401961162507730967 1223906102941743761596451)
    ·
      refine ⟨1835859154412615642394677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1223906102941743761596451 1835859154412615642394677)
      ·
        refine ⟨172111795726182716474501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1835859154412615642394677 172111795726182716474501)
        ·
          refine ⟨32270961698659259338969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 172111795726182716474501 32270961698659259338969)
          ·
            refine ⟨24203221273994444504227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32270961698659259338969 24203221273994444504227)
            ·
              refine ⟨36304831910991666756341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24203221273994444504227 36304831910991666756341)
              ·
                refine ⟨3403577991655468758407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36304831910991666756341 3403577991655468758407)
                ·
                  rfl

theorem cell20_22371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 5].length) (baseStart_22371 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_22371 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_22371 prefixEnd_22371 := by exact prefixLift 22371
  have htrace : WordTrace (prefixWord ++ tailWord_22371) baseStart_22371 baseEnd_22371 := by
    simpa [prefixWord, tailWord_22371, baseEnd_22371] using wordTrace_append hprefix tailTrace_22371
  have hstable : (prefixWord ++ tailWord_22371).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22371).length < 2 ^ (prefixWord ++ tailWord_22371).sum := by decide
  have hdescent : baseEnd_22371 < baseStart_22371 := by decide
  rcases family_descends (prefixWord ++ tailWord_22371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22398 : List Nat := [4, 2, 3, 1, 1, 2, 2, 3, 2]
def baseStart_22398 : Nat := 118140960795 + 22398 * 2 ^ 59
def prefixEnd_22398 : Nat := 4983230072969 + 3 ^ 40 * 22398 * 2
def baseEnd_22398 : Nat := 10223057510674312375111

theorem tailTrace_22398 : CollatzResearch.WordTrace tailWord_22398 prefixEnd_22398 10223057510674312375111 := by
  unfold tailWord_22398
  simp only [CollatzResearch.WordTrace]
  refine ⟨102115271607918264870481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 544614781908897412642565 102115271607918264870481)
  ·
    refine ⟨76586453705938698652861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102115271607918264870481 76586453705938698652861)
    ·
      refine ⟨28719920139727011994823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76586453705938698652861 28719920139727011994823)
      ·
        refine ⟨43079880209590517992235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28719920139727011994823 43079880209590517992235)
        ·
          refine ⟨64619820314385776988353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43079880209590517992235 64619820314385776988353)
          ·
            refine ⟨48464865235789332741265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64619820314385776988353 48464865235789332741265)
            ·
              refine ⟨36348648926841999555949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48464865235789332741265 36348648926841999555949)
              ·
                refine ⟨13630743347565749833481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36348648926841999555949 13630743347565749833481)
                ·
                  refine ⟨10223057510674312375111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13630743347565749833481 10223057510674312375111)
                  ·
                    rfl

theorem cell20_22398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 3, 2].length) (baseStart_22398 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_22398 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_22398 prefixEnd_22398 := by exact prefixLift 22398
  have htrace : WordTrace (prefixWord ++ tailWord_22398) baseStart_22398 baseEnd_22398 := by
    simpa [prefixWord, tailWord_22398, baseEnd_22398] using wordTrace_append hprefix tailTrace_22398
  have hstable : (prefixWord ++ tailWord_22398).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22398).length < 2 ^ (prefixWord ++ tailWord_22398).sum := by decide
  have hdescent : baseEnd_22398 < baseStart_22398 := by decide
  rcases family_descends (prefixWord ++ tailWord_22398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22423 : List Nat := [1, 1, 3, 3, 1, 4, 2, 1, 4]
def baseStart_22423 : Nat := 118140960795 + 22423 * 2 ^ 59
def prefixEnd_22423 : Nat := 4983230072969 + 3 ^ 40 * 22423 * 2
def baseEnd_22423 : Nat := 10234468191885336541675

theorem tailTrace_22423 : CollatzResearch.WordTrace tailWord_22423 prefixEnd_22423 10234468191885336541675 := by
  unfold tailWord_22423
  simp only [CollatzResearch.WordTrace]
  refine ⟨817833997772775388623923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 545222665181850259082615 817833997772775388623923)
  ·
    refine ⟨1226750996659163082935885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 817833997772775388623923 1226750996659163082935885)
    ·
      refine ⟨460031623747186156100957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1226750996659163082935885 460031623747186156100957)
      ·
        refine ⟨172511858905194808537859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 460031623747186156100957 172511858905194808537859)
        ·
          refine ⟨258767788357792212806789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172511858905194808537859 258767788357792212806789)
          ·
            refine ⟨48518960317086039901273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 258767788357792212806789 48518960317086039901273)
            ·
              refine ⟨36389220237814529925955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48518960317086039901273 36389220237814529925955)
              ·
                refine ⟨54583830356721794888933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36389220237814529925955 54583830356721794888933)
                ·
                  refine ⟨10234468191885336541675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54583830356721794888933 10234468191885336541675)
                  ·
                    rfl

theorem cell20_22423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 1, 4].length) (baseStart_22423 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_22423 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_22423 prefixEnd_22423 := by exact prefixLift 22423
  have htrace : WordTrace (prefixWord ++ tailWord_22423) baseStart_22423 baseEnd_22423 := by
    simpa [prefixWord, tailWord_22423, baseEnd_22423] using wordTrace_append hprefix tailTrace_22423
  have hstable : (prefixWord ++ tailWord_22423).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22423).length < 2 ^ (prefixWord ++ tailWord_22423).sum := by decide
  have hdescent : baseEnd_22423 < baseStart_22423 := by decide
  rcases family_descends (prefixWord ++ tailWord_22423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22437 : List Nat := [1, 3, 1, 2, 1, 1, 1, 7, 3]
def baseStart_22437 : Nat := 118140960795 + 22437 * 2 ^ 59
def prefixEnd_22437 : Nat := 4983230072969 + 3 ^ 40 * 22437 * 2
def baseEnd_22437 : Nat := 10240858173363510074951

theorem tailTrace_22437 : CollatzResearch.WordTrace tailWord_22437 prefixEnd_22437 10240858173363510074951 := by
  unfold tailWord_22437
  simp only [CollatzResearch.WordTrace]
  refine ⟨818344619722055779633565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 545563079814703853089043 818344619722055779633565)
  ·
    refine ⟨306879232395770917362587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 818344619722055779633565 306879232395770917362587)
    ·
      refine ⟨460318848593656376043881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306879232395770917362587 460318848593656376043881)
      ·
        refine ⟨345239136445242282032911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 460318848593656376043881 345239136445242282032911)
        ·
          refine ⟨517858704667863423049367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 345239136445242282032911 517858704667863423049367)
          ·
            refine ⟨776788057001795134574051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 517858704667863423049367 776788057001795134574051)
            ·
              refine ⟨1165182085502692701861077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 776788057001795134574051 1165182085502692701861077)
              ·
                refine ⟨27308955128969360199869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1165182085502692701861077 27308955128969360199869)
                ·
                  refine ⟨10240858173363510074951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27308955128969360199869 10240858173363510074951)
                  ·
                    rfl

theorem cell20_22437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 7, 3].length) (baseStart_22437 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_22437 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_22437 prefixEnd_22437 := by exact prefixLift 22437
  have htrace : WordTrace (prefixWord ++ tailWord_22437) baseStart_22437 baseEnd_22437 := by
    simpa [prefixWord, tailWord_22437, baseEnd_22437] using wordTrace_append hprefix tailTrace_22437
  have hstable : (prefixWord ++ tailWord_22437).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22437).length < 2 ^ (prefixWord ++ tailWord_22437).sum := by decide
  have hdescent : baseEnd_22437 < baseStart_22437 := by decide
  rcases family_descends (prefixWord ++ tailWord_22437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22451 : List Nat := [1, 1, 1, 2, 3, 1, 5, 6]
def baseStart_22451 : Nat := 118140960795 + 22451 * 2 ^ 59
def prefixEnd_22451 : Nat := 4983230072969 + 3 ^ 40 * 22451 * 2
def baseEnd_22451 : Nat := 3415749384947227869409

theorem tailTrace_22451 : CollatzResearch.WordTrace tailWord_22451 prefixEnd_22451 3415749384947227869409 := by
  unfold tailWord_22451
  simp only [CollatzResearch.WordTrace]
  refine ⟨818855241671336170643207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 545903494447557447095471 818855241671336170643207)
  ·
    refine ⟨1228282862507004255964811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 818855241671336170643207 1228282862507004255964811)
    ·
      refine ⟨1842424293760506383947217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1228282862507004255964811 1842424293760506383947217)
      ·
        refine ⟨1381818220320379787960413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1842424293760506383947217 1381818220320379787960413)
        ·
          refine ⟨518181832620142420485155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1381818220320379787960413 518181832620142420485155)
          ·
            refine ⟨777272748930213630727733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 518181832620142420485155 777272748930213630727733)
            ·
              refine ⟨72869320212207527880725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 777272748930213630727733 72869320212207527880725)
              ·
                refine ⟨3415749384947227869409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 72869320212207527880725 3415749384947227869409)
                ·
                  rfl

theorem cell20_22451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 6].length) (baseStart_22451 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_22451 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_22451 prefixEnd_22451 := by exact prefixLift 22451
  have htrace : WordTrace (prefixWord ++ tailWord_22451) baseStart_22451 baseEnd_22451 := by
    simpa [prefixWord, tailWord_22451, baseEnd_22451] using wordTrace_append hprefix tailTrace_22451
  have hstable : (prefixWord ++ tailWord_22451).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22451).length < 2 ^ (prefixWord ++ tailWord_22451).sum := by decide
  have hdescent : baseEnd_22451 < baseStart_22451 := by decide
  rcases family_descends (prefixWord ++ tailWord_22451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22475 : List Nat := [1, 1, 1, 1, 3, 4, 2, 4, 3]
def baseStart_22475 : Nat := 118140960795 + 22475 * 2 ^ 59
def prefixEnd_22475 : Nat := 4983230072969 + 3 ^ 40 * 22475 * 2
def baseEnd_22475 : Nat := 10258202408804266808129

theorem tailTrace_22475 : CollatzResearch.WordTrace tailWord_22475 prefixEnd_22475 10258202408804266808129 := by
  unfold tailWord_22475
  simp only [CollatzResearch.WordTrace]
  refine ⟨819730593584388269516879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 546487062389592179677919 819730593584388269516879)
  ·
    refine ⟨1229595890376582404275319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 819730593584388269516879 1229595890376582404275319)
    ·
      refine ⟨1844393835564873606412979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1229595890376582404275319 1844393835564873606412979)
      ·
        refine ⟨2766590753347310409619469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1844393835564873606412979 2766590753347310409619469)
        ·
          refine ⟨1037471532505241403607301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2766590753347310409619469 1037471532505241403607301)
          ·
            refine ⟨194525912344732763176369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1037471532505241403607301 194525912344732763176369)
            ·
              refine ⟨145894434258549572382277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 194525912344732763176369 145894434258549572382277)
              ·
                refine ⟨27355206423478044821677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 145894434258549572382277 27355206423478044821677)
                ·
                  refine ⟨10258202408804266808129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27355206423478044821677 10258202408804266808129)
                  ·
                    rfl

theorem cell20_22475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 4, 3].length) (baseStart_22475 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_22475 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_22475 prefixEnd_22475 := by exact prefixLift 22475
  have htrace : WordTrace (prefixWord ++ tailWord_22475) baseStart_22475 baseEnd_22475 := by
    simpa [prefixWord, tailWord_22475, baseEnd_22475] using wordTrace_append hprefix tailTrace_22475
  have hstable : (prefixWord ++ tailWord_22475).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22475).length < 2 ^ (prefixWord ++ tailWord_22475).sum := by decide
  have hdescent : baseEnd_22475 < baseStart_22475 := by decide
  rcases family_descends (prefixWord ++ tailWord_22475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22533 : List Nat := [1, 3, 1, 1, 2, 6, 2, 2, 2]
def baseStart_22533 : Nat := 118140960795 + 22533 * 2 ^ 59
def prefixEnd_22533 : Nat := 4983230072969 + 3 ^ 40 * 22533 * 2
def baseEnd_22533 : Nat := 10284675189213842874559

theorem tailTrace_22533 : CollatzResearch.WordTrace tailWord_22533 prefixEnd_22533 10284675189213842874559 := by
  unfold tailWord_22533
  simp only [CollatzResearch.WordTrace]
  refine ⟨821846027374264175128253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 547897351582842783418835 821846027374264175128253)
  ·
    refine ⟨308192260265349065673095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 821846027374264175128253 308192260265349065673095)
    ·
      refine ⟨462288390398023598509643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308192260265349065673095 462288390398023598509643)
      ·
        refine ⟨693432585597035397764465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 462288390398023598509643 693432585597035397764465)
        ·
          refine ⟨520074439197776548323349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 693432585597035397764465 520074439197776548323349)
          ·
            refine ⟨24378489337395775702657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 520074439197776548323349 24378489337395775702657)
            ·
              refine ⟨18283867003046831776993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24378489337395775702657 18283867003046831776993)
              ·
                refine ⟨13712900252285123832745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18283867003046831776993 13712900252285123832745)
                ·
                  refine ⟨10284675189213842874559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13712900252285123832745 10284675189213842874559)
                  ·
                    rfl

theorem cell20_22533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 2, 2, 2].length) (baseStart_22533 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_22533 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_22533 prefixEnd_22533 := by exact prefixLift 22533
  have htrace : WordTrace (prefixWord ++ tailWord_22533) baseStart_22533 baseEnd_22533 := by
    simpa [prefixWord, tailWord_22533, baseEnd_22533] using wordTrace_append hprefix tailTrace_22533
  have hstable : (prefixWord ++ tailWord_22533).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22533).length < 2 ^ (prefixWord ++ tailWord_22533).sum := by decide
  have hdescent : baseEnd_22533 < baseStart_22533 := by decide
  rcases family_descends (prefixWord ++ tailWord_22533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22561 : List Nat := [1, 2, 3, 2, 4, 1, 3, 4]
def baseStart_22561 : Nat := 118140960795 + 22561 * 2 ^ 59
def prefixEnd_22561 : Nat := 4983230072969 + 3 ^ 40 * 22561 * 2
def baseEnd_22561 : Nat := 3432485050723396647037

theorem tailTrace_22561 : CollatzResearch.WordTrace tailWord_22561 prefixEnd_22561 3432485050723396647037 := by
  unfold tailWord_22561
  simp only [CollatzResearch.WordTrace]
  refine ⟨822867271272824957147537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 548578180848549971431691 822867271272824957147537)
  ·
    refine ⟨617150453454618717860653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 822867271272824957147537 617150453454618717860653)
    ·
      refine ⟨231431420045482019197745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 617150453454618717860653 231431420045482019197745)
      ·
        refine ⟨173573565034111514398309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 231431420045482019197745 173573565034111514398309)
        ·
          refine ⟨32545043443895908949683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 173573565034111514398309 32545043443895908949683)
          ·
            refine ⟨48817565165843863424525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32545043443895908949683 48817565165843863424525)
            ·
              refine ⟨18306586937191448784197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48817565165843863424525 18306586937191448784197)
              ·
                refine ⟨3432485050723396647037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18306586937191448784197 3432485050723396647037)
                ·
                  rfl

theorem cell20_22561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 3, 4].length) (baseStart_22561 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_22561 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_22561 prefixEnd_22561 := by exact prefixLift 22561
  have htrace : WordTrace (prefixWord ++ tailWord_22561) baseStart_22561 baseEnd_22561 := by
    simpa [prefixWord, tailWord_22561, baseEnd_22561] using wordTrace_append hprefix tailTrace_22561
  have hstable : (prefixWord ++ tailWord_22561).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22561).length < 2 ^ (prefixWord ++ tailWord_22561).sum := by decide
  have hdescent : baseEnd_22561 < baseStart_22561 := by decide
  rcases family_descends (prefixWord ++ tailWord_22561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22582 : List Nat := [5, 1, 2, 1, 1, 1, 9]
def baseStart_22582 : Nat := 118140960795 + 22582 * 2 ^ 59
def prefixEnd_22582 : Nat := 4983230072969 + 3 ^ 40 * 22582 * 2
def baseEnd_22582 : Nat := 1145226680487494471225

theorem tailTrace_22582 : CollatzResearch.WordTrace tailWord_22582 prefixEnd_22582 1145226680487494471225 := by
  unfold tailWord_22582
  simp only [CollatzResearch.WordTrace]
  refine ⟨51477075262296596478875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 549088802797830362441333 51477075262296596478875)
  ·
    refine ⟨77215612893444894718313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51477075262296596478875 77215612893444894718313)
    ·
      refine ⟨57911709670083671038735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77215612893444894718313 57911709670083671038735)
      ·
        refine ⟨86867564505125506558103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57911709670083671038735 86867564505125506558103)
        ·
          refine ⟨130301346757688259837155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86867564505125506558103 130301346757688259837155)
          ·
            refine ⟨195452020136532389755733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130301346757688259837155 195452020136532389755733)
            ·
              refine ⟨1145226680487494471225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 195452020136532389755733 1145226680487494471225)
              ·
                rfl

theorem cell20_22582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 9].length) (baseStart_22582 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_22582 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_22582 prefixEnd_22582 := by exact prefixLift 22582
  have htrace : WordTrace (prefixWord ++ tailWord_22582) baseStart_22582 baseEnd_22582 := by
    simpa [prefixWord, tailWord_22582, baseEnd_22582] using wordTrace_append hprefix tailTrace_22582
  have hstable : (prefixWord ++ tailWord_22582).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22582).length < 2 ^ (prefixWord ++ tailWord_22582).sum := by decide
  have hdescent : baseEnd_22582 < baseStart_22582 := by decide
  rcases family_descends (prefixWord ++ tailWord_22582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22585 : List Nat := [1, 2, 1, 5, 3, 2, 1, 2, 3]
def baseStart_22585 : Nat := 118140960795 + 22585 * 2 ^ 59
def prefixEnd_22585 : Nat := 4983230072969 + 3 ^ 40 * 22585 * 2
def baseEnd_22585 : Nat := 10308409406132773141013

theorem tailTrace_22585 : CollatzResearch.WordTrace tailWord_22585 prefixEnd_22585 10308409406132773141013 := by
  unfold tailWord_22585
  simp only [CollatzResearch.WordTrace]
  refine ⟨823742623185877056021209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 549161748790584704014139 823742623185877056021209)
  ·
    refine ⟨617806967389407792015907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 823742623185877056021209 617806967389407792015907)
    ·
      refine ⟨926710451084111688023861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 617806967389407792015907 926710451084111688023861)
      ·
        refine ⟨86879104789135470752237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 926710451084111688023861 86879104789135470752237)
        ·
          refine ⟨32579664295925801532089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86879104789135470752237 32579664295925801532089)
          ·
            refine ⟨24434748221944351149067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32579664295925801532089 24434748221944351149067)
            ·
              refine ⟨36652122332916526723601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24434748221944351149067 36652122332916526723601)
              ·
                refine ⟨27489091749687395042701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36652122332916526723601 27489091749687395042701)
                ·
                  refine ⟨10308409406132773141013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27489091749687395042701 10308409406132773141013)
                  ·
                    rfl

theorem cell20_22585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 2, 3].length) (baseStart_22585 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_22585 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_22585 prefixEnd_22585 := by exact prefixLift 22585
  have htrace : WordTrace (prefixWord ++ tailWord_22585) baseStart_22585 baseEnd_22585 := by
    simpa [prefixWord, tailWord_22585, baseEnd_22585] using wordTrace_append hprefix tailTrace_22585
  have hstable : (prefixWord ++ tailWord_22585).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22585).length < 2 ^ (prefixWord ++ tailWord_22585).sum := by decide
  have hdescent : baseEnd_22585 < baseStart_22585 := by decide
  rcases family_descends (prefixWord ++ tailWord_22585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22589 : List Nat := [1, 4, 1, 3, 1, 1, 3, 1, 5]
def baseStart_22589 : Nat := 118140960795 + 22589 * 2 ^ 59
def prefixEnd_22589 : Nat := 4983230072969 + 3 ^ 40 * 22589 * 2
def baseEnd_22589 : Nat := 10310235115126537007663

theorem tailTrace_22589 : CollatzResearch.WordTrace tailWord_22589 prefixEnd_22589 10310235115126537007663 := by
  unfold tailWord_22589
  simp only [CollatzResearch.WordTrace]
  refine ⟨823888515171385739166821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 549259010114257159444547 823888515171385739166821)
  ·
    refine ⟨154479096594634826093779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 823888515171385739166821 154479096594634826093779)
    ·
      refine ⟨231718644891952239140669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154479096594634826093779 231718644891952239140669)
      ·
        refine ⟨86894491834482089677751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 231718644891952239140669 86894491834482089677751)
        ·
          refine ⟨130341737751723134516627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86894491834482089677751 130341737751723134516627)
          ·
            refine ⟨195512606627584701774941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130341737751723134516627 195512606627584701774941)
            ·
              refine ⟨73317227485344263165603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 195512606627584701774941 73317227485344263165603)
              ·
                refine ⟨109975841228016394748405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73317227485344263165603 109975841228016394748405)
                ·
                  refine ⟨10310235115126537007663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 109975841228016394748405 10310235115126537007663)
                  ·
                    rfl

theorem cell20_22589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_22589 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_22589 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_22589 prefixEnd_22589 := by exact prefixLift 22589
  have htrace : WordTrace (prefixWord ++ tailWord_22589) baseStart_22589 baseEnd_22589 := by
    simpa [prefixWord, tailWord_22589, baseEnd_22589] using wordTrace_append hprefix tailTrace_22589
  have hstable : (prefixWord ++ tailWord_22589).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22589).length < 2 ^ (prefixWord ++ tailWord_22589).sum := by decide
  have hdescent : baseEnd_22589 < baseStart_22589 := by decide
  rcases family_descends (prefixWord ++ tailWord_22589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22620 : List Nat := [2, 2, 4, 1, 1, 3, 1, 6]
def baseStart_22620 : Nat := 118140960795 + 22620 * 2 ^ 59
def prefixEnd_22620 : Nat := 4983230072969 + 3 ^ 40 * 22620 * 2
def baseEnd_22620 : Nat := 3441461453276068991401

theorem tailTrace_22620 : CollatzResearch.WordTrace tailWord_22620 prefixEnd_22620 3441461453276068991401 := by
  unfold tailWord_22620
  simp only [CollatzResearch.WordTrace]
  refine ⟨412509589029539016772657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 550012785372718689030209 412509589029539016772657)
  ·
    refine ⟨309382191772154262579493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 412509589029539016772657 309382191772154262579493)
    ·
      refine ⟨58009160957278924233655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 309382191772154262579493 58009160957278924233655)
      ·
        refine ⟨87013741435918386350483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58009160957278924233655 87013741435918386350483)
        ·
          refine ⟨130520612153877579525725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87013741435918386350483 130520612153877579525725)
          ·
            refine ⟨48945229557704092322147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130520612153877579525725 48945229557704092322147)
            ·
              refine ⟨73417844336556138483221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48945229557704092322147 73417844336556138483221)
              ·
                refine ⟨3441461453276068991401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 73417844336556138483221 3441461453276068991401)
                ·
                  rfl

theorem cell20_22620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 6].length) (baseStart_22620 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_22620 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_22620 prefixEnd_22620 := by exact prefixLift 22620
  have htrace : WordTrace (prefixWord ++ tailWord_22620) baseStart_22620 baseEnd_22620 := by
    simpa [prefixWord, tailWord_22620, baseEnd_22620] using wordTrace_append hprefix tailTrace_22620
  have hstable : (prefixWord ++ tailWord_22620).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22620).length < 2 ^ (prefixWord ++ tailWord_22620).sum := by decide
  have hdescent : baseEnd_22620 < baseStart_22620 := by decide
  rcases family_descends (prefixWord ++ tailWord_22620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22622 : List Nat := [4, 4, 1, 1, 3, 1, 1, 3, 2]
def baseStart_22622 : Nat := 118140960795 + 22622 * 2 ^ 59
def prefixEnd_22622 : Nat := 4983230072969 + 3 ^ 40 * 22622 * 2
def baseEnd_22622 : Nat := 10325297214325088907529

theorem tailTrace_22622 : CollatzResearch.WordTrace tailWord_22622 prefixEnd_22622 10325297214325088907529 := by
  unfold tailWord_22622
  simp only [CollatzResearch.WordTrace]
  refine ⟨103136515506479046889765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 550061416034554916745413 103136515506479046889765)
  ·
    refine ⟨19338096657464821291831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103136515506479046889765 19338096657464821291831)
    ·
      refine ⟨29007144986197231937747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19338096657464821291831 29007144986197231937747)
      ·
        refine ⟨43510717479295847906621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29007144986197231937747 43510717479295847906621)
        ·
          refine ⟨16316519054735942964983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43510717479295847906621 16316519054735942964983)
          ·
            refine ⟨24474778582103914447475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16316519054735942964983 24474778582103914447475)
            ·
              refine ⟨36712167873155871671213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24474778582103914447475 36712167873155871671213)
              ·
                refine ⟨13767062952433451876705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36712167873155871671213 13767062952433451876705)
                ·
                  refine ⟨10325297214325088907529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13767062952433451876705 10325297214325088907529)
                  ·
                    rfl

theorem cell20_22622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_22622 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_22622 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_22622 prefixEnd_22622 := by exact prefixLift 22622
  have htrace : WordTrace (prefixWord ++ tailWord_22622) baseStart_22622 baseEnd_22622 := by
    simpa [prefixWord, tailWord_22622, baseEnd_22622] using wordTrace_append hprefix tailTrace_22622
  have hstable : (prefixWord ++ tailWord_22622).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22622).length < 2 ^ (prefixWord ++ tailWord_22622).sum := by decide
  have hdescent : baseEnd_22622 < baseStart_22622 := by decide
  rcases family_descends (prefixWord ++ tailWord_22622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22626 : List Nat := [3, 3, 2, 2, 2, 2, 1, 3, 2]
def baseStart_22626 : Nat := 118140960795 + 22626 * 2 ^ 59
def prefixEnd_22626 : Nat := 4983230072969 + 3 ^ 40 * 22626 * 2
def baseEnd_22626 : Nat := 10327122923318852774179

theorem tailTrace_22626 : CollatzResearch.WordTrace tailWord_22626 prefixEnd_22626 10327122923318852774179 := by
  unfold tailWord_22626
  simp only [CollatzResearch.WordTrace]
  refine ⟨206309504009335264565933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 550158677358227372175821 206309504009335264565933)
  ·
    refine ⟨77366064003500724212225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206309504009335264565933 77366064003500724212225)
    ·
      refine ⟨58024548002625543159169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77366064003500724212225 58024548002625543159169)
      ·
        refine ⟨43518411001969157369377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58024548002625543159169 43518411001969157369377)
        ·
          refine ⟨32638808251476868027033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43518411001969157369377 32638808251476868027033)
          ·
            refine ⟨24479106188607651020275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32638808251476868027033 24479106188607651020275)
            ·
              refine ⟨36718659282911476530413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24479106188607651020275 36718659282911476530413)
              ·
                refine ⟨13769497231091803698905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36718659282911476530413 13769497231091803698905)
                ·
                  refine ⟨10327122923318852774179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13769497231091803698905 10327122923318852774179)
                  ·
                    rfl

theorem cell20_22626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 3, 2].length) (baseStart_22626 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_22626 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_22626 prefixEnd_22626 := by exact prefixLift 22626
  have htrace : WordTrace (prefixWord ++ tailWord_22626) baseStart_22626 baseEnd_22626 := by
    simpa [prefixWord, tailWord_22626, baseEnd_22626] using wordTrace_append hprefix tailTrace_22626
  have hstable : (prefixWord ++ tailWord_22626).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22626).length < 2 ^ (prefixWord ++ tailWord_22626).sum := by decide
  have hdescent : baseEnd_22626 < baseStart_22626 := by decide
  rcases family_descends (prefixWord ++ tailWord_22626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22661 : List Nat := [1, 3, 1, 1, 5, 3, 2, 1, 3]
def baseStart_22661 : Nat := 118140960795 + 22661 * 2 ^ 59
def prefixEnd_22661 : Nat := 4983230072969 + 3 ^ 40 * 22661 * 2
def baseEnd_22661 : Nat := 10343097877014286607369

theorem tailTrace_22661 : CollatzResearch.WordTrace tailWord_22661 prefixEnd_22661 10343097877014286607369 := by
  unfold tailWord_22661
  simp only [CollatzResearch.WordTrace]
  refine ⟨826514570910542035787837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 551009713940361357191891 826514570910542035787837)
  ·
    refine ⟨309942964091453263420439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 826514570910542035787837 309942964091453263420439)
    ·
      refine ⟨464914446137179895130659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309942964091453263420439 464914446137179895130659)
      ·
        refine ⟨697371669205769842695989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 464914446137179895130659 697371669205769842695989)
        ·
          refine ⟨65378593988040922752749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 697371669205769842695989 65378593988040922752749)
          ·
            refine ⟨24516972745515346032281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65378593988040922752749 24516972745515346032281)
            ·
              refine ⟨18387729559136509524211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24516972745515346032281 18387729559136509524211)
              ·
                refine ⟨27581594338704764286317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18387729559136509524211 27581594338704764286317)
                ·
                  refine ⟨10343097877014286607369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27581594338704764286317 10343097877014286607369)
                  ·
                    rfl

theorem cell20_22661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 2, 1, 3].length) (baseStart_22661 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_22661 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_22661 prefixEnd_22661 := by exact prefixLift 22661
  have htrace : WordTrace (prefixWord ++ tailWord_22661) baseStart_22661 baseEnd_22661 := by
    simpa [prefixWord, tailWord_22661, baseEnd_22661] using wordTrace_append hprefix tailTrace_22661
  have hstable : (prefixWord ++ tailWord_22661).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22661).length < 2 ^ (prefixWord ++ tailWord_22661).sum := by decide
  have hdescent : baseEnd_22661 < baseStart_22661 := by decide
  rcases family_descends (prefixWord ++ tailWord_22661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22665 : List Nat := [1, 2, 1, 1, 4, 2, 3, 3, 3]
def baseStart_22665 : Nat := 118140960795 + 22665 * 2 ^ 59
def prefixEnd_22665 : Nat := 4983230072969 + 3 ^ 40 * 22665 * 2
def baseEnd_22665 : Nat := 10344923586008050474019

theorem tailTrace_22665 : CollatzResearch.WordTrace tailWord_22665 prefixEnd_22665 10344923586008050474019 := by
  unfold tailWord_22665
  simp only [CollatzResearch.WordTrace]
  refine ⟨826660462896050718933449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 551106975264033812622299 826660462896050718933449)
  ·
    refine ⟨619995347172038039200087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 826660462896050718933449 619995347172038039200087)
    ·
      refine ⟨929993020758057058800131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 619995347172038039200087 929993020758057058800131)
      ·
        refine ⟨1394989531137085588200197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 929993020758057058800131 1394989531137085588200197)
        ·
          refine ⟨261560537088203547787537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1394989531137085588200197 261560537088203547787537)
          ·
            refine ⟨196170402816152660840653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 261560537088203547787537 196170402816152660840653)
            ·
              refine ⟨73563901056057247815245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 196170402816152660840653 73563901056057247815245)
              ·
                refine ⟨27586462896021467930717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73563901056057247815245 27586462896021467930717)
                ·
                  refine ⟨10344923586008050474019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27586462896021467930717 10344923586008050474019)
                  ·
                    rfl

theorem cell20_22665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 3, 3].length) (baseStart_22665 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_22665 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_22665 prefixEnd_22665 := by exact prefixLift 22665
  have htrace : WordTrace (prefixWord ++ tailWord_22665) baseStart_22665 baseEnd_22665 := by
    simpa [prefixWord, tailWord_22665, baseEnd_22665] using wordTrace_append hprefix tailTrace_22665
  have hstable : (prefixWord ++ tailWord_22665).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22665).length < 2 ^ (prefixWord ++ tailWord_22665).sum := by decide
  have hdescent : baseEnd_22665 < baseStart_22665 := by decide
  rcases family_descends (prefixWord ++ tailWord_22665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22702 : List Nat := [4, 1, 4, 2, 1, 1, 1, 4, 2]
def baseStart_22702 : Nat := 118140960795 + 22702 * 2 ^ 59
def prefixEnd_22702 : Nat := 4983230072969 + 3 ^ 40 * 22702 * 2
def baseEnd_22702 : Nat := 10361811394200366240535

theorem tailTrace_22702 : CollatzResearch.WordTrace tailWord_22702 prefixEnd_22702 10361811394200366240535 := by
  unfold tailWord_22702
  simp only [CollatzResearch.WordTrace]
  refine ⟨103501245470250754753795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 552006642508004025353573 103501245470250754753795)
  ·
    refine ⟨155251868205376132130693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103501245470250754753795 155251868205376132130693)
    ·
      refine ⟨29109725288508024774505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 155251868205376132130693 29109725288508024774505)
      ·
        refine ⟨21832293966381018580879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29109725288508024774505 21832293966381018580879)
        ·
          refine ⟨32748440949571527871319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21832293966381018580879 32748440949571527871319)
          ·
            refine ⟨49122661424357291806979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32748440949571527871319 49122661424357291806979)
            ·
              refine ⟨73683992136535937710469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49122661424357291806979 73683992136535937710469)
              ·
                refine ⟨13815748525600488320713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73683992136535937710469 13815748525600488320713)
                ·
                  refine ⟨10361811394200366240535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13815748525600488320713 10361811394200366240535)
                  ·
                    rfl

theorem cell20_22702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 4, 2].length) (baseStart_22702 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_22702 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_22702 prefixEnd_22702 := by exact prefixLift 22702
  have htrace : WordTrace (prefixWord ++ tailWord_22702) baseStart_22702 baseEnd_22702 := by
    simpa [prefixWord, tailWord_22702, baseEnd_22702] using wordTrace_append hprefix tailTrace_22702
  have hstable : (prefixWord ++ tailWord_22702).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22702).length < 2 ^ (prefixWord ++ tailWord_22702).sum := by decide
  have hdescent : baseEnd_22702 < baseStart_22702 := by decide
  rcases family_descends (prefixWord ++ tailWord_22702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22744 : List Nat := [2, 1, 2, 2, 4, 2, 2, 3, 2]
def baseStart_22744 : Nat := 118140960795 + 22744 * 2 ^ 59
def prefixEnd_22744 : Nat := 4983230072969 + 3 ^ 40 * 22744 * 2
def baseEnd_22744 : Nat := 10380981338634886840363

theorem tailTrace_22744 : CollatzResearch.WordTrace tailWord_22744 prefixEnd_22744 10380981338634886840363 := by
  unfold tailWord_22744
  simp only [CollatzResearch.WordTrace]
  refine ⟨414770914804923605529643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 553027886406564807372857 414770914804923605529643)
  ·
    refine ⟨622156372207385408294465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 414770914804923605529643 622156372207385408294465)
    ·
      refine ⟨466617279155539056220849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 622156372207385408294465 466617279155539056220849)
      ·
        refine ⟨349962959366654292165637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 466617279155539056220849 349962959366654292165637)
        ·
          refine ⟨65618054881247679781057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 349962959366654292165637 65618054881247679781057)
          ·
            refine ⟨49213541160935759835793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65618054881247679781057 49213541160935759835793)
            ·
              refine ⟨36910155870701819876845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49213541160935759835793 36910155870701819876845)
              ·
                refine ⟨13841308451513182453817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36910155870701819876845 13841308451513182453817)
                ·
                  refine ⟨10380981338634886840363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13841308451513182453817 10380981338634886840363)
                  ·
                    rfl

theorem cell20_22744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 3, 2].length) (baseStart_22744 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_22744 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_22744 prefixEnd_22744 := by exact prefixLift 22744
  have htrace : WordTrace (prefixWord ++ tailWord_22744) baseStart_22744 baseEnd_22744 := by
    simpa [prefixWord, tailWord_22744, baseEnd_22744] using wordTrace_append hprefix tailTrace_22744
  have hstable : (prefixWord ++ tailWord_22744).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22744).length < 2 ^ (prefixWord ++ tailWord_22744).sum := by decide
  have hdescent : baseEnd_22744 < baseStart_22744 := by decide
  rcases family_descends (prefixWord ++ tailWord_22744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22754 : List Nat := [3, 3, 4, 1, 1, 1, 1, 1, 5]
def baseStart_22754 : Nat := 118140960795 + 22754 * 2 ^ 59
def prefixEnd_22754 : Nat := 4983230072969 + 3 ^ 40 * 22754 * 2
def baseEnd_22754 : Nat := 10385545611119296506989

theorem tailTrace_22754 : CollatzResearch.WordTrace tailWord_22754 prefixEnd_22754 10385545611119296506989 := by
  unfold tailWord_22754
  simp only [CollatzResearch.WordTrace]
  refine ⟨207476639893404729730829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 553271039715745945948877 207476639893404729730829)
  ·
    refine ⟨77803739960026773649061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207476639893404729730829 77803739960026773649061)
    ·
      refine ⟨14588201242505020059199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77803739960026773649061 14588201242505020059199)
      ·
        refine ⟨21882301863757530088799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14588201242505020059199 21882301863757530088799)
        ·
          refine ⟨32823452795636295133199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21882301863757530088799 32823452795636295133199)
          ·
            refine ⟨49235179193454442699799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32823452795636295133199 49235179193454442699799)
            ·
              refine ⟨73852768790181664049699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49235179193454442699799 73852768790181664049699)
              ·
                refine ⟨110779153185272496074549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73852768790181664049699 110779153185272496074549)
                ·
                  refine ⟨10385545611119296506989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 110779153185272496074549 10385545611119296506989)
                  ·
                    rfl

theorem cell20_22754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 1, 5].length) (baseStart_22754 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_22754 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_22754 prefixEnd_22754 := by exact prefixLift 22754
  have htrace : WordTrace (prefixWord ++ tailWord_22754) baseStart_22754 baseEnd_22754 := by
    simpa [prefixWord, tailWord_22754, baseEnd_22754] using wordTrace_append hprefix tailTrace_22754
  have hstable : (prefixWord ++ tailWord_22754).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22754).length < 2 ^ (prefixWord ++ tailWord_22754).sum := by decide
  have hdescent : baseEnd_22754 < baseStart_22754 := by decide
  rcases family_descends (prefixWord ++ tailWord_22754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22793 : List Nat := [1, 2, 1, 1, 3, 5, 1, 6]
def baseStart_22793 : Nat := 118140960795 + 22793 * 2 ^ 59
def prefixEnd_22793 : Nat := 4983230072969 + 3 ^ 40 * 22793 * 2
def baseEnd_22793 : Nat := 3467782091269498068943

theorem tailTrace_22793 : CollatzResearch.WordTrace tailWord_22793 prefixEnd_22793 3467782091269498068943 := by
  unfold tailWord_22793
  simp only [CollatzResearch.WordTrace]
  refine ⟨831329006432328579593033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 554219337621552386395355 831329006432328579593033)
  ·
    refine ⟨623496754824246434694775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 831329006432328579593033 623496754824246434694775)
    ·
      refine ⟨935245132236369652042163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 623496754824246434694775 935245132236369652042163)
      ·
        refine ⟨1402867698354554478063245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 935245132236369652042163 1402867698354554478063245)
        ·
          refine ⟨526075386882957929273717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1402867698354554478063245 526075386882957929273717)
          ·
            refine ⟨49319567520277305869411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 526075386882957929273717 49319567520277305869411)
            ·
              refine ⟨73979351280415958804117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49319567520277305869411 73979351280415958804117)
              ·
                refine ⟨3467782091269498068943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 73979351280415958804117 3467782091269498068943)
                ·
                  rfl

theorem cell20_22793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 6].length) (baseStart_22793 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_22793 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_22793 prefixEnd_22793 := by exact prefixLift 22793
  have htrace : WordTrace (prefixWord ++ tailWord_22793) baseStart_22793 baseEnd_22793 := by
    simpa [prefixWord, tailWord_22793, baseEnd_22793] using wordTrace_append hprefix tailTrace_22793
  have hstable : (prefixWord ++ tailWord_22793).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22793).length < 2 ^ (prefixWord ++ tailWord_22793).sum := by decide
  have hdescent : baseEnd_22793 < baseStart_22793 := by decide
  rcases family_descends (prefixWord ++ tailWord_22793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22810 : List Nat := [3, 1, 1, 3, 4, 2, 6]
def baseStart_22810 : Nat := 118140960795 + 22810 * 2 ^ 59
def prefixEnd_22810 : Nat := 4983230072969 + 3 ^ 40 * 22810 * 2
def baseEnd_22810 : Nat := 1156789504114665626677

theorem tailTrace_22810 : CollatzResearch.WordTrace tailWord_22810 prefixEnd_22810 1156789504114665626677 := by
  unfold tailWord_22810
  simp only [CollatzResearch.WordTrace]
  refine ⟨207987261842685120740471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 554632698247160321974589 207987261842685120740471)
  ·
    refine ⟨311980892764027681110707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207987261842685120740471 311980892764027681110707)
    ·
      refine ⟨467971339146041521666061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311980892764027681110707 467971339146041521666061)
      ·
        refine ⟨175489252179765570624773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 467971339146041521666061 175489252179765570624773)
        ·
          refine ⟨32904234783706044492145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 175489252179765570624773 32904234783706044492145)
          ·
            refine ⟨24678176087779533369109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32904234783706044492145 24678176087779533369109)
            ·
              refine ⟨1156789504114665626677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 24678176087779533369109 1156789504114665626677)
              ·
                rfl

theorem cell20_22810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 6].length) (baseStart_22810 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_22810 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_22810 prefixEnd_22810 := by exact prefixLift 22810
  have htrace : WordTrace (prefixWord ++ tailWord_22810) baseStart_22810 baseEnd_22810 := by
    simpa [prefixWord, tailWord_22810, baseEnd_22810] using wordTrace_append hprefix tailTrace_22810
  have hstable : (prefixWord ++ tailWord_22810).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22810).length < 2 ^ (prefixWord ++ tailWord_22810).sum := by decide
  have hdescent : baseEnd_22810 < baseStart_22810 := by decide
  rcases family_descends (prefixWord ++ tailWord_22810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22834 : List Nat := [3, 2, 1, 1, 5, 1, 1, 3, 3]
def baseStart_22834 : Nat := 118140960795 + 22834 * 2 ^ 59
def prefixEnd_22834 : Nat := 4983230072969 + 3 ^ 40 * 22834 * 2
def baseEnd_22834 : Nat := 10422059790994573839995

theorem tailTrace_22834 : CollatzResearch.WordTrace tailWord_22834 prefixEnd_22834 10422059790994573839995 := by
  unfold tailWord_22834
  simp only [CollatzResearch.WordTrace]
  refine ⟨208206099820948145458889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 555216266189195054557037 208206099820948145458889)
  ·
    refine ⟨156154574865711109094167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208206099820948145458889 156154574865711109094167)
    ·
      refine ⟨234231862298566663641251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156154574865711109094167 234231862298566663641251)
      ·
        refine ⟨351347793447849995461877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234231862298566663641251 351347793447849995461877)
        ·
          refine ⟨32938855635735937074551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 351347793447849995461877 32938855635735937074551)
          ·
            refine ⟨49408283453603905611827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32938855635735937074551 49408283453603905611827)
            ·
              refine ⟨74112425180405858417741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49408283453603905611827 74112425180405858417741)
              ·
                refine ⟨27792159442652196906653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74112425180405858417741 27792159442652196906653)
                ·
                  refine ⟨10422059790994573839995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27792159442652196906653 10422059790994573839995)
                  ·
                    rfl

theorem cell20_22834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 3, 3].length) (baseStart_22834 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_22834 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_22834 prefixEnd_22834 := by exact prefixLift 22834
  have htrace : WordTrace (prefixWord ++ tailWord_22834) baseStart_22834 baseEnd_22834 := by
    simpa [prefixWord, tailWord_22834, baseEnd_22834] using wordTrace_append hprefix tailTrace_22834
  have hstable : (prefixWord ++ tailWord_22834).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22834).length < 2 ^ (prefixWord ++ tailWord_22834).sum := by decide
  have hdescent : baseEnd_22834 < baseStart_22834 := by decide
  rcases family_descends (prefixWord ++ tailWord_22834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22869 : List Nat := [1, 3, 2, 2, 4, 8]
def baseStart_22869 : Nat := 118140960795 + 22869 * 2 ^ 59
def prefixEnd_22869 : Nat := 4983230072969 + 3 ^ 40 * 22869 * 2
def baseEnd_22869 : Nat := 386593879432963247155

theorem tailTrace_22869 : CollatzResearch.WordTrace tailWord_22869 prefixEnd_22869 386593879432963247155 := by
  unfold tailWord_22869
  simp only [CollatzResearch.WordTrace]
  refine ⟨834100954156993559359661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 556067302771329039573107 834100954156993559359661)
  ·
    refine ⟨312787857808872584759873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 834100954156993559359661 312787857808872584759873)
    ·
      refine ⟨234590893356654438569905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 312787857808872584759873 234590893356654438569905)
      ·
        refine ⟨175943170017490828927429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 234590893356654438569905 175943170017490828927429)
        ·
          refine ⟨32989344378279530423893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 175943170017490828927429 32989344378279530423893)
          ·
            refine ⟨386593879432963247155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 32989344378279530423893 386593879432963247155)
            ·
              rfl

theorem cell20_22869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 8].length) (baseStart_22869 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_22869 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_22869 prefixEnd_22869 := by exact prefixLift 22869
  have htrace : WordTrace (prefixWord ++ tailWord_22869) baseStart_22869 baseEnd_22869 := by
    simpa [prefixWord, tailWord_22869, baseEnd_22869] using wordTrace_append hprefix tailTrace_22869
  have hstable : (prefixWord ++ tailWord_22869).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22869).length < 2 ^ (prefixWord ++ tailWord_22869).sum := by decide
  have hdescent : baseEnd_22869 < baseStart_22869 := by decide
  rcases family_descends (prefixWord ++ tailWord_22869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22878 : List Nat := [4, 4, 2, 1, 1, 2, 1, 5]
def baseStart_22878 : Nat := 118140960795 + 22878 * 2 ^ 59
def prefixEnd_22878 : Nat := 4983230072969 + 3 ^ 40 * 22878 * 2
def baseEnd_22878 : Nat := 3480714196641992124383

theorem tailTrace_22878 : CollatzResearch.WordTrace tailWord_22878 prefixEnd_22878 3480714196641992124383 := by
  unfold tailWord_22878
  simp only [CollatzResearch.WordTrace]
  refine ⟨104303651390548512054661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 556286140749592064291525 104303651390548512054661)
  ·
    refine ⟨19556934635727846010249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104303651390548512054661 19556934635727846010249)
    ·
      refine ⟨14667700976795884507687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19556934635727846010249 14667700976795884507687)
      ·
        refine ⟨22001551465193826761531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14667700976795884507687 22001551465193826761531)
        ·
          refine ⟨33002327197790740142297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22001551465193826761531 33002327197790740142297)
          ·
            refine ⟨24751745398343055106723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33002327197790740142297 24751745398343055106723)
            ·
              refine ⟨37127618097514582660085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24751745398343055106723 37127618097514582660085)
              ·
                refine ⟨3480714196641992124383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37127618097514582660085 3480714196641992124383)
                ·
                  rfl

theorem cell20_22878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 5].length) (baseStart_22878 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_22878 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_22878 prefixEnd_22878 := by exact prefixLift 22878
  have htrace : WordTrace (prefixWord ++ tailWord_22878) baseStart_22878 baseEnd_22878 := by
    simpa [prefixWord, tailWord_22878, baseEnd_22878] using wordTrace_append hprefix tailTrace_22878
  have hstable : (prefixWord ++ tailWord_22878).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22878).length < 2 ^ (prefixWord ++ tailWord_22878).sum := by decide
  have hdescent : baseEnd_22878 < baseStart_22878 := by decide
  rcases family_descends (prefixWord ++ tailWord_22878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22893 : List Nat := [1, 5, 1, 1, 1, 2, 1, 5, 3]
def baseStart_22893 : Nat := 118140960795 + 22893 * 2 ^ 59
def prefixEnd_22893 : Nat := 4983230072969 + 3 ^ 40 * 22893 * 2
def baseEnd_22893 : Nat := 10448988998652590873087

theorem tailTrace_22893 : CollatzResearch.WordTrace tailWord_22893 prefixEnd_22893 10448988998652590873087 := by
  unfold tailWord_22893
  simp only [CollatzResearch.WordTrace]
  refine ⟨834976306070045658233333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 556650870713363772155555 834976306070045658233333)
  ·
    refine ⟨78279028694066780459375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 834976306070045658233333 78279028694066780459375)
    ·
      refine ⟨117418543041100170689063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78279028694066780459375 117418543041100170689063)
      ·
        refine ⟨176127814561650256033595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117418543041100170689063 176127814561650256033595)
        ·
          refine ⟨264191721842475384050393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176127814561650256033595 264191721842475384050393)
          ·
            refine ⟨198143791381856538037795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 264191721842475384050393 198143791381856538037795)
            ·
              refine ⟨297215687072784807056693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 198143791381856538037795 297215687072784807056693)
              ·
                refine ⟨27863970663073575661565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 297215687072784807056693 27863970663073575661565)
                ·
                  refine ⟨10448988998652590873087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27863970663073575661565 10448988998652590873087)
                  ·
                    rfl

theorem cell20_22893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_22893 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_22893 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_22893 prefixEnd_22893 := by exact prefixLift 22893
  have htrace : WordTrace (prefixWord ++ tailWord_22893) baseStart_22893 baseEnd_22893 := by
    simpa [prefixWord, tailWord_22893, baseEnd_22893] using wordTrace_append hprefix tailTrace_22893
  have hstable : (prefixWord ++ tailWord_22893).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22893).length < 2 ^ (prefixWord ++ tailWord_22893).sum := by decide
  have hdescent : baseEnd_22893 < baseStart_22893 := by decide
  rcases family_descends (prefixWord ++ tailWord_22893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22938 : List Nat := [3, 1, 1, 4, 1, 2, 1, 3, 4]
def baseStart_22938 : Nat := 118140960795 + 22938 * 2 ^ 59
def prefixEnd_22938 : Nat := 4983230072969 + 3 ^ 40 * 22938 * 2
def baseEnd_22938 : Nat := 10469528224832434372903

theorem tailTrace_22938 : CollatzResearch.WordTrace tailWord_22938 prefixEnd_22938 10469528224832434372903 := by
  unfold tailWord_22938
  simp only [CollatzResearch.WordTrace]
  refine ⟨209154397726754585905367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 557745060604678895747645 209154397726754585905367)
  ·
    refine ⟨313731596590131878858051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209154397726754585905367 313731596590131878858051)
    ·
      refine ⟨470597394885197818287077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313731596590131878858051 470597394885197818287077)
      ·
        refine ⟨88237011540974590928827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 470597394885197818287077 88237011540974590928827)
        ·
          refine ⟨132355517311461886393241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88237011540974590928827 132355517311461886393241)
          ·
            refine ⟨99266637983596414794931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132355517311461886393241 99266637983596414794931)
            ·
              refine ⟨148899956975394622192397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99266637983596414794931 148899956975394622192397)
              ·
                refine ⟨55837483865772983322149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 148899956975394622192397 55837483865772983322149)
                ·
                  refine ⟨10469528224832434372903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55837483865772983322149 10469528224832434372903)
                  ·
                    rfl

theorem cell20_22938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 3, 4].length) (baseStart_22938 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_22938 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_22938 prefixEnd_22938 := by exact prefixLift 22938
  have htrace : WordTrace (prefixWord ++ tailWord_22938) baseStart_22938 baseEnd_22938 := by
    simpa [prefixWord, tailWord_22938, baseEnd_22938] using wordTrace_append hprefix tailTrace_22938
  have hstable : (prefixWord ++ tailWord_22938).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22938).length < 2 ^ (prefixWord ++ tailWord_22938).sum := by decide
  have hdescent : baseEnd_22938 < baseStart_22938 := by decide
  rcases family_descends (prefixWord ++ tailWord_22938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22954 : List Nat := [3, 1, 6, 1, 2, 1, 2, 4]
def baseStart_22954 : Nat := 118140960795 + 22954 * 2 ^ 59
def prefixEnd_22954 : Nat := 4983230072969 + 3 ^ 40 * 22954 * 2
def baseEnd_22954 : Nat := 3492277020269163279835

theorem tailTrace_22954 : CollatzResearch.WordTrace tailWord_22954 prefixEnd_22954 3492277020269163279835 := by
  unfold tailWord_22954
  simp only [CollatzResearch.WordTrace]
  refine ⟨209300289712263269050979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 558134105899368717469277 209300289712263269050979)
  ·
    refine ⟨313950434568394903576469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209300289712263269050979 313950434568394903576469)
    ·
      refine ⟨14716426620393511105147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 313950434568394903576469 14716426620393511105147)
      ·
        refine ⟨22074639930590266657721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14716426620393511105147 22074639930590266657721)
        ·
          refine ⟨16555979947942699993291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22074639930590266657721 16555979947942699993291)
          ·
            refine ⟨24833969921914049989937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16555979947942699993291 24833969921914049989937)
            ·
              refine ⟨18625477441435537492453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24833969921914049989937 18625477441435537492453)
              ·
                refine ⟨3492277020269163279835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18625477441435537492453 3492277020269163279835)
                ·
                  rfl

theorem cell20_22954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 2, 4].length) (baseStart_22954 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_22954 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_22954 prefixEnd_22954 := by exact prefixLift 22954
  have htrace : WordTrace (prefixWord ++ tailWord_22954) baseStart_22954 baseEnd_22954 := by
    simpa [prefixWord, tailWord_22954, baseEnd_22954] using wordTrace_append hprefix tailTrace_22954
  have hstable : (prefixWord ++ tailWord_22954).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22954).length < 2 ^ (prefixWord ++ tailWord_22954).sum := by decide
  have hdescent : baseEnd_22954 < baseStart_22954 := by decide
  rcases family_descends (prefixWord ++ tailWord_22954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22972 : List Nat := [2, 2, 2, 4, 1, 1, 3, 3, 2]
def baseStart_22972 : Nat := 118140960795 + 22972 * 2 ^ 59
def prefixEnd_22972 : Nat := 4983230072969 + 3 ^ 40 * 22972 * 2
def baseEnd_22972 : Nat := 10485046751279427239431

theorem tailTrace_22972 : CollatzResearch.WordTrace tailWord_22972 prefixEnd_22972 10485046751279427239431 := by
  unfold tailWord_22972
  simp only [CollatzResearch.WordTrace]
  refine ⟨418928836391921075179585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 558571781855894766906113 418928836391921075179585)
  ·
    refine ⟨314196627293940806384689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 418928836391921075179585 314196627293940806384689)
    ·
      refine ⟨235647470470455604788517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 314196627293940806384689 235647470470455604788517)
      ·
        refine ⟨44183900713210425897847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 235647470470455604788517 44183900713210425897847)
        ·
          refine ⟨66275851069815638846771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44183900713210425897847 66275851069815638846771)
          ·
            refine ⟨99413776604723458270157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66275851069815638846771 99413776604723458270157)
            ·
              refine ⟨37280166226771296851309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99413776604723458270157 37280166226771296851309)
              ·
                refine ⟨13980062335039236319241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37280166226771296851309 13980062335039236319241)
                ·
                  refine ⟨10485046751279427239431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13980062335039236319241 10485046751279427239431)
                  ·
                    rfl

theorem cell20_22972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 3, 2].length) (baseStart_22972 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_22972 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_22972 prefixEnd_22972 := by exact prefixLift 22972
  have htrace : WordTrace (prefixWord ++ tailWord_22972) baseStart_22972 baseEnd_22972 := by
    simpa [prefixWord, tailWord_22972, baseEnd_22972] using wordTrace_append hprefix tailTrace_22972
  have hstable : (prefixWord ++ tailWord_22972).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22972).length < 2 ^ (prefixWord ++ tailWord_22972).sum := by decide
  have hdescent : baseEnd_22972 < baseStart_22972 := by decide
  rcases family_descends (prefixWord ++ tailWord_22972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22983 : List Nat := [1, 1, 4, 1, 1, 6, 6]
def baseStart_22983 : Nat := 118140960795 + 22983 * 2 ^ 59
def prefixEnd_22983 : Nat := 4983230072969 + 3 ^ 40 * 22983 * 2
def baseEnd_22983 : Nat := 1165563050112475319191

theorem tailTrace_22983 : CollatzResearch.WordTrace tailWord_22983 prefixEnd_22983 1165563050112475319191 := by
  unfold tailWord_22983
  simp only [CollatzResearch.WordTrace]
  refine ⟨838258875743991029009603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 558839250495994019339735 838258875743991029009603)
  ·
    refine ⟨1257388313615986543514405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 838258875743991029009603 1257388313615986543514405)
    ·
      refine ⟨235760308802997476908951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1257388313615986543514405 235760308802997476908951)
      ·
        refine ⟨353640463204496215363427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235760308802997476908951 353640463204496215363427)
        ·
          refine ⟨530460694806744323045141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 353640463204496215363427 530460694806744323045141)
          ·
            refine ⟨24865345069066140142741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 530460694806744323045141 24865345069066140142741)
            ·
              refine ⟨1165563050112475319191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 24865345069066140142741 1165563050112475319191)
              ·
                rfl

theorem cell20_22983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 6].length) (baseStart_22983 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_22983 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_22983 prefixEnd_22983 := by exact prefixLift 22983
  have htrace : WordTrace (prefixWord ++ tailWord_22983) baseStart_22983 baseEnd_22983 := by
    simpa [prefixWord, tailWord_22983, baseEnd_22983] using wordTrace_append hprefix tailTrace_22983
  have hstable : (prefixWord ++ tailWord_22983).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22983).length < 2 ^ (prefixWord ++ tailWord_22983).sum := by decide
  have hdescent : baseEnd_22983 < baseStart_22983 := by decide
  rcases family_descends (prefixWord ++ tailWord_22983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23007 : List Nat := [1, 1, 2, 3, 3, 3, 1, 3, 3]
def baseStart_23007 : Nat := 118140960795 + 23007 * 2 ^ 59
def prefixEnd_23007 : Nat := 4983230072969 + 3 ^ 40 * 23007 * 2
def baseEnd_23007 : Nat := 10501021704974861072621

theorem tailTrace_23007 : CollatzResearch.WordTrace tailWord_23007 prefixEnd_23007 10501021704974861072621 := by
  unfold tailWord_23007
  simp only [CollatzResearch.WordTrace]
  refine ⟨839134227657043127883275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 559422818438028751922183 839134227657043127883275)
  ·
    refine ⟨1258701341485564691824913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 839134227657043127883275 1258701341485564691824913)
    ·
      refine ⟨944026006114173518868685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1258701341485564691824913 944026006114173518868685)
      ·
        refine ⟨354009752292815069575757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 944026006114173518868685 354009752292815069575757)
        ·
          refine ⟨132753657109805651090909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 354009752292815069575757 132753657109805651090909)
          ·
            refine ⟨49782621416177119159091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 132753657109805651090909 49782621416177119159091)
            ·
              refine ⟨74673932124265678738637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49782621416177119159091 74673932124265678738637)
              ·
                refine ⟨28002724546599629526989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74673932124265678738637 28002724546599629526989)
                ·
                  refine ⟨10501021704974861072621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28002724546599629526989 10501021704974861072621)
                  ·
                    rfl

theorem cell20_23007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 3, 3].length) (baseStart_23007 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_23007 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_23007 prefixEnd_23007 := by exact prefixLift 23007
  have htrace : WordTrace (prefixWord ++ tailWord_23007) baseStart_23007 baseEnd_23007 := by
    simpa [prefixWord, tailWord_23007, baseEnd_23007] using wordTrace_append hprefix tailTrace_23007
  have hstable : (prefixWord ++ tailWord_23007).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23007).length < 2 ^ (prefixWord ++ tailWord_23007).sum := by decide
  have hdescent : baseEnd_23007 < baseStart_23007 := by decide
  rcases family_descends (prefixWord ++ tailWord_23007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23100 : List Nat := [2, 2, 2, 2, 3, 3, 1, 2, 3]
def baseStart_23100 : Nat := 118140960795 + 23100 * 2 ^ 59
def prefixEnd_23100 : Nat := 4983230072969 + 3 ^ 40 * 23100 * 2
def baseEnd_23100 : Nat := 10543469439079870972241

theorem tailTrace_23100 : CollatzResearch.WordTrace tailWord_23100 prefixEnd_23100 10543469439079870972241 := by
  unfold tailWord_23100
  simp only [CollatzResearch.WordTrace]
  refine ⟨421263108160060005509377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 561684144213413340679169 421263108160060005509377)
  ·
    refine ⟨315947331120045004132033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 421263108160060005509377 315947331120045004132033)
    ·
      refine ⟨236960498340033753099025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 315947331120045004132033 236960498340033753099025)
      ·
        refine ⟨177720373755025314824269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 236960498340033753099025 177720373755025314824269)
        ·
          refine ⟨66645140158134493059101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 177720373755025314824269 66645140158134493059101)
          ·
            refine ⟨24991927559300434897163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66645140158134493059101 24991927559300434897163)
            ·
              refine ⟨37487891338950652345745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24991927559300434897163 37487891338950652345745)
              ·
                refine ⟨28115918504212989259309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37487891338950652345745 28115918504212989259309)
                ·
                  refine ⟨10543469439079870972241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28115918504212989259309 10543469439079870972241)
                  ·
                    rfl

theorem cell20_23100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 2, 3].length) (baseStart_23100 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_23100 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_23100 prefixEnd_23100 := by exact prefixLift 23100
  have htrace : WordTrace (prefixWord ++ tailWord_23100) baseStart_23100 baseEnd_23100 := by
    simpa [prefixWord, tailWord_23100, baseEnd_23100] using wordTrace_append hprefix tailTrace_23100
  have hstable : (prefixWord ++ tailWord_23100).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23100).length < 2 ^ (prefixWord ++ tailWord_23100).sum := by decide
  have hdescent : baseEnd_23100 < baseStart_23100 := by decide
  rcases family_descends (prefixWord ++ tailWord_23100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23117 : List Nat := [1, 6, 1, 1, 2, 2, 3, 1, 3]
def baseStart_23117 : Nat := 118140960795 + 23117 * 2 ^ 59
def prefixEnd_23117 : Nat := 4983230072969 + 3 ^ 40 * 23117 * 2
def baseEnd_23117 : Nat := 10551228702303367405505

theorem tailTrace_23117 : CollatzResearch.WordTrace tailWord_23117 prefixEnd_23117 10551228702303367405505 := by
  unfold tailWord_23117
  simp only [CollatzResearch.WordTrace]
  refine ⟨843146257258531914387605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 562097504839021276258403 843146257258531914387605)
  ·
    refine ⟨39522480808993683486919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 843146257258531914387605 39522480808993683486919)
    ·
      refine ⟨59283721213490525230379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39522480808993683486919 59283721213490525230379)
      ·
        refine ⟨88925581820235787845569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59283721213490525230379 88925581820235787845569)
        ·
          refine ⟨66694186365176840884177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88925581820235787845569 66694186365176840884177)
          ·
            refine ⟨50020639773882630663133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66694186365176840884177 50020639773882630663133)
            ·
              refine ⟨18757739915205986498675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50020639773882630663133 18757739915205986498675)
              ·
                refine ⟨28136609872808979748013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18757739915205986498675 28136609872808979748013)
                ·
                  refine ⟨10551228702303367405505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28136609872808979748013 10551228702303367405505)
                  ·
                    rfl

theorem cell20_23117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_23117 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_23117 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_23117 prefixEnd_23117 := by exact prefixLift 23117
  have htrace : WordTrace (prefixWord ++ tailWord_23117) baseStart_23117 baseEnd_23117 := by
    simpa [prefixWord, tailWord_23117, baseEnd_23117] using wordTrace_append hprefix tailTrace_23117
  have hstable : (prefixWord ++ tailWord_23117).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23117).length < 2 ^ (prefixWord ++ tailWord_23117).sum := by decide
  have hdescent : baseEnd_23117 < baseStart_23117 := by decide
  rcases family_descends (prefixWord ++ tailWord_23117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23141 : List Nat := [1, 3, 1, 3, 5, 1, 1, 3, 2]
def baseStart_23141 : Nat := 118140960795 + 23141 * 2 ^ 59
def prefixEnd_23141 : Nat := 4983230072969 + 3 ^ 40 * 23141 * 2
def baseEnd_23141 : Nat := 10562182956265950605407

theorem tailTrace_23141 : CollatzResearch.WordTrace tailWord_23141 prefixEnd_23141 10562182956265950605407 := by
  unfold tailWord_23141
  simp only [CollatzResearch.WordTrace]
  refine ⟨844021609171584013261277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 562681072781056008840851 844021609171584013261277)
  ·
    refine ⟨316508103439344004972979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 844021609171584013261277 316508103439344004972979)
    ·
      refine ⟨474762155159016007459469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316508103439344004972979 474762155159016007459469)
      ·
        refine ⟨178035808184631002797301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 474762155159016007459469 178035808184631002797301)
        ·
          refine ⟨16690857017309156512247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 178035808184631002797301 16690857017309156512247)
          ·
            refine ⟨25036285525963734768371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16690857017309156512247 25036285525963734768371)
            ·
              refine ⟨37554428288945602152557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25036285525963734768371 37554428288945602152557)
              ·
                refine ⟨14082910608354600807209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37554428288945602152557 14082910608354600807209)
                ·
                  refine ⟨10562182956265950605407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14082910608354600807209 10562182956265950605407)
                  ·
                    rfl

theorem cell20_23141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 3, 2].length) (baseStart_23141 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_23141 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_23141 prefixEnd_23141 := by exact prefixLift 23141
  have htrace : WordTrace (prefixWord ++ tailWord_23141) baseStart_23141 baseEnd_23141 := by
    simpa [prefixWord, tailWord_23141, baseEnd_23141] using wordTrace_append hprefix tailTrace_23141
  have hstable : (prefixWord ++ tailWord_23141).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23141).length < 2 ^ (prefixWord ++ tailWord_23141).sum := by decide
  have hdescent : baseEnd_23141 < baseStart_23141 := by decide
  rcases family_descends (prefixWord ++ tailWord_23141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23152 : List Nat := [2, 1, 1, 1, 8, 1, 6]
def baseStart_23152 : Nat := 118140960795 + 23152 * 2 ^ 59
def prefixEnd_23152 : Nat := 4983230072969 + 3 ^ 40 * 23152 * 2
def baseEnd_23152 : Nat := 1174133739555422359855

theorem tailTrace_23152 : CollatzResearch.WordTrace tailWord_23152 prefixEnd_23152 1174133739555422359855 := by
  unfold tailWord_23152
  simp only [CollatzResearch.WordTrace]
  refine ⟨422211406065866445955855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 562948541421155261274473 422211406065866445955855)
  ·
    refine ⟨633317109098799668933783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 422211406065866445955855 633317109098799668933783)
    ·
      refine ⟨949975663648199503400675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 633317109098799668933783 949975663648199503400675)
      ·
        refine ⟨1424963495472299255101013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 949975663648199503400675 1424963495472299255101013)
        ·
          refine ⟨16698790962566006895715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 1424963495472299255101013 16698790962566006895715)
          ·
            refine ⟨25048186443849010343573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16698790962566006895715 25048186443849010343573)
            ·
              refine ⟨1174133739555422359855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 25048186443849010343573 1174133739555422359855)
              ·
                rfl

theorem cell20_23152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 6].length) (baseStart_23152 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_23152 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_23152 prefixEnd_23152 := by exact prefixLift 23152
  have htrace : WordTrace (prefixWord ++ tailWord_23152) baseStart_23152 baseEnd_23152 := by
    simpa [prefixWord, tailWord_23152, baseEnd_23152] using wordTrace_append hprefix tailTrace_23152
  have hstable : (prefixWord ++ tailWord_23152).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23152).length < 2 ^ (prefixWord ++ tailWord_23152).sum := by decide
  have hdescent : baseEnd_23152 < baseStart_23152 := by decide
  rcases family_descends (prefixWord ++ tailWord_23152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23173 : List Nat := [1, 3, 1, 1, 4, 3, 2, 5]
def baseStart_23173 : Nat := 118140960795 + 23173 * 2 ^ 59
def prefixEnd_23173 : Nat := 4983230072969 + 3 ^ 40 * 23173 * 2
def baseEnd_23173 : Nat := 3525596209405353846203

theorem tailTrace_23173 : CollatzResearch.WordTrace tailWord_23173 prefixEnd_23173 3525596209405353846203 := by
  unfold tailWord_23173
  simp only [CollatzResearch.WordTrace]
  refine ⟨845188745055653478426173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 563459163370435652284115 845188745055653478426173)
  ·
    refine ⟨316945779395870054409815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 845188745055653478426173 316945779395870054409815)
    ·
      refine ⟨475418669093805081614723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316945779395870054409815 475418669093805081614723)
      ·
        refine ⟨713128003640707622422085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 475418669093805081614723 713128003640707622422085)
        ·
          refine ⟨133711500682632679204141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 713128003640707622422085 133711500682632679204141)
          ·
            refine ⟨50141812755987254701553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 133711500682632679204141 50141812755987254701553)
            ·
              refine ⟨37606359566990441026165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50141812755987254701553 37606359566990441026165)
              ·
                refine ⟨3525596209405353846203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37606359566990441026165 3525596209405353846203)
                ·
                  rfl

theorem cell20_23173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 5].length) (baseStart_23173 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_23173 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_23173 prefixEnd_23173 := by exact prefixLift 23173
  have htrace : WordTrace (prefixWord ++ tailWord_23173) baseStart_23173 baseEnd_23173 := by
    simpa [prefixWord, tailWord_23173, baseEnd_23173] using wordTrace_append hprefix tailTrace_23173
  have hstable : (prefixWord ++ tailWord_23173).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23173).length < 2 ^ (prefixWord ++ tailWord_23173).sum := by decide
  have hdescent : baseEnd_23173 < baseStart_23173 := by decide
  rcases family_descends (prefixWord ++ tailWord_23173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23214 : List Nat := [4, 1, 4, 1, 1, 1, 1, 4, 3]
def baseStart_23214 : Nat := 118140960795 + 23214 * 2 ^ 59
def prefixEnd_23214 : Nat := 4983230072969 + 3 ^ 40 * 23214 * 2
def baseEnd_23214 : Nat := 10595502145402141171775

theorem tailTrace_23214 : CollatzResearch.WordTrace tailWord_23214 prefixEnd_23214 10595502145402141171775 := by
  unfold tailWord_23214
  simp only [CollatzResearch.WordTrace]
  refine ⟨105835517238389685083587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 564456091938078320445797 105835517238389685083587)
  ·
    refine ⟨158753275857584527625381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105835517238389685083587 158753275857584527625381)
    ·
      refine ⟨29766239223297098929759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 158753275857584527625381 29766239223297098929759)
      ·
        refine ⟨44649358834945648394639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29766239223297098929759 44649358834945648394639)
        ·
          refine ⟨66974038252418472591959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44649358834945648394639 66974038252418472591959)
          ·
            refine ⟨100461057378627708887939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66974038252418472591959 100461057378627708887939)
            ·
              refine ⟨150691586067941563331909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100461057378627708887939 150691586067941563331909)
              ·
                refine ⟨28254672387739043124733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 150691586067941563331909 28254672387739043124733)
                ·
                  refine ⟨10595502145402141171775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28254672387739043124733 10595502145402141171775)
                  ·
                    rfl

theorem cell20_23214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 4, 3].length) (baseStart_23214 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_23214 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_23214 prefixEnd_23214 := by exact prefixLift 23214
  have htrace : WordTrace (prefixWord ++ tailWord_23214) baseStart_23214 baseEnd_23214 := by
    simpa [prefixWord, tailWord_23214, baseEnd_23214] using wordTrace_append hprefix tailTrace_23214
  have hstable : (prefixWord ++ tailWord_23214).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23214).length < 2 ^ (prefixWord ++ tailWord_23214).sum := by decide
  have hdescent : baseEnd_23214 < baseStart_23214 := by decide
  rcases family_descends (prefixWord ++ tailWord_23214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23225 : List Nat := [1, 2, 1, 4, 1, 1, 1, 5, 4]
def baseStart_23225 : Nat := 118140960795 + 23225 * 2 ^ 59
def prefixEnd_23225 : Nat := 4983230072969 + 3 ^ 40 * 23225 * 2
def baseEnd_23225 : Nat := 10600522845134991805063

theorem tailTrace_23225 : CollatzResearch.WordTrace tailWord_23225 prefixEnd_23225 10600522845134991805063 := by
  unfold tailWord_23225
  simp only [CollatzResearch.WordTrace]
  refine ⟨847085340867266359319129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 564723560578177572879419 847085340867266359319129)
  ·
    refine ⟨635314005650449769489347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 847085340867266359319129 635314005650449769489347)
    ·
      refine ⟨952971008475674654234021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 635314005650449769489347 952971008475674654234021)
      ·
        refine ⟨178682064089188997668879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 952971008475674654234021 178682064089188997668879)
        ·
          refine ⟨268023096133783496503319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178682064089188997668879 268023096133783496503319)
          ·
            refine ⟨402034644200675244754979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 268023096133783496503319 402034644200675244754979)
            ·
              refine ⟨603051966301012867132469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 402034644200675244754979 603051966301012867132469)
              ·
                refine ⟨56536121840719956293669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 603051966301012867132469 56536121840719956293669)
                ·
                  refine ⟨10600522845134991805063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56536121840719956293669 10600522845134991805063)
                  ·
                    rfl

theorem cell20_23225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 5, 4].length) (baseStart_23225 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_23225 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_23225 prefixEnd_23225 := by exact prefixLift 23225
  have htrace : WordTrace (prefixWord ++ tailWord_23225) baseStart_23225 baseEnd_23225 := by
    simpa [prefixWord, tailWord_23225, baseEnd_23225] using wordTrace_append hprefix tailTrace_23225
  have hstable : (prefixWord ++ tailWord_23225).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23225).length < 2 ^ (prefixWord ++ tailWord_23225).sum := by decide
  have hdescent : baseEnd_23225 < baseStart_23225 := by decide
  rcases family_descends (prefixWord ++ tailWord_23225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23242 : List Nat := [3, 1, 2, 1, 4, 2, 1, 2, 4]
def baseStart_23242 : Nat := 118140960795 + 23242 * 2 ^ 59
def prefixEnd_23242 : Nat := 4983230072969 + 3 ^ 40 * 23242 * 2
def baseEnd_23242 : Nat := 10608282108358488238327

theorem tailTrace_23242 : CollatzResearch.WordTrace tailWord_23242 prefixEnd_23242 10608282108358488238327 := by
  unfold tailWord_23242
  simp only [CollatzResearch.WordTrace]
  refine ⟨211926345451419565671995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 565136921203785508458653 211926345451419565671995)
  ·
    refine ⟨317889518177129348507993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211926345451419565671995 317889518177129348507993)
    ·
      refine ⟨238417138632847011380995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 317889518177129348507993 238417138632847011380995)
      ·
        refine ⟨357625707949270517071493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238417138632847011380995 357625707949270517071493)
        ·
          refine ⟨67054820240488221950905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 357625707949270517071493 67054820240488221950905)
          ·
            refine ⟨50291115180366166463179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67054820240488221950905 50291115180366166463179)
            ·
              refine ⟨75436672770549249694769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50291115180366166463179 75436672770549249694769)
              ·
                refine ⟨56577504577911937271077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75436672770549249694769 56577504577911937271077)
                ·
                  refine ⟨10608282108358488238327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56577504577911937271077 10608282108358488238327)
                  ·
                    rfl

theorem cell20_23242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 2, 4].length) (baseStart_23242 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_23242 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_23242 prefixEnd_23242 := by exact prefixLift 23242
  have htrace : WordTrace (prefixWord ++ tailWord_23242) baseStart_23242 baseEnd_23242 := by
    simpa [prefixWord, tailWord_23242, baseEnd_23242] using wordTrace_append hprefix tailTrace_23242
  have hstable : (prefixWord ++ tailWord_23242).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23242).length < 2 ^ (prefixWord ++ tailWord_23242).sum := by decide
  have hdescent : baseEnd_23242 < baseStart_23242 := by decide
  rcases family_descends (prefixWord ++ tailWord_23242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23249 : List Nat := [1, 2, 2, 1, 2, 3, 5, 4]
def baseStart_23249 : Nat := 118140960795 + 23249 * 2 ^ 59
def prefixEnd_23249 : Nat := 4983230072969 + 3 ^ 40 * 23249 * 2
def baseEnd_23249 : Nat := 3537159033032525001655

theorem tailTrace_23249 : CollatzResearch.WordTrace tailWord_23249 prefixEnd_23249 3537159033032525001655 := by
  unfold tailWord_23249
  simp only [CollatzResearch.WordTrace]
  refine ⟨847960692780318458192801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 565307128520212305461867 847960692780318458192801)
  ·
    refine ⟨635970519585238843644601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 847960692780318458192801 635970519585238843644601)
    ·
      refine ⟨476977889688929132733451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 635970519585238843644601 476977889688929132733451)
      ·
        refine ⟨715466834533393699100177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 476977889688929132733451 715466834533393699100177)
        ·
          refine ⟨536600125900045274325133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 715466834533393699100177 536600125900045274325133)
          ·
            refine ⟨201225047212516977871925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 536600125900045274325133 201225047212516977871925)
            ·
              refine ⟨18864848176173466675493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 201225047212516977871925 18864848176173466675493)
              ·
                refine ⟨3537159033032525001655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18864848176173466675493 3537159033032525001655)
                ·
                  rfl

theorem cell20_23249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 5, 4].length) (baseStart_23249 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_23249 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_23249 prefixEnd_23249 := by exact prefixLift 23249
  have htrace : WordTrace (prefixWord ++ tailWord_23249) baseStart_23249 baseEnd_23249 := by
    simpa [prefixWord, tailWord_23249, baseEnd_23249] using wordTrace_append hprefix tailTrace_23249
  have hstable : (prefixWord ++ tailWord_23249).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23249).length < 2 ^ (prefixWord ++ tailWord_23249).sum := by decide
  have hdescent : baseEnd_23249 < baseStart_23249 := by decide
  rcases family_descends (prefixWord ++ tailWord_23249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23280 : List Nat := [2, 1, 1, 1, 3, 1, 3, 6, 2]
def baseStart_23280 : Nat := 118140960795 + 23280 * 2 ^ 59
def prefixEnd_23280 : Nat := 4983230072969 + 3 ^ 40 * 23280 * 2
def baseEnd_23280 : Nat := 10625626343799244971505

theorem tailTrace_23280 : CollatzResearch.WordTrace tailWord_23280 prefixEnd_23280 10625626343799244971505 := by
  unfold tailWord_23280
  simp only [CollatzResearch.WordTrace]
  refine ⟨424545677834005376285647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 566060903778673835047529 424545677834005376285647)
  ·
    refine ⟨636818516751008064428471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 424545677834005376285647 636818516751008064428471)
    ·
      refine ⟨955227775126512096642707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 636818516751008064428471 955227775126512096642707)
      ·
        refine ⟨1432841662689768144964061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 955227775126512096642707 1432841662689768144964061)
        ·
          refine ⟨537315623508663054361523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1432841662689768144964061 537315623508663054361523)
          ·
            refine ⟨805973435262994581542285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 537315623508663054361523 805973435262994581542285)
            ·
              refine ⟨302240038223622968078357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 805973435262994581542285 302240038223622968078357)
              ·
                refine ⟨14167501791732326628673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 302240038223622968078357 14167501791732326628673)
                ·
                  refine ⟨10625626343799244971505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14167501791732326628673 10625626343799244971505)
                  ·
                    rfl

theorem cell20_23280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 6, 2].length) (baseStart_23280 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_23280 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_23280 prefixEnd_23280 := by exact prefixLift 23280
  have htrace : WordTrace (prefixWord ++ tailWord_23280) baseStart_23280 baseEnd_23280 := by
    simpa [prefixWord, tailWord_23280, baseEnd_23280] using wordTrace_append hprefix tailTrace_23280
  have hstable : (prefixWord ++ tailWord_23280).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23280).length < 2 ^ (prefixWord ++ tailWord_23280).sum := by decide
  have hdescent : baseEnd_23280 < baseStart_23280 := by decide
  rcases family_descends (prefixWord ++ tailWord_23280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23304 : List Nat := [2, 1, 3, 2, 2, 4, 2, 4]
def baseStart_23304 : Nat := 118140960795 + 23304 * 2 ^ 59
def prefixEnd_23304 : Nat := 4983230072969 + 3 ^ 40 * 23304 * 2
def baseEnd_23304 : Nat := 3545526865920609390469

theorem tailTrace_23304 : CollatzResearch.WordTrace tailWord_23304 prefixEnd_23304 3545526865920609390469 := by
  unfold tailWord_23304
  simp only [CollatzResearch.WordTrace]
  refine ⟨424983353790531425722483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 566644471720708567629977 424983353790531425722483)
  ·
    refine ⟨637475030685797138583725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 424983353790531425722483 637475030685797138583725)
    ·
      refine ⟨239053136507173926968897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 637475030685797138583725 239053136507173926968897)
      ·
        refine ⟨179289852380380445226673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239053136507173926968897 179289852380380445226673)
        ·
          refine ⟨134467389285285333920005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179289852380380445226673 134467389285285333920005)
          ·
            refine ⟨25212635490991000110001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 134467389285285333920005 25212635490991000110001)
            ·
              refine ⟨18909476618243250082501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25212635490991000110001 18909476618243250082501)
              ·
                refine ⟨3545526865920609390469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18909476618243250082501 3545526865920609390469)
                ·
                  rfl

theorem cell20_23304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 2, 4].length) (baseStart_23304 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_23304 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_23304 prefixEnd_23304 := by exact prefixLift 23304
  have htrace : WordTrace (prefixWord ++ tailWord_23304) baseStart_23304 baseEnd_23304 := by
    simpa [prefixWord, tailWord_23304, baseEnd_23304] using wordTrace_append hprefix tailTrace_23304
  have hstable : (prefixWord ++ tailWord_23304).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23304).length < 2 ^ (prefixWord ++ tailWord_23304).sum := by decide
  have hdescent : baseEnd_23304 < baseStart_23304 := by decide
  rcases family_descends (prefixWord ++ tailWord_23304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23315 : List Nat := [1, 1, 1, 2, 1, 3, 3, 1, 7]
def baseStart_23315 : Nat := 118140960795 + 23315 * 2 ^ 59
def prefixEnd_23315 : Nat := 4983230072969 + 3 ^ 40 * 23315 * 2
def baseEnd_23315 : Nat := 10641601297494678804695

theorem tailTrace_23315 : CollatzResearch.WordTrace tailWord_23315 prefixEnd_23315 10641601297494678804695 := by
  unfold tailWord_23315
  simp only [CollatzResearch.WordTrace]
  refine ⟨850367910541211730095399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 566911940360807820063599 850367910541211730095399)
  ·
    refine ⟨1275551865811817595143099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 850367910541211730095399 1275551865811817595143099)
    ·
      refine ⟨1913327798717726392714649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1275551865811817595143099 1913327798717726392714649)
      ·
        refine ⟨1434995849038294794535987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1913327798717726392714649 1434995849038294794535987)
        ·
          refine ⟨2152493773557442191803981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1434995849038294794535987 2152493773557442191803981)
          ·
            refine ⟨807185165084040821926493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2152493773557442191803981 807185165084040821926493)
            ·
              refine ⟨302694436906515308222435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 807185165084040821926493 302694436906515308222435)
              ·
                refine ⟨454041655359772962333653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 302694436906515308222435 454041655359772962333653)
                ·
                  refine ⟨10641601297494678804695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 454041655359772962333653 10641601297494678804695)
                  ·
                    rfl

theorem cell20_23315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 7].length) (baseStart_23315 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_23315 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_23315 prefixEnd_23315 := by exact prefixLift 23315
  have htrace : WordTrace (prefixWord ++ tailWord_23315) baseStart_23315 baseEnd_23315 := by
    simpa [prefixWord, tailWord_23315, baseEnd_23315] using wordTrace_append hprefix tailTrace_23315
  have hstable : (prefixWord ++ tailWord_23315).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23315).length < 2 ^ (prefixWord ++ tailWord_23315).sum := by decide
  have hdescent : baseEnd_23315 < baseStart_23315 := by decide
  rcases family_descends (prefixWord ++ tailWord_23315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23341 : List Nat := [1, 5, 3, 2, 2, 1, 2, 1, 3]
def baseStart_23341 : Nat := 118140960795 + 23341 * 2 ^ 59
def prefixEnd_23341 : Nat := 4983230072969 + 3 ^ 40 * 23341 * 2
def baseEnd_23341 : Nat := 10653468405954143937923

theorem tailTrace_23341 : CollatzResearch.WordTrace tailWord_23341 prefixEnd_23341 10653468405954143937923 := by
  unfold tailWord_23341
  simp only [CollatzResearch.WordTrace]
  refine ⟨851316208447018170541877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 567544138964678780361251 851316208447018170541877)
  ·
    refine ⟨79810894541907953488301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 851316208447018170541877 79810894541907953488301)
    ·
      refine ⟨29929085453215482558113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79810894541907953488301 29929085453215482558113)
      ·
        refine ⟨22446814089911611918585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29929085453215482558113 22446814089911611918585)
        ·
          refine ⟨16835110567433708938939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22446814089911611918585 16835110567433708938939)
          ·
            refine ⟨25252665851150563408409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16835110567433708938939 25252665851150563408409)
            ·
              refine ⟨18939499388362922556307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25252665851150563408409 18939499388362922556307)
              ·
                refine ⟨28409249082544383834461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18939499388362922556307 28409249082544383834461)
                ·
                  refine ⟨10653468405954143937923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28409249082544383834461 10653468405954143937923)
                  ·
                    rfl

theorem cell20_23341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 2, 1, 3].length) (baseStart_23341 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_23341 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_23341 prefixEnd_23341 := by exact prefixLift 23341
  have htrace : WordTrace (prefixWord ++ tailWord_23341) baseStart_23341 baseEnd_23341 := by
    simpa [prefixWord, tailWord_23341, baseEnd_23341] using wordTrace_append hprefix tailTrace_23341
  have hstable : (prefixWord ++ tailWord_23341).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23341).length < 2 ^ (prefixWord ++ tailWord_23341).sum := by decide
  have hdescent : baseEnd_23341 < baseStart_23341 := by decide
  rcases family_descends (prefixWord ++ tailWord_23341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23342 : List Nat := [4, 1, 3, 2, 1, 2, 2, 5]
def baseStart_23342 : Nat := 118140960795 + 23342 * 2 ^ 59
def prefixEnd_23342 : Nat := 4983230072969 + 3 ^ 40 * 23342 * 2
def baseEnd_23342 : Nat := 3551308277734194968195

theorem tailTrace_23342 : CollatzResearch.WordTrace tailWord_23342 prefixEnd_23342 3551308277734194968195 := by
  unfold tailWord_23342
  simp only [CollatzResearch.WordTrace]
  refine ⟨106419085180424417666035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 567568454295596894218853 106419085180424417666035)
  ·
    refine ⟨159628627770636626499053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106419085180424417666035 159628627770636626499053)
    ·
      refine ⟨59860735413988734937145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159628627770636626499053 59860735413988734937145)
      ·
        refine ⟨44895551560491551202859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59860735413988734937145 44895551560491551202859)
        ·
          refine ⟨67343327340737326804289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44895551560491551202859 67343327340737326804289)
          ·
            refine ⟨50507495505552995103217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67343327340737326804289 50507495505552995103217)
            ·
              refine ⟨37880621629164746327413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50507495505552995103217 37880621629164746327413)
              ·
                refine ⟨3551308277734194968195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37880621629164746327413 3551308277734194968195)
                ·
                  rfl

theorem cell20_23342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 5].length) (baseStart_23342 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_23342 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_23342 prefixEnd_23342 := by exact prefixLift 23342
  have htrace : WordTrace (prefixWord ++ tailWord_23342) baseStart_23342 baseEnd_23342 := by
    simpa [prefixWord, tailWord_23342, baseEnd_23342] using wordTrace_append hprefix tailTrace_23342
  have hstable : (prefixWord ++ tailWord_23342).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23342).length < 2 ^ (prefixWord ++ tailWord_23342).sum := by decide
  have hdescent : baseEnd_23342 < baseStart_23342 := by decide
  rcases family_descends (prefixWord ++ tailWord_23342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23349 : List Nat := [1, 3, 3, 1, 3, 2, 1, 3, 3]
def baseStart_23349 : Nat := 118140960795 + 23349 * 2 ^ 59
def prefixEnd_23349 : Nat := 4983230072969 + 3 ^ 40 * 23349 * 2
def baseEnd_23349 : Nat := 10657119823941671671223

theorem tailTrace_23349 : CollatzResearch.WordTrace tailWord_23349 prefixEnd_23349 10657119823941671671223 := by
  unfold tailWord_23349
  simp only [CollatzResearch.WordTrace]
  refine ⟨851607992418035536833101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 567738661612023691222067 851607992418035536833101)
  ·
    refine ⟨319352997156763326312413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 851607992418035536833101 319352997156763326312413)
    ·
      refine ⟨119757373933786247367155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 319352997156763326312413 119757373933786247367155)
      ·
        refine ⟨179636060900679371050733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119757373933786247367155 179636060900679371050733)
        ·
          refine ⟨67363522837754764144025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 179636060900679371050733 67363522837754764144025)
          ·
            refine ⟨50522642128316073108019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67363522837754764144025 50522642128316073108019)
            ·
              refine ⟨75783963192474109662029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50522642128316073108019 75783963192474109662029)
              ·
                refine ⟨28418986197177791123261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75783963192474109662029 28418986197177791123261)
                ·
                  refine ⟨10657119823941671671223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28418986197177791123261 10657119823941671671223)
                  ·
                    rfl

theorem cell20_23349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 3, 3].length) (baseStart_23349 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_23349 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_23349 prefixEnd_23349 := by exact prefixLift 23349
  have htrace : WordTrace (prefixWord ++ tailWord_23349) baseStart_23349 baseEnd_23349 := by
    simpa [prefixWord, tailWord_23349, baseEnd_23349] using wordTrace_append hprefix tailTrace_23349
  have hstable : (prefixWord ++ tailWord_23349).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23349).length < 2 ^ (prefixWord ++ tailWord_23349).sum := by decide
  have hdescent : baseEnd_23349 < baseStart_23349 := by decide
  rcases family_descends (prefixWord ++ tailWord_23349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23408 : List Nat := [2, 1, 1, 1, 4, 1, 4, 3, 3]
def baseStart_23408 : Nat := 118140960795 + 23408 * 2 ^ 59
def prefixEnd_23408 : Nat := 4983230072969 + 3 ^ 40 * 23408 * 2
def baseEnd_23408 : Nat := 10684049031599688704315

theorem tailTrace_23408 : CollatzResearch.WordTrace tailWord_23408 prefixEnd_23408 10684049031599688704315 := by
  unfold tailWord_23408
  simp only [CollatzResearch.WordTrace]
  refine ⟨426879949602144306615439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 569173266136192408820585 426879949602144306615439)
  ·
    refine ⟨640319924403216459923159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 426879949602144306615439 640319924403216459923159)
    ·
      refine ⟨960479886604824689884739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 640319924403216459923159 960479886604824689884739)
      ·
        refine ⟨1440719829907237034827109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 960479886604824689884739 1440719829907237034827109)
        ·
          refine ⟨270134968107606944030083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1440719829907237034827109 270134968107606944030083)
          ·
            refine ⟨405202452161410416045125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 270134968107606944030083 405202452161410416045125)
            ·
              refine ⟨75975459780264453008461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 405202452161410416045125 75975459780264453008461)
              ·
                refine ⟨28490797417599169878173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75975459780264453008461 28490797417599169878173)
                ·
                  refine ⟨10684049031599688704315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28490797417599169878173 10684049031599688704315)
                  ·
                    rfl

theorem cell20_23408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 3, 3].length) (baseStart_23408 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_23408 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_23408 prefixEnd_23408 := by exact prefixLift 23408
  have htrace : WordTrace (prefixWord ++ tailWord_23408) baseStart_23408 baseEnd_23408 := by
    simpa [prefixWord, tailWord_23408, baseEnd_23408] using wordTrace_append hprefix tailTrace_23408
  have hstable : (prefixWord ++ tailWord_23408).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23408).length < 2 ^ (prefixWord ++ tailWord_23408).sum := by decide
  have hdescent : baseEnd_23408 < baseStart_23408 := by decide
  rcases family_descends (prefixWord ++ tailWord_23408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23460 : List Nat := [2, 3, 1, 2, 1, 2, 2, 7]
def baseStart_23460 : Nat := 118140960795 + 23460 * 2 ^ 59
def prefixEnd_23460 : Nat := 4983230072969 + 3 ^ 40 * 23460 * 2
def baseEnd_23460 : Nat := 3569261082839539656923

theorem tailTrace_23460 : CollatzResearch.WordTrace tailWord_23460 prefixEnd_23460 3569261082839539656923 := by
  unfold tailWord_23460
  simp only [CollatzResearch.WordTrace]
  refine ⟨427828247507950747061917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 570437663343934329415889 427828247507950747061917)
  ·
    refine ⟨160435592815481530148219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 427828247507950747061917 160435592815481530148219)
    ·
      refine ⟨240653389223222295222329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160435592815481530148219 240653389223222295222329)
      ·
        refine ⟨180490041917416721416747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240653389223222295222329 180490041917416721416747)
        ·
          refine ⟨270735062876125082125121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180490041917416721416747 270735062876125082125121)
          ·
            refine ⟨203051297157093811593841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 270735062876125082125121 203051297157093811593841)
            ·
              refine ⟨152288472867820358695381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 203051297157093811593841 152288472867820358695381)
              ·
                refine ⟨3569261082839539656923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 152288472867820358695381 3569261082839539656923)
                ·
                  rfl

theorem cell20_23460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 7].length) (baseStart_23460 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_23460 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_23460 prefixEnd_23460 := by exact prefixLift 23460
  have htrace : WordTrace (prefixWord ++ tailWord_23460) baseStart_23460 baseEnd_23460 := by
    simpa [prefixWord, tailWord_23460, baseEnd_23460] using wordTrace_append hprefix tailTrace_23460
  have hstable : (prefixWord ++ tailWord_23460).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23460).length < 2 ^ (prefixWord ++ tailWord_23460).sum := by decide
  have hdescent : baseEnd_23460 < baseStart_23460 := by decide
  rcases family_descends (prefixWord ++ tailWord_23460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23473 : List Nat := [1, 2, 2, 4, 4, 1, 2, 4]
def baseStart_23473 : Nat := 118140960795 + 23473 * 2 ^ 59
def prefixEnd_23473 : Nat := 4983230072969 + 3 ^ 40 * 23473 * 2
def baseEnd_23473 : Nat := 3571238934249450512461

theorem tailTrace_23473 : CollatzResearch.WordTrace tailWord_23473 prefixEnd_23473 3571238934249450512461 := by
  unfold tailWord_23473
  simp only [CollatzResearch.WordTrace]
  refine ⟨856130643968804714347073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 570753762645869809564715 856130643968804714347073)
  ·
    refine ⟨642097982976603535760305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 856130643968804714347073 642097982976603535760305)
    ·
      refine ⟨481573487232452651820229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 642097982976603535760305 481573487232452651820229)
      ·
        refine ⟨90295028856084872216293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 481573487232452651820229 90295028856084872216293)
        ·
          refine ⟨16930317910515913540555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90295028856084872216293 16930317910515913540555)
          ·
            refine ⟨25395476865773870310833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16930317910515913540555 25395476865773870310833)
            ·
              refine ⟨19046607649330402733125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25395476865773870310833 19046607649330402733125)
              ·
                refine ⟨3571238934249450512461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19046607649330402733125 3571238934249450512461)
                ·
                  rfl

theorem cell20_23473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 2, 4].length) (baseStart_23473 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_23473 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_23473 prefixEnd_23473 := by exact prefixLift 23473
  have htrace : WordTrace (prefixWord ++ tailWord_23473) baseStart_23473 baseEnd_23473 := by
    simpa [prefixWord, tailWord_23473, baseEnd_23473] using wordTrace_append hprefix tailTrace_23473
  have hstable : (prefixWord ++ tailWord_23473).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23473).length < 2 ^ (prefixWord ++ tailWord_23473).sum := by decide
  have hdescent : baseEnd_23473 < baseStart_23473 := by decide
  rcases family_descends (prefixWord ++ tailWord_23473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23505 : List Nat := [1, 2, 2, 1, 2, 1, 3, 3, 5]
def baseStart_23505 : Nat := 118140960795 + 23505 * 2 ^ 59
def prefixEnd_23505 : Nat := 4983230072969 + 3 ^ 40 * 23505 * 2
def baseEnd_23505 : Nat := 10728322474698462470585

theorem tailTrace_23505 : CollatzResearch.WordTrace tailWord_23505 prefixEnd_23505 10728322474698462470585 := by
  unfold tailWord_23505
  simp only [CollatzResearch.WordTrace]
  refine ⟨857297779852874179511969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 571531853235249453007979 857297779852874179511969)
  ·
    refine ⟨642973334889655634633977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 857297779852874179511969 642973334889655634633977)
    ·
      refine ⟨482230001167241725975483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 642973334889655634633977 482230001167241725975483)
      ·
        refine ⟨723345001750862588963225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 482230001167241725975483 723345001750862588963225)
        ·
          refine ⟨542508751313146941722419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 723345001750862588963225 542508751313146941722419)
          ·
            refine ⟨813763126969720412583629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 542508751313146941722419 813763126969720412583629)
            ·
              refine ⟨305161172613645154718861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 813763126969720412583629 305161172613645154718861)
              ·
                refine ⟨114435439730116933019573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 305161172613645154718861 114435439730116933019573)
                ·
                  refine ⟨10728322474698462470585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 114435439730116933019573 10728322474698462470585)
                  ·
                    rfl

theorem cell20_23505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 3, 5].length) (baseStart_23505 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_23505 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_23505 prefixEnd_23505 := by exact prefixLift 23505
  have htrace : WordTrace (prefixWord ++ tailWord_23505) baseStart_23505 baseEnd_23505 := by
    simpa [prefixWord, tailWord_23505, baseEnd_23505] using wordTrace_append hprefix tailTrace_23505
  have hstable : (prefixWord ++ tailWord_23505).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23505).length < 2 ^ (prefixWord ++ tailWord_23505).sum := by decide
  have hdescent : baseEnd_23505 < baseStart_23505 := by decide
  rcases family_descends (prefixWord ++ tailWord_23505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23508 : List Nat := [2, 4, 1, 2, 1, 2, 3, 1, 4]
def baseStart_23508 : Nat := 118140960795 + 23508 * 2 ^ 59
def prefixEnd_23508 : Nat := 4983230072969 + 3 ^ 40 * 23508 * 2
def baseEnd_23508 : Nat := 10729691756443785370573

theorem tailTrace_23508 : CollatzResearch.WordTrace tailWord_23508 prefixEnd_23508 10729691756443785370573 := by
  unfold tailWord_23508
  simp only [CollatzResearch.WordTrace]
  refine ⟨428703599421002845935589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 571604799228003794580785 428703599421002845935589)
  ·
    refine ⟨80381924891438033612923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 428703599421002845935589 80381924891438033612923)
    ·
      refine ⟨120572887337157050419385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80381924891438033612923 120572887337157050419385)
      ·
        refine ⟨90429665502867787814539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120572887337157050419385 90429665502867787814539)
        ·
          refine ⟨135644498254301681721809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90429665502867787814539 135644498254301681721809)
          ·
            refine ⟨101733373690726261291357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135644498254301681721809 101733373690726261291357)
            ·
              refine ⟨38150015134022347984259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101733373690726261291357 38150015134022347984259)
              ·
                refine ⟨57225022701033521976389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38150015134022347984259 57225022701033521976389)
                ·
                  refine ⟨10729691756443785370573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57225022701033521976389 10729691756443785370573)
                  ·
                    rfl

theorem cell20_23508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_23508 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_23508 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_23508 prefixEnd_23508 := by exact prefixLift 23508
  have htrace : WordTrace (prefixWord ++ tailWord_23508) baseStart_23508 baseEnd_23508 := by
    simpa [prefixWord, tailWord_23508, baseEnd_23508] using wordTrace_append hprefix tailTrace_23508
  have hstable : (prefixWord ++ tailWord_23508).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23508).length < 2 ^ (prefixWord ++ tailWord_23508).sum := by decide
  have hdescent : baseEnd_23508 < baseStart_23508 := by decide
  rcases family_descends (prefixWord ++ tailWord_23508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23560 : List Nat := [2, 1, 3, 2, 1, 3, 1, 4, 3]
def baseStart_23560 : Nat := 118140960795 + 23560 * 2 ^ 59
def prefixEnd_23560 : Nat := 4983230072969 + 3 ^ 40 * 23560 * 2
def baseEnd_23560 : Nat := 10753425973362715637027

theorem tailTrace_23560 : CollatzResearch.WordTrace tailWord_23560 prefixEnd_23560 10753425973362715637027 := by
  unfold tailWord_23560
  simp only [CollatzResearch.WordTrace]
  refine ⟨429651897326809286382067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 572869196435745715176089 429651897326809286382067)
  ·
    refine ⟨644477845990213929573101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 429651897326809286382067 644477845990213929573101)
    ·
      refine ⟨241679192246330223589913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 644477845990213929573101 241679192246330223589913)
      ·
        refine ⟨181259394184747667692435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 241679192246330223589913 181259394184747667692435)
        ·
          refine ⟨271889091277121501538653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181259394184747667692435 271889091277121501538653)
          ·
            refine ⟨101958409228920563076995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 271889091277121501538653 101958409228920563076995)
            ·
              refine ⟨152937613843380844615493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101958409228920563076995 152937613843380844615493)
              ·
                refine ⟨28675802595633908365405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 152937613843380844615493 28675802595633908365405)
                ·
                  refine ⟨10753425973362715637027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28675802595633908365405 10753425973362715637027)
                  ·
                    rfl

theorem cell20_23560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 4, 3].length) (baseStart_23560 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_23560 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_23560 prefixEnd_23560 := by exact prefixLift 23560
  have htrace : WordTrace (prefixWord ++ tailWord_23560) baseStart_23560 baseEnd_23560 := by
    simpa [prefixWord, tailWord_23560, baseEnd_23560] using wordTrace_append hprefix tailTrace_23560
  have hstable : (prefixWord ++ tailWord_23560).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23560).length < 2 ^ (prefixWord ++ tailWord_23560).sum := by decide
  have hdescent : baseEnd_23560 < baseStart_23560 := by decide
  rcases family_descends (prefixWord ++ tailWord_23560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23563 : List Nat := [1, 1, 1, 1, 6, 2, 4, 2, 2]
def baseStart_23563 : Nat := 118140960795 + 23563 * 2 ^ 59
def prefixEnd_23563 : Nat := 4983230072969 + 3 ^ 40 * 23563 * 2
def baseEnd_23563 : Nat := 10754795255108038537015

theorem tailTrace_23563 : CollatzResearch.WordTrace tailWord_23563 prefixEnd_23563 10754795255108038537015 := by
  unfold tailWord_23563
  simp only [CollatzResearch.WordTrace]
  refine ⟨859413213642750085123343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 572942142428500056748895 859413213642750085123343)
  ·
    refine ⟨1289119820464125127685015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 859413213642750085123343 1289119820464125127685015)
    ·
      refine ⟨1933679730696187691527523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1289119820464125127685015 1933679730696187691527523)
      ·
        refine ⟨2900519596044281537291285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1933679730696187691527523 2900519596044281537291285)
        ·
          refine ⟨135961856064575697060529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 2900519596044281537291285 135961856064575697060529)
          ·
            refine ⟨101971392048431772795397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135961856064575697060529 101971392048431772795397)
            ·
              refine ⟨19119636009080957399137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 101971392048431772795397 19119636009080957399137)
              ·
                refine ⟨14339727006810718049353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19119636009080957399137 14339727006810718049353)
                ·
                  refine ⟨10754795255108038537015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14339727006810718049353 10754795255108038537015)
                  ·
                    rfl

theorem cell20_23563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 4, 2, 2].length) (baseStart_23563 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_23563 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_23563 prefixEnd_23563 := by exact prefixLift 23563
  have htrace : WordTrace (prefixWord ++ tailWord_23563) baseStart_23563 baseEnd_23563 := by
    simpa [prefixWord, tailWord_23563, baseEnd_23563] using wordTrace_append hprefix tailTrace_23563
  have hstable : (prefixWord ++ tailWord_23563).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23563).length < 2 ^ (prefixWord ++ tailWord_23563).sum := by decide
  have hdescent : baseEnd_23563 < baseStart_23563 := by decide
  rcases family_descends (prefixWord ++ tailWord_23563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23598 : List Nat := [4, 1, 3, 1, 1, 1, 2, 2, 5]
def baseStart_23598 : Nat := 118140960795 + 23598 * 2 ^ 59
def prefixEnd_23598 : Nat := 4983230072969 + 3 ^ 40 * 23598 * 2
def baseEnd_23598 : Nat := 10770770208803472370205

theorem tailTrace_23598 : CollatzResearch.WordTrace tailWord_23598 prefixEnd_23598 10770770208803472370205 := by
  unfold tailWord_23598
  simp only [CollatzResearch.WordTrace]
  refine ⟨107586221064493882830931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 573793179010634041764965 107586221064493882830931)
  ·
    refine ⟨161379331596740824246397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107586221064493882830931 161379331596740824246397)
    ·
      refine ⟨60517249348777809092399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161379331596740824246397 60517249348777809092399)
      ·
        refine ⟨90775874023166713638599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60517249348777809092399 90775874023166713638599)
        ·
          refine ⟨136163811034750070457899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90775874023166713638599 136163811034750070457899)
          ·
            refine ⟨204245716552125105686849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136163811034750070457899 204245716552125105686849)
            ·
              refine ⟨153184287414093829265137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 204245716552125105686849 153184287414093829265137)
              ·
                refine ⟨114888215560570371948853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 153184287414093829265137 114888215560570371948853)
                ·
                  refine ⟨10770770208803472370205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 114888215560570371948853 10770770208803472370205)
                  ·
                    rfl

theorem cell20_23598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_23598 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_23598 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_23598 prefixEnd_23598 := by exact prefixLift 23598
  have htrace : WordTrace (prefixWord ++ tailWord_23598) baseStart_23598 baseEnd_23598 := by
    simpa [prefixWord, tailWord_23598, baseEnd_23598] using wordTrace_append hprefix tailTrace_23598
  have hstable : (prefixWord ++ tailWord_23598).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23598).length < 2 ^ (prefixWord ++ tailWord_23598).sum := by decide
  have hdescent : baseEnd_23598 < baseStart_23598 := by decide
  rcases family_descends (prefixWord ++ tailWord_23598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23612 : List Nat := [2, 2, 2, 2, 2, 3, 7]
def baseStart_23612 : Nat := 118140960795 + 23612 * 2 ^ 59
def prefixEnd_23612 : Nat := 4983230072969 + 3 ^ 40 * 23612 * 2
def baseEnd_23612 : Nat := 1197462243364627322609

theorem tailTrace_23612 : CollatzResearch.WordTrace tailWord_23612 prefixEnd_23612 1197462243364627322609 := by
  unfold tailWord_23612
  simp only [CollatzResearch.WordTrace]
  refine ⟨430600195232615726828545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 574133593643487635771393 430600195232615726828545)
  ·
    refine ⟨322950146424461795121409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 430600195232615726828545 322950146424461795121409)
    ·
      refine ⟨242212609818346346341057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 322950146424461795121409 242212609818346346341057)
      ·
        refine ⟨181659457363759759755793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 242212609818346346341057 181659457363759759755793)
        ·
          refine ⟨136244593022819819816845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181659457363759759755793 136244593022819819816845)
          ·
            refine ⟨51091722383557432431317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136244593022819819816845 51091722383557432431317)
            ·
              refine ⟨1197462243364627322609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 51091722383557432431317 1197462243364627322609)
              ·
                rfl

theorem cell20_23612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 7].length) (baseStart_23612 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_23612 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_23612 prefixEnd_23612 := by exact prefixLift 23612
  have htrace : WordTrace (prefixWord ++ tailWord_23612) baseStart_23612 baseEnd_23612 := by
    simpa [prefixWord, tailWord_23612, baseEnd_23612] using wordTrace_append hprefix tailTrace_23612
  have hstable : (prefixWord ++ tailWord_23612).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23612).length < 2 ^ (prefixWord ++ tailWord_23612).sum := by decide
  have hdescent : baseEnd_23612 < baseStart_23612 := by decide
  rcases family_descends (prefixWord ++ tailWord_23612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23619 : List Nat := [1, 1, 1, 3, 1, 2, 5, 1, 5]
def baseStart_23619 : Nat := 118140960795 + 23619 * 2 ^ 59
def prefixEnd_23619 : Nat := 4983230072969 + 3 ^ 40 * 23619 * 2
def baseEnd_23619 : Nat := 10780355181020732670119

theorem tailTrace_23619 : CollatzResearch.WordTrace tailWord_23619 prefixEnd_23619 10780355181020732670119 := by
  unfold tailWord_23619
  simp only [CollatzResearch.WordTrace]
  refine ⟨861455701439871649161911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 574303800959914432774607 861455701439871649161911)
  ·
    refine ⟨1292183552159807473742867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 861455701439871649161911 1292183552159807473742867)
    ·
      refine ⟨1938275328239711210614301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1292183552159807473742867 1938275328239711210614301)
      ·
        refine ⟨726853248089891703980363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1938275328239711210614301 726853248089891703980363)
        ·
          refine ⟨1090279872134837555970545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 726853248089891703980363 1090279872134837555970545)
          ·
            refine ⟨817709904101128166977909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1090279872134837555970545 817709904101128166977909)
            ·
              refine ⟨76660303509480765654179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 817709904101128166977909 76660303509480765654179)
              ·
                refine ⟨114990455264221148481269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76660303509480765654179 114990455264221148481269)
                ·
                  refine ⟨10780355181020732670119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 114990455264221148481269 10780355181020732670119)
                  ·
                    rfl

theorem cell20_23619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 1, 5].length) (baseStart_23619 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_23619 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_23619 prefixEnd_23619 := by exact prefixLift 23619
  have htrace : WordTrace (prefixWord ++ tailWord_23619) baseStart_23619 baseEnd_23619 := by
    simpa [prefixWord, tailWord_23619, baseEnd_23619] using wordTrace_append hprefix tailTrace_23619
  have hstable : (prefixWord ++ tailWord_23619).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23619).length < 2 ^ (prefixWord ++ tailWord_23619).sum := by decide
  have hdescent : baseEnd_23619 < baseStart_23619 := by decide
  rcases family_descends (prefixWord ++ tailWord_23619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23636 : List Nat := [2, 4, 1, 1, 1, 1, 2, 5, 3]
def baseStart_23636 : Nat := 118140960795 + 23636 * 2 ^ 59
def prefixEnd_23636 : Nat := 4983230072969 + 3 ^ 40 * 23636 * 2
def baseEnd_23636 : Nat := 10788114444244229103383

theorem tailTrace_23636 : CollatzResearch.WordTrace tailWord_23636 prefixEnd_23636 10788114444244229103383 := by
  unfold tailWord_23636
  simp only [CollatzResearch.WordTrace]
  refine ⟨431037871189141776265381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 574717161585522368353841 431037871189141776265381)
  ·
    refine ⟨80819600847964083049759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 431037871189141776265381 80819600847964083049759)
    ·
      refine ⟨121229401271946124574639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80819600847964083049759 121229401271946124574639)
      ·
        refine ⟨181844101907919186861959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121229401271946124574639 181844101907919186861959)
        ·
          refine ⟨272766152861878780292939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181844101907919186861959 272766152861878780292939)
          ·
            refine ⟨409149229292818170439409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 272766152861878780292939 409149229292818170439409)
            ·
              refine ⟨306861921969613627829557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 409149229292818170439409 306861921969613627829557)
              ·
                refine ⟨28768305184651277609021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 306861921969613627829557 28768305184651277609021)
                ·
                  refine ⟨10788114444244229103383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28768305184651277609021 10788114444244229103383)
                  ·
                    rfl

theorem cell20_23636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_23636 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_23636 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_23636 prefixEnd_23636 := by exact prefixLift 23636
  have htrace : WordTrace (prefixWord ++ tailWord_23636) baseStart_23636 baseEnd_23636 := by
    simpa [prefixWord, tailWord_23636, baseEnd_23636] using wordTrace_append hprefix tailTrace_23636
  have hstable : (prefixWord ++ tailWord_23636).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23636).length < 2 ^ (prefixWord ++ tailWord_23636).sum := by decide
  have hdescent : baseEnd_23636 < baseStart_23636 := by decide
  rcases family_descends (prefixWord ++ tailWord_23636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23657 : List Nat := [1, 2, 1, 1, 1, 6, 1, 2, 5]
def baseStart_23657 : Nat := 118140960795 + 23657 * 2 ^ 59
def prefixEnd_23657 : Nat := 4983230072969 + 3 ^ 40 * 23657 * 2
def baseEnd_23657 : Nat := 10797699416461489403297

theorem tailTrace_23657 : CollatzResearch.WordTrace tailWord_23657 prefixEnd_23657 10797699416461489403297 := by
  unfold tailWord_23657
  simp only [CollatzResearch.WordTrace]
  refine ⟨862841675302204139045225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 575227783534802759363483 862841675302204139045225)
  ·
    refine ⟨647131256476653104283919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 862841675302204139045225 647131256476653104283919)
    ·
      refine ⟨970696884714979656425879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 647131256476653104283919 970696884714979656425879)
      ·
        refine ⟨1456045327072469484638819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 970696884714979656425879 1456045327072469484638819)
        ·
          refine ⟨2184067990608704226958229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1456045327072469484638819 2184067990608704226958229)
          ·
            refine ⟨102378187059783010638667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 2184067990608704226958229 102378187059783010638667)
            ·
              refine ⟨153567280589674515958001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102378187059783010638667 153567280589674515958001)
              ·
                refine ⟨115175460442255886968501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 153567280589674515958001 115175460442255886968501)
                ·
                  refine ⟨10797699416461489403297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 115175460442255886968501 10797699416461489403297)
                  ·
                    rfl

theorem cell20_23657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 2, 5].length) (baseStart_23657 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_23657 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_23657 prefixEnd_23657 := by exact prefixLift 23657
  have htrace : WordTrace (prefixWord ++ tailWord_23657) baseStart_23657 baseEnd_23657 := by
    simpa [prefixWord, tailWord_23657, baseEnd_23657] using wordTrace_append hprefix tailTrace_23657
  have hstable : (prefixWord ++ tailWord_23657).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23657).length < 2 ^ (prefixWord ++ tailWord_23657).sum := by decide
  have hdescent : baseEnd_23657 < baseStart_23657 := by decide
  rcases family_descends (prefixWord ++ tailWord_23657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23677 : List Nat := [1, 4, 1, 1, 3, 1, 5, 2, 2]
def baseStart_23677 : Nat := 118140960795 + 23677 * 2 ^ 59
def prefixEnd_23677 : Nat := 4983230072969 + 3 ^ 40 * 23677 * 2
def baseEnd_23677 : Nat := 10806827961430308736549

theorem tailTrace_23677 : CollatzResearch.WordTrace tailWord_23677 prefixEnd_23677 10806827961430308736549 := by
  unfold tailWord_23677
  simp only [CollatzResearch.WordTrace]
  refine ⟨863571135229747554773285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 575714090153165036515523 863571135229747554773285)
  ·
    refine ⟨161919587855577666519991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 863571135229747554773285 161919587855577666519991)
    ·
      refine ⟨242879381783366499779987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161919587855577666519991 242879381783366499779987)
      ·
        refine ⟨364319072675049749669981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242879381783366499779987 364319072675049749669981)
        ·
          refine ⟨136619652253143656126243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 364319072675049749669981 136619652253143656126243)
          ·
            refine ⟨204929478379715484189365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136619652253143656126243 204929478379715484189365)
            ·
              refine ⟨19212138598098326642753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 204929478379715484189365 19212138598098326642753)
              ·
                refine ⟨14409103948573744982065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19212138598098326642753 14409103948573744982065)
                ·
                  refine ⟨10806827961430308736549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14409103948573744982065 10806827961430308736549)
                  ·
                    rfl

theorem cell20_23677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 5, 2, 2].length) (baseStart_23677 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_23677 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_23677 prefixEnd_23677 := by exact prefixLift 23677
  have htrace : WordTrace (prefixWord ++ tailWord_23677) baseStart_23677 baseEnd_23677 := by
    simpa [prefixWord, tailWord_23677, baseEnd_23677] using wordTrace_append hprefix tailTrace_23677
  have hstable : (prefixWord ++ tailWord_23677).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23677).length < 2 ^ (prefixWord ++ tailWord_23677).sum := by decide
  have hdescent : baseEnd_23677 < baseStart_23677 := by decide
  rcases family_descends (prefixWord ++ tailWord_23677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23726 : List Nat := [4, 1, 4, 11]
def baseStart_23726 : Nat := 118140960795 + 23726 * 2 ^ 59
def prefixEnd_23726 : Nat := 4983230072969 + 3 ^ 40 * 23726 * 2
def baseEnd_23726 : Nat := 44564579821415292605

theorem tailTrace_23726 : CollatzResearch.WordTrace tailWord_23726 prefixEnd_23726 44564579821415292605 := by
  unfold tailWord_23726
  simp only [CollatzResearch.WordTrace]
  refine ⟨108169789006528615413379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 576905541368152615538021 108169789006528615413379)
  ·
    refine ⟨162254683509792923120069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108169789006528615413379 162254683509792923120069)
    ·
      refine ⟨30422753158086173085013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 162254683509792923120069 30422753158086173085013)
      ·
        refine ⟨44564579821415292605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 11 30422753158086173085013 44564579821415292605)
        ·
          rfl

theorem cell20_23726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 11].length) (baseStart_23726 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_23726 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_23726 prefixEnd_23726 := by exact prefixLift 23726
  have htrace : WordTrace (prefixWord ++ tailWord_23726) baseStart_23726 baseEnd_23726 := by
    simpa [prefixWord, tailWord_23726, baseEnd_23726] using wordTrace_append hprefix tailTrace_23726
  have hstable : (prefixWord ++ tailWord_23726).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23726).length < 2 ^ (prefixWord ++ tailWord_23726).sum := by decide
  have hdescent : baseEnd_23726 < baseStart_23726 := by decide
  rcases family_descends (prefixWord ++ tailWord_23726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23729 : List Nat := [1, 2, 2, 5, 1, 2, 2, 2, 3]
def baseStart_23729 : Nat := 118140960795 + 23729 * 2 ^ 59
def prefixEnd_23729 : Nat := 4983230072969 + 3 ^ 40 * 23729 * 2
def baseEnd_23729 : Nat := 10830562178349239003003

theorem tailTrace_23729 : CollatzResearch.WordTrace tailWord_23729 prefixEnd_23729 10830562178349239003003 := by
  unfold tailWord_23729
  simp only [CollatzResearch.WordTrace]
  refine ⟨865467731041360435666241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 576978487360906957110827 865467731041360435666241)
  ·
    refine ⟨649100798281020326749681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 865467731041360435666241 649100798281020326749681)
    ·
      refine ⟨486825598710765245062261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 649100798281020326749681 486825598710765245062261)
      ·
        refine ⟨45639899879134241724587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 486825598710765245062261 45639899879134241724587)
        ·
          refine ⟨68459849818701362586881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45639899879134241724587 68459849818701362586881)
          ·
            refine ⟨51344887364026021940161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68459849818701362586881 51344887364026021940161)
            ·
              refine ⟨38508665523019516455121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51344887364026021940161 38508665523019516455121)
              ·
                refine ⟨28881499142264637341341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38508665523019516455121 28881499142264637341341)
                ·
                  refine ⟨10830562178349239003003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28881499142264637341341 10830562178349239003003)
                  ·
                    rfl

theorem cell20_23729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 2, 3].length) (baseStart_23729 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_23729 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_23729 prefixEnd_23729 := by exact prefixLift 23729
  have htrace : WordTrace (prefixWord ++ tailWord_23729) baseStart_23729 baseEnd_23729 := by
    simpa [prefixWord, tailWord_23729, baseEnd_23729] using wordTrace_append hprefix tailTrace_23729
  have hstable : (prefixWord ++ tailWord_23729).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23729).length < 2 ^ (prefixWord ++ tailWord_23729).sum := by decide
  have hdescent : baseEnd_23729 < baseStart_23729 := by decide
  rcases family_descends (prefixWord ++ tailWord_23729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23747 : List Nat := [1, 1, 1, 3, 1, 1, 1, 11]
def baseStart_23747 : Nat := 118140960795 + 23747 * 2 ^ 59
def prefixEnd_23747 : Nat := 4983230072969 + 3 ^ 40 * 23747 * 2
def baseEnd_23747 : Nat := 3612925956273725467643

theorem tailTrace_23747 : CollatzResearch.WordTrace tailWord_23747 prefixEnd_23747 3612925956273725467643 := by
  unfold tailWord_23747
  simp only [CollatzResearch.WordTrace]
  refine ⟨866124244976149509821495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 577416163317433006547663 866124244976149509821495)
  ·
    refine ⟨1299186367464224264732243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 866124244976149509821495 1299186367464224264732243)
    ·
      refine ⟨1948779551196336397098365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1299186367464224264732243 1948779551196336397098365)
      ·
        refine ⟨730792331698626148911887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1948779551196336397098365 730792331698626148911887)
        ·
          refine ⟨1096188497547939223367831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 730792331698626148911887 1096188497547939223367831)
          ·
            refine ⟨1644282746321908835051747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1096188497547939223367831 1644282746321908835051747)
            ·
              refine ⟨2466424119482863252577621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1644282746321908835051747 2466424119482863252577621)
              ·
                refine ⟨3612925956273725467643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 2466424119482863252577621 3612925956273725467643)
                ·
                  rfl

theorem cell20_23747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 11].length) (baseStart_23747 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_23747 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_23747 prefixEnd_23747 := by exact prefixLift 23747
  have htrace : WordTrace (prefixWord ++ tailWord_23747) baseStart_23747 baseEnd_23747 := by
    simpa [prefixWord, tailWord_23747, baseEnd_23747] using wordTrace_append hprefix tailTrace_23747
  have hstable : (prefixWord ++ tailWord_23747).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23747).length < 2 ^ (prefixWord ++ tailWord_23747).sum := by decide
  have hdescent : baseEnd_23747 < baseStart_23747 := by decide
  rcases family_descends (prefixWord ++ tailWord_23747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23788 : List Nat := [2, 2, 1, 1, 2, 4, 3, 2, 3]
def baseStart_23788 : Nat := 118140960795 + 23788 * 2 ^ 59
def prefixEnd_23788 : Nat := 4983230072969 + 3 ^ 40 * 23788 * 2
def baseEnd_23788 : Nat := 10857491386007256036095

theorem tailTrace_23788 : CollatzResearch.WordTrace tailWord_23788 prefixEnd_23788 10857491386007256036095 := by
  unfold tailWord_23788
  simp only [CollatzResearch.WordTrace]
  refine ⟨433809818913806756032009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 578413091885075674709345 433809818913806756032009)
  ·
    refine ⟨325357364185355067024007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 433809818913806756032009 325357364185355067024007)
    ·
      refine ⟨488036046278032600536011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325357364185355067024007 488036046278032600536011)
      ·
        refine ⟨732054069417048900804017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 488036046278032600536011 732054069417048900804017)
        ·
          refine ⟨549040552062786675603013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 732054069417048900804017 549040552062786675603013)
          ·
            refine ⟨102945103511772501675565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 549040552062786675603013 102945103511772501675565)
            ·
              refine ⟨38604413816914688128337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102945103511772501675565 38604413816914688128337)
              ·
                refine ⟨28953310362686016096253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38604413816914688128337 28953310362686016096253)
                ·
                  refine ⟨10857491386007256036095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28953310362686016096253 10857491386007256036095)
                  ·
                    rfl

theorem cell20_23788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 3].length) (baseStart_23788 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_23788 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_23788 prefixEnd_23788 := by exact prefixLift 23788
  have htrace : WordTrace (prefixWord ++ tailWord_23788) baseStart_23788 baseEnd_23788 := by
    simpa [prefixWord, tailWord_23788, baseEnd_23788] using wordTrace_append hprefix tailTrace_23788
  have hstable : (prefixWord ++ tailWord_23788).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23788).length < 2 ^ (prefixWord ++ tailWord_23788).sum := by decide
  have hdescent : baseEnd_23788 < baseStart_23788 := by decide
  rcases family_descends (prefixWord ++ tailWord_23788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
